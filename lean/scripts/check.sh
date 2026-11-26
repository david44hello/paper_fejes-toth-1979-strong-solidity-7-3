#!/usr/bin/env bash
# check.sh — build, source policy scan, and axiom audit for FejesTothP7Lean.
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

scan_sources() {
    local source_dir=$1 status=0 failed=0
    [[ -d "$source_dir" ]] || { echo "ERROR: missing source directory: $source_dir" >&2; return 2; }
    # Conservative scan: forbidden proof holes, custom axioms, and unsafe/kernel-bypass constructs.
    (cd "$source_dir" && rg --hidden --no-ignore -n -w --glob '*.lean' \
        --glob '!.lake/**' --glob '!.git/**' --glob '!versions/**' \
        'sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|debug[.]skipKernelTC|csimp' .) || status=$?
    if (( status == 0 )); then
        echo 'ERROR: proof hole, custom axiom, or forbidden construct in local Lean sources.' >&2
        failed=1
    elif (( status != 1 )); then return "$status"; fi
    return "$failed"
}

run_tests() (
    local fixture
    fixture=$(mktemp -d "$project_dir/scripts/.check-test.XXXXXX")
    trap 'python3 -c "import pathlib, shutil, sys; shutil.rmtree(pathlib.Path(sys.argv[1]))" "$fixture"' EXIT
    mkdir -p "$fixture/FejesTothP7" "$fixture/.lake/packages/dependency" "$fixture/versions"
    printf 'theorem good : True := True.intro\n' > "$fixture/FejesTothP7/Basic.lean"
    printf 'theorem dependency_result : True := by sorry\n' > "$fixture/.lake/packages/dependency/Basic.lean"
    printf 'axiom old_assumption : True\ntheorem old_gap : True := by sorry\n' > "$fixture/versions/Old.lean"
    scan_sources "$fixture" || return 1
    local bad_source
    for bad_source in 'theorem hole : True := by sorry' 'theorem hole : True := by admit' \
        'axiom invented : True' 'axiom\ninvented : True' 'def hidden := sorryAx' \
        'example : True := by native_decide' '@[implemented_by replacement] def original := 1' \
        '@[extern "foreign"] opaque external : Nat' 'unsafe def unchecked := 1' \
        'set_option debug.skipKernelTC true' '@[csimp] theorem compiled_replacement : True := True.intro'; do
        printf '%b\n' "$bad_source" > "$fixture/FejesTothP7/Basic.lean"
        if scan_sources "$fixture" >/dev/null 2>&1; then
            echo "TEST FAILED: accepted $bad_source" >&2; return 1
        fi
    done
    echo 'PASS: scanner rejects all proof holes, custom axioms, and forbidden constructs.'
)

main() {
    case "${1:-}" in
        --test) [[ $# == 1 ]] || return 2; run_tests; return ;;
        '') [[ $# == 0 ]] || return 2 ;;
        *) echo "Usage: $0 [--test]" >&2; return 2 ;;
    esac
    cd "$project_dir"
    export PATH="$HOME/.elan/bin:$PATH"
    export LEAN_NUM_THREADS=1
    nice -n 19 lake --no-build build mathlib/Mathlib
    nice -n 19 lake build
    local scan_status=0
    scan_sources . || scan_status=$?
    nice -n 19 python3 scripts/audit.py
    (( scan_status == 0 )) || return "$scan_status"
    echo 'PASS: project builds; source policy passes; every paper claim proved from standard axioms only.'
}

main "$@"
