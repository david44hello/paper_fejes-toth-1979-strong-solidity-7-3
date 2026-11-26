# Comparing the Lean statements

The challenge states Theorem 1.1, Corollary 1.2, and all 41 supporting lemmas, propositions, remarks, and named proof steps of the paper (43 theorems in `FejesTothP7.Challenge.Statements`, importing only `FejesTothP7.Defs.*` and `Mathlib.Topology.Order.Basic`). Each challenge theorem has an open proof. The solution in the Lean directory supplies the proofs. The comparison permits Lean’s three standard axioms alone (`propext`, `Quot.sound`, `Classical.choice`), with no custom or cited axioms.

To run the comparison on Linux with Git, elan, and bubblewrap, start at the root of the checked-out repository.

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp -R comparator/FejesTothP7/Challenge "$comparison_dir/FejesTothP7/"
cp comparator/comparator.json "$comparison_dir/"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares the declarations and checks the solution. A successful run ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
