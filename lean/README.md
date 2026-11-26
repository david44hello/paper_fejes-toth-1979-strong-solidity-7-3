# Strong solidity of the `{7, 3}` hyperbolic circle packing — Lean 4 proof

The paper’s link is on the [front page of this repository](https://github.com/david44hello/paper_fejes-toth-1979-strong-solidity-7-3).

This folder is a Lean 4 proof of the paper’s results: Theorem 1.1 (`FejesTothP7.Paper.thm_1_1_strong_solidity`, strong solidity of the face-incircle packing of `{7, 3}`), Corollary 1.2 (`FejesTothP7.Paper.cor_1_2_grade_and_order`, grade of saturatedness `g₇ = 3` and order of solidity `k₇ = 1`), and every supporting lemma, proposition, remark, and named proof step (43 statements in `FejesTothP7/Paper/Statements.lean`). Every statement is proved from Lean 4’s three standard axioms alone (`propext`, `Classical.choice`, `Quot.sound`) — no custom axioms, no cited external results, and no computer checks.

For what is proved, proof routes, and how the release was checked, see [WHAT_TO_READ.md](WHAT_TO_READ.md).

## How to verify

Install Git, Lean (`https://lean-lang.org/install/`), Python 3, and ripgrep, then run:

```bash
./scripts/check.sh
```

Its last lines read:

```
AUDIT: 43 claims. PROVED: 43. Table: AUDIT.md
PASS: project builds; source policy passes; every paper claim proved from standard axioms only.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
