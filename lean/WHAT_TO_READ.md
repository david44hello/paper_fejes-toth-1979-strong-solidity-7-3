# Guide to the Lean 4 proof of strong solidity for `{7, 3}`

## What is proved

All 43 claims in `FejesTothP7/Paper/Statements.lean` are formally proved in Lean 4 (`leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, rev `56a005855ea17e0b0958f73ec801ae140b0a1679`):

| Paper result | Lean declaration |
|---|---|
| Theorem 1.1: face-incircles of `{7, 3}` form a strongly solid packing | `FejesTothP7.Paper.thm_1_1_strong_solidity` |
| Corollary 1.2: grade of saturatedness `g₇ = 3` and order of solidity `k₇ = 1` | `FejesTothP7.Paper.cor_1_2_grade_and_order` |
| Section 1: strong solidity is equivalent to solidity of order `1` | `FejesTothP7.Paper.text_1_strong_solidity_iff_order_one` |
| Section 1 & Figure 2: metric gap `Δ_p < 0`, `|h_p - ρ_p^*| < r_p` (`p ≥ 8`), `Δ₇ = 0`, and `7 ≤ p ≤ 14` vs `p ≥ 15` regime split | `text_1_metric_gap_p_ge_8`, `fig_2_delta7_zero`, `fig_2_caption_regime_split` |
| Section 2: hyperbolic constants, `β`/`ρ*` properties, 5-decimal bounds, open-disc bridges, `{7, 3}`/`{3, 7}` certification, Lemmas 2.1–2.5 | `eq_1_consts`, `eq_2_order`, `text_2_beta_properties`, `text_2_numerical_bounds`, `isPacking_iff_pairwise_disjoint_balls`, `overlaps_iff_balls_inter_nonempty`, `sites37_tiling_certification`, `lem_2_1_trivial_rearrangement` .. `lem_2_5_reuleaux` |
| Section 3: exact `p = 7` identity `h = r + ρ*`, minimal cubic eq. (6), tip distances eq. (5), Lemmas 3.2–3.3 | `prop_3_1_exact_identity`, `eq_6_lambda7_cubic`, `eq_5_tip_distances`, `lem_3_2_tip_disc`, `lem_3_3_half_lens` |
| Section 4: Lemmas 4.1, 4.3, 4.4, 4.5 (including Steps 1–5) and Remark 4.2 | `lem_4_1_bridge`, `rem_4_2_tau3_edge_count`, `lem_4_3_join_le_two`, `lem_4_4_join_tau3`, `lem_4_5_step1_edge_counts` .. `lem_4_5_step5_contradiction_at_c3`, `lem_4_5_nine_site` |
| Section 5: Lemma 5.1 (combinatorial & geometric zone substitution, convex polygon `P_m`, `σ²` block decomposition, no adjacent `S-D-S` arcs) and named induction steps | `lem_5_1_zone_substitution`, `thm_1_1_step_zone1`, `thm_1_1_step_zone2`, `thm_1_1_step_zone_m`, `cor_1_2_step_order_chain` |

See `CLAIM_MAP.tsv` and `AUDIT.md` for the complete 43-row table.

## Trust surface and assumptions

Every declaration depends solely on Lean 4’s three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — zero custom axioms, zero cited external axioms, zero `sorry`, and zero computer checks.

To verify the formalization, a referee only needs to inspect two folders:

1. `FejesTothP7/Defs/` — hyperboloid model `H2` with metric space structure and isometries (`H2.lean`), metric constants (`Constants.lean`), circle packings / rearrangements / strong solidity / order of solidity / grade of saturatedness (`Packing.lean`), and the `(2, 3, 7)` reflection group `Delta237`, site orbit `sites37`, `SiteFrame`, zones `Zone`, and substitution words `zoneWord` (`Tiling.lean`).
2. `FejesTothP7/Paper/Statements.lean` — one top-level theorem per claim of the paper.

Everything under `FejesTothP7/Proofs/` is machine-checked by Lean’s kernel.

### Verbatim `#print axioms` output for the main results

```
'FejesTothP7.Paper.thm_1_1_strong_solidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'FejesTothP7.Paper.cor_1_2_grade_and_order' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof routes vs the printed paper

See `AUDIT_NOTES.md` for the detailed list of places where the Lean proof establishes the exact same theorem via an equivalent elementary route (most notably: constructive layer-by-layer `{3, 7}` generation with global convexity `ZoneConvexity` and edge-rigidity instead of hyperbolic `(k + 2)`-gon angle-sum; exact concave quadratic in `tanh(ρ/2)^2` for Lemma 3.2; barycentric conical combination + Edge Lemma for Lemma 2.5; universal `λ_p` algebraic identity for `p ≥ 8` metric gap; and uniform far-away triangle cofinite rigidity for all `m ≥ 2` in Corollary 1.2).

## How the release is checked

1. Fresh build from empty (`lake build`), conservative source policy scan (`scripts/check.sh`), and automated `#print axioms` table generation (`scripts/audit.py` -> `AUDIT.md`).
2. Independent kernel replay (`scripts/kernel_replay.sh`): Lean’s C++ kernel (`leanchecker`) on every `.olean` module, plus full transitive export checked from an empty environment by `leanchecker --from-export`, `leanchecker-paranoid --from-export`, `lean4lean --import`, `nanoda`, `con-leche --verified`, and `con-ron --verified`.
3. Sandboxed statement-matching comparison (`lake comparator`, standard and `--paranoid`) against the stripped `Challenge` file whose proofs are left open.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
