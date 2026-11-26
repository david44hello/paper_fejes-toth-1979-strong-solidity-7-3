# Audit Notes and Proof-Route Differences

This file documents the correspondence between the Lean 4 formalization (`FejesTothP7/Paper/Statements.lean`, 43 theorems) and the printed paper, including places where the Lean proof achieves the exact same statement by an equivalent elementary proof route.

## Axioms and Trust Surface

- **Axioms:** Every one of the 43 public theorems in `FejesTothP7/Paper/Statements.lean` depends strictly on Lean 4’s three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There are zero custom axioms, zero cited axioms, zero `sorry`, and zero computational oracles.
- **Open-disc equivalence:** `Packing.lean` defines `IsPacking` and `Overlaps` via center distances (`2 * r ≤ dist x y` and `dist P q < 2 * r`). `isPacking_iff_pairwise_disjoint_balls` and `overlaps_iff_balls_inter_nonempty` establish exact equivalence with pairwise disjointness / nonempty intersection of open hyperbolic balls `Metric.ball x r` for all `r > 0`.
- **Concrete `{7, 3}` / `{3, 7}` certification:** `sites37` is defined concretely as the orbit of the origin under the `(2, 3, 7)` reflection group `Delta237`. `sites37_tiling_certification` proves that `sites37` is a radius-`r7` packing, every site admits a 7-neighbor `SiteFrame`, every point of `H2` lies within covering radius `Rc7` of some site, and `Delta237` acts transitively on `sites37`.

## Proof-Route Differences

1. **Global `{3, 7}` construction and Lemma 5.1 (`ZoneLayers.lean`, `ZoneGeometry.lean`, `ZoneConvexity.lean`, `TilingMain.lean`):**
   Instead of invoking the hyperbolic `(k + 2)`-gon interior-angle-sum theorem to prove embeddedness and convexity of the zone polygons `P_m`, the formalization generates each zone layer `zoneLayer m` explicitly by applying exact `(2, 3, 7)` hyperbolic frame transitions, proves uniform half-plane containment (`ZoneConvexInv m`) and exponential radial growth (`zoneGrowthBase ^ m ≤ v.z`) by direct Lorentzian `detH` induction, proves global packing of the union `V_all`, and identifies `V_all = sites37` via local edge-rigidity of `Delta237`. This yields the full statement of Lemma 5.1 (including simple cycle structure, exact inner/ring/outer neighbor counts, convexity of `P_m`, and word properties (a)–(c)) with zero external topological prerequisites.
2. **Lemma 2.5 (Reuleaux-Triangle Lemma, `LocalGeom.lean`):**
   Rather than arguing via geodesics through boundary intersections of three circles, the formalization expresses the two points `P, Q` in positive/signed conical coordinates relative to the equilateral triangle `(u, v, w)` and applies pigeonhole on edge half-planes together with Lemma 2.4(ii) (`lem_2_4_edge`).
3. **Lemma 3.2 (Tip-Disc Lemma, `TipGeom.lean`):**
   Instead of a spherical/hyperbolic trigonometry monotonicity case analysis along the boundary arcs, the formalization rewrites the tip-disc distance inequality in the variable `u = tanh(ρ/2)^2`, obtaining an exact concave quadratic with roots at `ρ = ρ*` and `ρ = 2r`, giving both the bound `d(P, M) ≤ r` and the unique equality characterization `P = tip` algebraically.
4. **Section 1 & Figure 2 metric gap (`MetricGap.lean`):**
   The strict negativity `Δ_p < 0`, `|h_p - ρ_p^*| < r_p` for all `p ≥ 8`, and the `7 ≤ p ≤ 14` vs `p ≥ 15` regime split are proved uniformly from the exact algebraic formula `tanh((h_p - r_p)/2) = sqrt(λ_p^2 - 3) / (λ_p + 1)` in `λ_p = 2 cos(π/p)`.
5. **Corollary 1.2 upper bound on order of solidity (`CorollaryOrder.lean`):**
   To rule out solidity of order `m` for all `m ≥ 2`, the formalization constructs an explicit `m`-truncation removing two adjacent neighbors of the origin and `m - 2` additional sites, moves the origin circle to the triangle circumcenter `O` (which is proved to lie at distance `> 2r` from every other site), and rules out any congruence to another `m`-truncation uniformly for all `m ≥ 2` via cofinite edge-rigidity (`isometry_preserves_sites37_of_cofinite`).
6. **Section 2.1 numerical bounds (`NumericalBounds.lean`):**
   The 5-decimal bounds for `2r, h, R_c, ρ*` are certified purely inside Lean’s kernel via a 10-digit root enclosure of the minimal cubic `λ^3 - λ^2 - 2λ + 1 = 0` and Taylor remainder bounds from `Real.exp_bound`.

## Background Context Not Formalized as Separate Claims

- Historical remarks in Section 1 comparing `{3, p}` zone-word run lengths `p - 6` and `p - 5` for `p ≥ 8` (background context citing Bezdek 1979 and Fejes Tóth 1968/1979) are contextual exposition rather than numbered claims of the proof for `{7, 3}`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
