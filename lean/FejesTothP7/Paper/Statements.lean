/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Defs.H2
import FejesTothP7.Defs.Constants
import FejesTothP7.Defs.Packing
import FejesTothP7.Defs.Tiling
import FejesTothP7.Proofs.Certify
import FejesTothP7.Proofs.NumericalBounds
import Mathlib.Topology.Order.Basic

/-!
# Statements of All Claims in the Paper

This file states and wires every numbered theorem, corollary, proposition, lemma, remark,
named proof step, and key in-text/caption mathematical claim of the paper.
Every theorem in this file is proved from Lean's three standard axioms alone.
-/

noncomputable section

open Classical Filter Set

namespace FejesTothP7.Paper

/-! ## Section 1: Main results and metric gap -/

/-- **Theorem 1.1**: The face-incircles of the regular hyperbolic tiling `{7, 3}`
    form a strongly solid packing. -/
theorem thm_1_1_strong_solidity :
    IsStronglySolid r7 sites37 :=
  FejesTothP7.Proofs.thm_1_1_strong_solidity

/-- **Corollary 1.2**: For the face-incircle packing `Π₇` of `{7, 3}`,
    the grade of saturatedness is `g₇ = 3` and the order of solidity is `k₇ = 1 = g₇ - 2`. -/
theorem cor_1_2_grade_and_order :
    HasGradeOfSaturatedness r7 sites37 3 ∧ HasOrderOfSolidity r7 sites37 1 :=
  FejesTothP7.Proofs.cor_1_2_grade_and_order

/-- **Section 1 in-text claim**: Since the symmetry group of `{7, 3}` acts transitively on faces,
    strong solidity of `Π₇` is equivalent to solidity of order `1`. -/
theorem text_1_strong_solidity_iff_order_one :
    IsStronglySolid r7 sites37 ↔ IsSolidOfOrder r7 sites37 1 :=
  FejesTothP7.Proofs.text_1_strong_solidity_iff_order_one

/-- **Section 1 & Figure 2 caption**: For every `p ≥ 8`, the metric gap `Δ_p = h_p - (r_p + ρ_p^*)`
    is strictly negative, and `|h_p - ρ_p^*| < r_p`. -/
theorem text_1_metric_gap_p_ge_8 (p : ℕ) (hp : 8 ≤ p) :
    deltaP p < 0 ∧ |hP p - rhoStarP p| < rP p :=
  FejesTothP7.Proofs.text_1_metric_gap_p_ge_8 p hp

/-- **Figure 2 caption**: For `7 ≤ p ≤ 14`, `ρ_p^* ≤ h_p` with `h₁₄ = ρ₁₄^*`;
    for `p ≥ 15`, `ρ_p^* < 2 r_p < h_p + r_p`. -/
theorem fig_2_caption_regime_split :
    (∀ p : ℕ, 7 ≤ p → p ≤ 14 → rhoStarP p ≤ hP p) ∧
    hP 14 = rhoStarP 14 ∧
    (∀ p : ℕ, 15 ≤ p → rhoStarP p < 2 * rP p ∧ 2 * rP p < hP p + rP p) :=
  FejesTothP7.Proofs.fig_2_caption_regime_split

/-- **Figure 2 caption (`p = 7` gap)**: The metric gap vanishes at `p = 7`, i.e. `Δ₇ = 0`. -/
theorem fig_2_delta7_zero :
    deltaP 7 = 0 :=
  FejesTothP7.Proofs.fig_2_delta7_zero

/-! ## Section 2: Constants, packing bridges, tiling certification, triviality, and local geometry -/

/-- **Open-disc packing bridge**: For `r > 0`, `IsPacking r C` is equivalent to pairwise disjointness
    of the open discs `Metric.ball x r`. -/
theorem isPacking_iff_pairwise_disjoint_balls {r : ℝ} (hr : 0 < r) (C : Set H2) :
    IsPacking r C ↔
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (Metric.ball x r) (Metric.ball y r) :=
  FejesTothP7.Proofs.isPacking_iff_pairwise_disjoint_balls hr C

/-- **Open-disc overlap bridge**: For `r > 0`, `Overlaps r P q` is equivalent to nonempty intersection
    of the open discs `Metric.ball P r` and `Metric.ball q r`. -/
theorem overlaps_iff_balls_inter_nonempty {r : ℝ} (hr : 0 < r) (P q : H2) :
    Overlaps r P q ↔ (Metric.ball P r ∩ Metric.ball q r).Nonempty :=
  FejesTothP7.Proofs.overlaps_iff_balls_inter_nonempty hr P q

/-- **Section 2.1 `{7, 3}` / `{3, 7}` certification**: The concrete `Delta237`-orbit `sites37` is a
    radius-`r7` packing in which every site has a 7-neighbor `SiteFrame`, every point of `H2` lies
    within covering radius `Rc7` of a site, and `Delta237` acts transitively on `sites37`. -/
theorem sites37_tiling_certification :
    IsPacking r7 sites37 ∧
    (∀ v ∈ sites37, Nonempty (SiteFrame sites37 v)) ∧
    (∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7) ∧
    (∀ u ∈ sites37, ∀ v ∈ sites37, ∃ g ∈ Delta237, g u = v ∧ g '' sites37 = sites37) :=
  FejesTothP7.Proofs.sites37_tiling_certification

/-- **Equation (1)**: Hyperbolic trigonometric identities for `r, h, R_c` at `p = 7`. -/
theorem eq_1_consts :
    Real.cosh r7 = 1 / (2 * Real.sin (Real.pi / 7)) ∧
    Real.cosh (2 * r7) = 2 * Real.cosh r7 ^ 2 - 1 ∧
    Real.cosh (2 * r7) = Real.cos α7 / (1 - Real.cos α7) ∧
    Real.cosh h7 = Real.cosh (2 * r7) / Real.cosh r7 ∧
    Real.sinh Rc7 = Real.sinh r7 / Real.sin (Real.pi / 3) :=
  FejesTothP7.Proofs.eq_1_consts

/-- **Equation (2)**: Ordering of the basic metric constants `r < R_c < h < 2r`. -/
theorem eq_2_order :
    r7 < Rc7 ∧ Rc7 < h7 ∧ h7 < 2 * r7 :=
  FejesTothP7.Proofs.eq_2_order

/-- **Section 2.1 properties of `β` and `ρ*`**:
    `coth(2r) tanh r = cosh(2r)/(cosh(2r)+1) = cos α`, `β` strictly decreasing on `(0, 2r]`,
    `lim_{ρ → 0⁺} β(ρ) = π/2`, `β(2r) = α`, `β(ρ) > α` on `(0, 2r)`, and `ρ* ∈ (0, 2r)`
    satisfies `β(ρ*) = 3α/2`. -/
theorem text_2_beta_properties :
    (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 =
      Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) ∧
    Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) = Real.cos α7 ∧
    StrictAntiOn β7 (Set.Ioc 0 (2 * r7)) ∧
    Tendsto β7 (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) ∧
    β7 (2 * r7) = α7 ∧
    (∀ ρ ∈ Set.Ioo 0 (2 * r7), α7 < β7 ρ) ∧
    0 < ρ7 ∧ ρ7 < 2 * r7 ∧ β7 ρ7 = 3 * α7 / 2 :=
  FejesTothP7.Proofs.text_2_beta_properties

/-- **Section 2.1 numerical bounds**: 5-decimal bounds on `2 r7 ≈ 1.09055`, `h7 ≈ 0.90380`,
    `Rc7 ≈ 0.62067`, and `ρ7 ≈ 0.35853`. -/
theorem text_2_numerical_bounds :
    |2 * r7 - 1.09055| < 5e-6 ∧
    |h7 - 0.90380| < 5e-6 ∧
    |Rc7 - 0.62067| < 5e-6 ∧
    |ρ7 - 0.35853| < 5e-6 :=
  FejesTothP7.Proofs.text_2_numerical_bounds

/-- **Lemma 2.1**: A rearrangement `X` of a finite subset `s ⊆ S` is trivial if and only if
    every circle of `X` is centered at a site of `{3, 7}`. -/
theorem lem_2_1_trivial_rearrangement (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) s X) :
    IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37 :=
  FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀ s X hX

/-- **Lemma 2.2 (Polar Lemma)**: For `P = polar(ρ, θ)` with `0 < ρ ≤ 2r` and `n = polar(2r, φ)`,
    `d(P, n) < 2r ↔ angleDiff(θ, φ) < β(ρ)` and `d(P, n) = 2r ↔ angleDiff(θ, φ) = β(ρ)`.
    We express the angle difference in `[0, π]` via `Real.arccos (Real.cos (θ - φ))`. -/
theorem lem_2_2_polar (φ_iso : H2 ≃ᵢ H2) (ρ θ φ : ℝ)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * r7) :
    (dist (φ_iso (H2.polarOrigin ρ θ)) (φ_iso (H2.polarOrigin (2 * r7) φ)) < 2 * r7 ↔
      Real.arccos (Real.cos (θ - φ)) < β7 ρ) ∧
    (dist (φ_iso (H2.polarOrigin ρ θ)) (φ_iso (H2.polarOrigin (2 * r7) φ)) = 2 * r7 ↔
      Real.arccos (Real.cos (θ - φ)) = β7 ρ) :=
  FejesTothP7.Proofs.lem_2_2_polar φ_iso ρ θ φ hρ0 hρ2

/-- **Lemma 2.3(a) (Free-Arc Lemma, part a)**:
    If `v` has zero, one, or two non-adjacent unfixed neighbors, no admissible `P ≠ v` with
    `d(P, v) < 2r` exists; if `v` has profile `τ_k` (`k ∈ {2, 3, 4}`), then `P` has a polar angle
    `θ ∈ [β(ρ) - α, k α - β(ρ)]`. -/
theorem lem_2_3_freearc_a (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ((∀ j : Fin 7, F.nbr j ∉ U) → False) ∧
    ((∃ j₀ : Fin 7, ∀ j : Fin 7, F.nbr j ∈ U → j = j₀) → False) ∧
    ((∃ j₁ j₂ : Fin 7, (∀ j : Fin 7, F.nbr j ∈ U → j = j₁ ∨ j = j₂) ∧
      (j₁.1 + 1) % 7 ≠ j₂.1 ∧ (j₂.1 + 1) % 7 ≠ j₁.1) → False) ∧
    (∀ k : ℕ, k = 2 ∨ k = 3 ∨ k = 4 → HasProfile V U v k F →
      ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
        β7 (dist P v) - α7 ≤ θ ∧ θ ≤ (k : ℝ) * α7 - β7 (dist P v)) :=
  FejesTothP7.Proofs.lem_2_3_freearc_a V U v F P hPv hPr hadm

/-- **Lemma 2.3(b) (Free-Arc Lemma, part b)**:
    At a `τ₃` site `v` with unfixed neighbors `a, i, b` at `0, α, 2α`, every admissible `P ≠ v`
    overlapping `v` overlaps `i`, overlaps `a ↔ θ < β`, overlaps `b ↔ θ > 2α - β`,
    overlaps at least one of `a, b`, and if it overlaps only one of `a, b` then `β ≤ 3α/2` (`ρ ≥ ρ*`). -/
theorem lem_2_3_freearc_b (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
      β7 (dist P v) - α7 ≤ θ ∧ θ ≤ 3 * α7 - β7 (dist P v) ∧
      Overlaps r7 P (F.nbr 1) ∧
      (Overlaps r7 P (F.nbr 0) ↔ θ < β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 (dist P v) < θ) ∧
      (Overlaps r7 P (F.nbr 0) ∨ Overlaps r7 P (F.nbr 2)) ∧
      ((Overlaps r7 P (F.nbr 0) ∧ ¬ Overlaps r7 P (F.nbr 2)) ∨
       (¬ Overlaps r7 P (F.nbr 0) ∧ Overlaps r7 P (F.nbr 2)) →
        β7 (dist P v) ≤ 3 * α7 / 2 ∧ ρ7 ≤ dist P v) :=
  FejesTothP7.Proofs.lem_2_3_freearc_b V U v F hprof P hPv hPr hadm

/-- **Lemma 2.3(c) (Free-Arc Lemma, part c)**:
    At a `τ₄` site `v` with unfixed neighbors `a, i, j, b` at `0, α, 2α, 3α`, overlap equivalences
    hold and if `P` overlaps neither `a` nor `b` then `θ ∈ [β, 3α - β]` and `P` overlaps both `i, j`. -/
theorem lem_2_3_freearc_c (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 4 F)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
      β7 (dist P v) - α7 ≤ θ ∧ θ ≤ 4 * α7 - β7 (dist P v) ∧
      (Overlaps r7 P (F.nbr 0) ↔ θ < β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 1) ↔ θ < α7 + β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 (dist P v) < θ) ∧
      (Overlaps r7 P (F.nbr 3) ↔ 3 * α7 - β7 (dist P v) < θ) ∧
      (¬ Overlaps r7 P (F.nbr 0) → ¬ Overlaps r7 P (F.nbr 3) →
        β7 (dist P v) ≤ θ ∧ θ ≤ 3 * α7 - β7 (dist P v) ∧
        Overlaps r7 P (F.nbr 1) ∧ Overlaps r7 P (F.nbr 2)) :=
  FejesTothP7.Proofs.lem_2_3_freearc_c V U v F hprof P hPv hPr hadm

/-- **Lemma 2.3(d) (Free-Arc Lemma, part d)**:
    A site `v` overlaps no neighbor of `v`; consequently, if a site has at least two overlappers
    in a rearrangement, no circle of that rearrangement is centered at it. -/
theorem lem_2_3_freearc_d (v w : H2) (hadj : Adj37 v w) :
    ¬ Overlaps r7 v w :=
  FejesTothP7.Proofs.lem_2_3_freearc_d v w hadj

/-- **Lemma 2.3(d) consequence**: If `q` has two distinct overlappers in a packing `X`,
    then `q ∉ X`. -/
theorem lem_2_3_freearc_d_conseq (X : Finset H2) (hpack : IsPacking r7 (X : Set H2)) (q : H2)
    (h2 : ∃ P₁ ∈ X, ∃ P₂ ∈ X, P₁ ≠ P₂ ∧ Overlaps r7 P₁ q ∧ Overlaps r7 P₂ q) :
    q ∉ X :=
  FejesTothP7.Proofs.lem_2_3_freearc_d_conseq X hpack q h2

/-- **Lemma 2.4 (Edge Lemma)**:
    Let `v, v'` be adjacent sites with a common neighbor `o` (equilateral triangle of side `2r`).
    (i) Every point `P` with `d(P, o) ≥ 2r` overlapping both `v` and `v'` lies on the open side
    of geodesic `v v'` opposite `o`.
    (ii) Any two points `P, P'` overlapping both `v` and `v'` on the same open side of `v v'`
    satisfy `d(P, P') < 2r`. -/
theorem lem_2_4_edge (v v' o : H2)
    (hvv' : Adj37 v v') (hvo : Adj37 v o) (hv'o : Adj37 v' o) :
    (∀ P : H2, Overlaps r7 P v → Overlaps r7 P v' → 2 * r7 ≤ dist P o →
      H2.detH v v' P * H2.detH v v' o < 0) ∧
    (∀ P P' : H2, Overlaps r7 P v → Overlaps r7 P v' →
      Overlaps r7 P' v → Overlaps r7 P' v' →
      0 < H2.detH v v' P * H2.detH v v' P' → dist P P' < 2 * r7) :=
  FejesTothP7.Proofs.lem_2_4_edge v v' o hvv' hvo hv'o

/-- **Lemma 2.4 consequence**: At most one circle of a rearrangement `X` overlaps both ends
    of an edge `(v, v')` possessing a fixed common neighbor `o`. -/
theorem lem_2_4_edge_conseq (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X)
    (v v' o : H2) (hvv' : Adj37 v v') (hvo : Adj37 v o) (hv'o : Adj37 v' o)
    (ho_fix : o ∈ sites37 \ UnfixedSites c₀ s) :
    (X.filter (fun P => Overlaps r7 P v ∧ Overlaps r7 P v')).card ≤ 1 :=
  FejesTothP7.Proofs.lem_2_4_edge_conseq c₀ s X hX v v' o hvv' hvo hv'o ho_fix

/-- **Lemma 2.5 (Reuleaux-Triangle Lemma)**:
    For any three mutually adjacent sites `u, v, w` of `{3, 7}`, any two points in
    `B(u, 2r) ∩ B(v, 2r) ∩ B(w, 2r)` lie at distance strictly less than `2r`. -/
theorem lem_2_5_reuleaux (u v w P Q : H2)
    (huv : Adj37 u v) (hvw : Adj37 v w) (hwu : Adj37 w u)
    (hPu : Overlaps r7 P u) (hPv : Overlaps r7 P v) (hPw : Overlaps r7 P w)
    (hQu : Overlaps r7 Q u) (hQv : Overlaps r7 Q v) (hQw : Overlaps r7 Q w) :
    dist P Q < 2 * r7 :=
  FejesTothP7.Proofs.lem_2_5_reuleaux u v w P Q huv hvw hwu hPu hPv hPw hQu hQv hQw

/-! ## Section 3: Exact `p = 7` identity and tip geometry -/

/-- **Proposition 3.1 (Exact `p = 7` identity)**: `h = r + ρ*`. -/
theorem prop_3_1_exact_identity :
    h7 = r7 + ρ7 :=
  FejesTothP7.Proofs.prop_3_1_exact_identity

/-- **Equation (6)**: Minimal cubic `λ³ - λ² - 2λ + 1 = 0` for `λ = 2 cos(π/7)`. -/
theorem eq_6_lambda7_cubic :
    (2 * Real.cos (Real.pi / 7)) ^ 3 - (2 * Real.cos (Real.pi / 7)) ^ 2 -
      2 * (2 * Real.cos (Real.pi / 7)) + 1 = 0 :=
  FejesTothP7.Proofs.lambda7_cubic

/-- **Section 3.1 & Equation (5)**: Tip distances `d(T, M) = r`, `d(T, n₀) = d(T, n₃) = 2r`,
    and `d(T, n₁) = d(T, n₂) = arcosh(cosh² r) < 2r`. -/
theorem eq_5_tip_distances (V : Set H2) (v : H2) (F : SiteFrame V v) :
    let T := F.tip12
    let M := H2.mid (F.nbr 1) (F.nbr 2)
    dist T M = r7 ∧
    dist T (F.nbr 0) = 2 * r7 ∧
    dist T (F.nbr 3) = 2 * r7 ∧
    dist T (F.nbr 1) = Real.arcosh (Real.cosh r7 ^ 2) ∧
    dist T (F.nbr 2) = Real.arcosh (Real.cosh r7 ^ 2) ∧
    Real.arcosh (Real.cosh r7 ^ 2) < 2 * r7 :=
  FejesTothP7.Proofs.eq_5_tip_distances V v F

/-- **Lemma 3.2 (Tip-Disc Lemma, standard & mirror forms)**:
    Every `P ∈ K₂` satisfies `d(P, mid(n₁, n₂)) ≤ r`, with equality iff `P = tip(v; n₁, n₂)`;
    symmetrically every `P ∈ K₂'` satisfies `d(P, mid(n₀, n₁)) ≤ r`, with equality iff `P = tip(v; n₀, n₁)`. -/
theorem lem_3_2_tip_disc (V : Set H2) (v : H2) (F : SiteFrame V v) :
    (∀ P ∈ F.K2, dist P (H2.mid (F.nbr 1) (F.nbr 2)) ≤ r7 ∧
      (dist P (H2.mid (F.nbr 1) (F.nbr 2)) = r7 ↔ P = F.tip12)) ∧
    (∀ P ∈ F.K2Mirror, dist P (H2.mid (F.nbr 0) (F.nbr 1)) ≤ r7 ∧
      (dist P (H2.mid (F.nbr 0) (F.nbr 1)) = r7 ↔ P = F.tip01)) :=
  FejesTothP7.Proofs.lem_3_2_tip_disc V v F

/-- **Lemma 3.3 (Strict Half-Lens Bound)**:
    If `v` has profile `τ₃` with unfixed neighbors `a, i, b` at `0, α, 2α` and `T = tip(v; i, b)`,
    then every admissible point `Y` overlapping both `a` and `v` satisfies `d(Y, T) < 2r`. -/
theorem lem_3_3_half_lens (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F)
    (Y : H2) (hadm : IsAdmissible r7 (V \ U) Y)
    (hYa : Overlaps r7 Y (F.nbr 0)) (hYv : Overlaps r7 Y v) :
    dist Y F.tip12 < 2 * r7 :=
  FejesTothP7.Proofs.lem_3_3_half_lens V U v F hprof Y hadm hYa hYv

/-! ## Section 4: Good sets and the joining lemmas -/

/-- **Lemma 4.1 (Bridge and Deletion Remarks)**:
    (a) Any non-trivial rearrangement `X` of `s' ⊆ S` has at least two circles not centered at sites;
        every singleton `{c} ⊆ S` is good.
    (b) If `c` cannot be joined to a good set `s`, then in every non-trivial rearrangement `X` of
        `s ∪ {c}`, at least two circles of `X` overlap `c`.
    (c) Every subset of a good set is good; if `c` cannot be joined to `s`, then in every non-trivial
        rearrangement of `s ∪ {c}`, every qualifying site `q` has at least two overlappers and carries
        no circle centered at `q`. -/
theorem lem_4_1_bridge (c₀ : H2) (hc₀ : c₀ ∈ sites37) :
    (∀ s' X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s' X →
      ¬ IsTrivialRearrangement (oneVacancy c₀) s' X →
      2 ≤ (X.filter (fun p => p ∉ sites37)).card) ∧
    (∀ c ∈ oneVacancy c₀, IsGood c₀ {c}) ∧
    (∀ s : Finset H2, ∀ c : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p c)).card) ∧
    (∀ s s' : Finset H2, IsGood c₀ s → s' ⊆ s → IsGood c₀ s') ∧
    (∀ s : Finset H2, ∀ c q : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c → IsQualifying c₀ s c q →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p q)).card ∧ q ∉ X) :=
  FejesTothP7.Proofs.lem_4_1_bridge c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)

/-- **Remark 4.2 (`τ₃` Edge-Count)**:
    A qualifying site `q` with profile `τ₃` (unfixed neighbors `a, i, b`) in a non-trivial
    rearrangement `X` of `s ∪ {c}` has exactly two overlappers: one overlapping `(a, q)` but not `b`,
    and the other overlapping `(q, b)` but not `a`. -/
theorem rem_4_2_tau3_edge_count (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c q : H2) (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hqual : IsQualifying c₀ s c q) (F : SiteFrame sites37 q)
    (hprof : HasProfile sites37 (UnfixedSites c₀ (insert c s)) q 3 F)
    (X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) (insert c s) X)
    (hnt : ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X) :
    ∃ P₁ ∈ X, ∃ P₂ ∈ X, P₁ ≠ P₂ ∧
      (∀ P ∈ X, Overlaps r7 P q ↔ P = P₁ ∨ P = P₂) ∧
      Overlaps r7 P₁ (F.nbr 0) ∧ ¬ Overlaps r7 P₁ (F.nbr 2) ∧
      Overlaps r7 P₂ (F.nbr 2) ∧ ¬ Overlaps r7 P₂ (F.nbr 0) :=
  FejesTothP7.Proofs.rem_4_2_tau3_edge_count c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)
    s c q hs hc hcs hqual F hprof X hX hnt

/-- **Lemma 4.3 (Joining with at most two unfixed neighbors)**:
    If `s` is good and `c ∈ S \ s` has at most two unfixed neighbors relative to `s ∪ {c}`,
    then `c` can be joined to `s`. -/
theorem lem_4_3_join_le_two (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c : H2) (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (F : SiteFrame sites37 c)
    (hle2 : (Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ UnfixedSites c₀ (insert c s))).card ≤ 2) :
    CanJoin c₀ s c :=
  FejesTothP7.Proofs.lem_4_3_join_le_two c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)
    s c hs hc hcs F hle2

/-- **Lemma 4.4 (Profile-`τ₃` joining lemma)**:
    If `s` is good, `c ∈ S \ s` has profile `τ₃` with consecutive unfixed neighbors `c₁, c₂, c₃`
    such that `c₁, c₃ ∈ s`, and all unfixed neighbors of `c₁` lie in `{c₄, c₂, c}` and all unfixed
    neighbors of `c₃` lie in `{c, c₂, c₅}`, then `c` can be joined to `s`. -/
theorem lem_4_4_join_tau3 (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c c₁ c₂ c₃ c₄ c₅ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (Fc : SiteFrame sites37 c)
    (hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc)
    (hc1_eq : Fc.nbr 0 = c₁) (hc2_eq : Fc.nbr 1 = c₂) (hc3_eq : Fc.nbr 2 = c₃)
    (hc1_s : c₁ ∈ s) (hc3_s : c₃ ∈ s)
    (hc4_adj1 : Adj37 c₄ c₁) (hc4_adj2 : Adj37 c₄ c₂) (hc4_ne : c₄ ≠ c)
    (hc5_adj2 : Adj37 c₅ c₂) (hc5_adj3 : Adj37 c₅ c₃) (hc5_ne : c₅ ≠ c)
    (hu1 : ∀ w ∈ sites37, Adj37 c₁ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₄ ∨ w = c₂ ∨ w = c)
    (hu3 : ∀ w ∈ sites37, Adj37 c₃ w → w ∈ UnfixedSites c₀ (insert c s) → w = c ∨ w = c₂ ∨ w = c₅) :
    CanJoin c₀ s c :=
  FejesTothP7.Proofs.lem_4_4_join_tau3 c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)
    s c c₁ c₂ c₃ c₄ c₅ hs hc hcs Fc hprof_c hc1_eq hc2_eq hc3_eq hc1_s hc3_s
    hc4_adj1 hc4_adj2 hc4_ne hc5_adj2 hc5_adj3 hc5_ne hu1 hu3

/-- **Lemma 4.5, Step 1 (Edge counts)**: From `τ₃` profiles at the qualifying sites `c, c₁, c₆, c₇`
    in a non-trivial rearrangement `X` of `insert c s`, there exist overlappers `Y₁, Z, W, E, V₁, V₂ ∈ X`
    on the respective edges. -/
theorem lem_4_5_step1_edge_counts (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c c₁ c₃ c₄ c₆ c₇ c₈ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hqual_c : IsQualifying c₀ s c c) (hqual_c1 : IsQualifying c₀ s c c₁)
    (hqual_c6 : IsQualifying c₀ s c c₆) (hqual_c7 : IsQualifying c₀ s c c₇)
    (Fc : SiteFrame sites37 c) (hFc_0 : Fc.nbr 0 = c₁) (hFc_2 : Fc.nbr 2 = c₃)
    (hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc)
    (Fc1 : SiteFrame sites37 c₁) (hFc1_0 : Fc1.nbr 0 = c₄) (hFc1_2 : Fc1.nbr 2 = c)
    (hprof_c1 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₁ 3 Fc1)
    (Fc6 : SiteFrame sites37 c₆) (hFc6_0 : Fc6.nbr 0 = c₃) (hFc6_2 : Fc6.nbr 2 = c₇)
    (hprof_c6 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₆ 3 Fc6)
    (Fc7 : SiteFrame sites37 c₇) (hFc7_0 : Fc7.nbr 0 = c₈) (hFc7_2 : Fc7.nbr 2 = c₆)
    (hprof_c7 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₇ 3 Fc7)
    (X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) (insert c s) X)
    (hnt : ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X) :
    ∃ Y₁ ∈ X, ∃ Z ∈ X, ∃ W ∈ X, ∃ E ∈ X, ∃ V₁ ∈ X, ∃ V₂ ∈ X,
      Z ≠ W ∧ Y₁ ≠ Z ∧ E ≠ V₁ ∧ V₂ ≠ V₁ ∧
      (∀ P ∈ X, Overlaps r7 P c ↔ P = Z ∨ P = W) ∧
      (∀ P ∈ X, Overlaps r7 P c₁ ↔ P = Y₁ ∨ P = Z) ∧
      (∀ P ∈ X, Overlaps r7 P c₆ ↔ P = E ∨ P = V₁) ∧
      (∀ P ∈ X, Overlaps r7 P c₇ ↔ P = V₂ ∨ P = V₁) ∧
      Overlaps r7 Y₁ c₄ ∧ ¬ Overlaps r7 Y₁ c ∧
      Overlaps r7 Z c₁ ∧ ¬ Overlaps r7 Z c₃ ∧ ¬ Overlaps r7 Z c₄ ∧
      Overlaps r7 W c₃ ∧ ¬ Overlaps r7 W c₁ ∧
      Overlaps r7 E c₃ ∧ ¬ Overlaps r7 E c₇ ∧
      Overlaps r7 V₁ c₇ ∧ ¬ Overlaps r7 V₁ c₃ ∧ ¬ Overlaps r7 V₁ c₈ ∧
      Overlaps r7 V₂ c₈ ∧ ¬ Overlaps r7 V₂ c₆ :=
  FejesTothP7.Proofs.lem_4_5_step1_edge_counts c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)
    s c c₁ c₃ c₄ c₆ c₇ c₈ hs hc hcs hqual_c hqual_c1 hqual_c6 hqual_c7
    Fc hFc_0 hFc_2 hprof_c Fc1 hFc1_0 hFc1_2 hprof_c1
    Fc6 hFc6_0 hFc6_2 hprof_c6 Fc7 hFc7_0 hFc7_2 hprof_c7 X hX hnt

/-- **Lemma 4.5, Step 2 (`W` overlaps `c₅`)**: Tip-Disc + Half-Lens forcing `W` to overlap `c₅`. -/
theorem lem_4_5_step2_W_overlaps_c5 (U : Set H2) (c c₁ c₂ c₃ c₄ c₅ c₆ : H2)
    (Fc1 : SiteFrame sites37 c₁)
    (hFc1_0 : Fc1.nbr 0 = c₄) (hFc1_1 : Fc1.nbr 1 = c₂) (hFc1_2 : Fc1.nbr 2 = c)
    (hprof_c1 : HasProfile sites37 U c₁ 3 Fc1)
    (Fc3 : SiteFrame sites37 c₃)
    (hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc1_notX : c₁ ∉ X) (hc3_notX : c₃ ∉ X)
    (Y₁ Z W : H2) (hY1X : Y₁ ∈ X) (hZX : Z ∈ X) (hWX : W ∈ X)
    (hZW_ne : Z ≠ W) (hY1Z_ne : Y₁ ≠ Z)
    (hY1_c1 : Overlaps r7 Y₁ c₁) (hY1_c4 : Overlaps r7 Y₁ c₄)
    (hZ_c1 : Overlaps r7 Z c₁) (hZ_c : Overlaps r7 Z c) (hZ_nc4 : ¬ Overlaps r7 Z c₄)
    (hW_c3 : Overlaps r7 W c₃) :
    Overlaps r7 W c₅ :=
  FejesTothP7.Proofs.lem_4_5_step2_W_overlaps_c5 U c c₁ c₂ c₃ c₄ c₅ c₆
    Fc1 hFc1_0 hFc1_1 hFc1_2 hprof_c1 Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3
    X hpackX hadmX hc1_notX hc3_notX Y₁ Z W hY1X hZX hWX hZW_ne hY1Z_ne
    hY1_c1 hY1_c4 hZ_c1 hZ_c hZ_nc4 hW_c3

/-- **Lemma 4.5, Step 3 (`E` overlaps `c₂`)**: Symmetrically, Tip-Disc + Half-Lens force `E` to overlap `c₂`. -/
theorem lem_4_5_step3_E_overlaps_c2 (U : Set H2) (c c₂ c₃ c₅ c₆ c₇ c₈ : H2)
    (Fc3 : SiteFrame sites37 c₃)
    (hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (Fc7 : SiteFrame sites37 c₇)
    (hFc7_0 : Fc7.nbr 0 = c₈) (hFc7_1 : Fc7.nbr 1 = c₅) (hFc7_2 : Fc7.nbr 2 = c₆)
    (hprof_c7 : HasProfile sites37 U c₇ 3 Fc7)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc3_notX : c₃ ∉ X) (hc7_notX : c₇ ∉ X)
    (E V₁ V₂ : H2) (hEX : E ∈ X) (hV1X : V₁ ∈ X) (hV2X : V₂ ∈ X)
    (hEV1_ne : E ≠ V₁) (hV2V1_ne : V₂ ≠ V₁)
    (hE_c3 : Overlaps r7 E c₃)
    (hV1_c7 : Overlaps r7 V₁ c₇) (hV1_c6 : Overlaps r7 V₁ c₆) (hV1_nc8 : ¬ Overlaps r7 V₁ c₈)
    (hV2_c7 : Overlaps r7 V₂ c₇) (hV2_c8 : Overlaps r7 V₂ c₈) :
    Overlaps r7 E c₂ :=
  FejesTothP7.Proofs.lem_4_5_step3_E_overlaps_c2 U c c₂ c₃ c₅ c₆ c₇ c₈
    Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3 Fc7 hFc7_0 hFc7_1 hFc7_2 hprof_c7
    X hpackX hadmX hc3_notX hc7_notX E V₁ V₂ hEX hV1X hV2X hEV1_ne hV2V1_ne
    hE_c3 hV1_c7 hV1_c6 hV1_nc8 hV2_c7 hV2_c8

/-- **Lemma 4.5, Step 4 (`W = E`)**: Reuleaux-Triangle Lemma on `c₂, c₃, c₅` forces `W = E`. -/
theorem lem_4_5_step4_W_eq_E (U : Set H2) (c c₂ c₃ c₅ c₆ : H2)
    (hadj_c2c3 : Adj37 c₂ c₃) (hadj_c3c5 : Adj37 c₃ c₅) (hadj_c5c2 : Adj37 c₅ c₂)
    (Fc : SiteFrame sites37 c) (hFc_1 : Fc.nbr 1 = c₂)
    (hprof_c : HasProfile sites37 U c 3 Fc)
    (Fc6 : SiteFrame sites37 c₆) (hFc6_1 : Fc6.nbr 1 = c₅)
    (hprof_c6 : HasProfile sites37 U c₆ 3 Fc6)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc_notX : c ∉ X) (hc6_notX : c₆ ∉ X)
    (W E : H2) (hWX : W ∈ X) (hEX : E ∈ X)
    (hW_c : Overlaps r7 W c) (hW_c3 : Overlaps r7 W c₃) (hW_c5 : Overlaps r7 W c₅)
    (hE_c6 : Overlaps r7 E c₆) (hE_c3 : Overlaps r7 E c₃) (hE_c2 : Overlaps r7 E c₂) :
    W = E ∧ Overlaps r7 W c₂ :=
  FejesTothP7.Proofs.lem_4_5_step4_W_eq_E U c c₂ c₃ c₅ c₆
    hadj_c2c3 hadj_c3c5 hadj_c5c2 Fc hFc_1 hprof_c Fc6 hFc6_1 hprof_c6
    X hpackX hadmX hc_notX hc6_notX W E hWX hEX hW_c hW_c3 hW_c5 hE_c6 hE_c3 hE_c2

/-- **Lemma 4.5, Step 5 (Contradiction at `c₃`)**: A second overlapper `G ≠ W` of `c₃` overlapping
    neither `c` nor `c₆` must overlap `c₂` and `c₅`, contradicting Lemma 2.5. -/
theorem lem_4_5_step5_contradiction_at_c3 (U : Set H2) (c c₂ c₃ c₅ c₆ : H2)
    (hadj_c2c3 : Adj37 c₂ c₃) (hadj_c3c5 : Adj37 c₃ c₅) (hadj_c5c2 : Adj37 c₅ c₂)
    (Fc3 : SiteFrame sites37 c₃)
    (hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc3_notX : c₃ ∉ X)
    (W G : H2) (hWX : W ∈ X) (hGX : G ∈ X) (hGW_ne : G ≠ W)
    (hW_c2 : Overlaps r7 W c₂) (hW_c3 : Overlaps r7 W c₃) (hW_c5 : Overlaps r7 W c₅)
    (hG_c3 : Overlaps r7 G c₃) (hGn_c : ¬ Overlaps r7 G c) (hGn_c6 : ¬ Overlaps r7 G c₆) :
    False :=
  FejesTothP7.Proofs.lem_4_5_step5_contradiction_at_c3 U c c₂ c₃ c₅ c₆
    hadj_c2c3 hadj_c3c5 hadj_c5c2 Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3
    X hpackX hadmX hc3_notX W G hWX hGX hGW_ne hW_c2 hW_c3 hW_c5 hG_c3 hGn_c hGn_c6

/-- **Lemma 4.5 (Nine-site closing lemma)**:
    Under the nine-site configuration `c, c₁, ..., c₈` around `c₂` and `c₅`,
    `c` can be joined to `s`. -/
theorem lem_4_5_nine_site (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hdistinct : [c, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈].Nodup)
    (Fc2 : SiteFrame sites37 c₂)
    (h2_0 : Fc2.nbr 0 = c₄) (h2_1 : Fc2.nbr 1 = c₁) (h2_2 : Fc2.nbr 2 = c)
    (h2_3 : Fc2.nbr 3 = c₃) (h2_4 : Fc2.nbr 4 = c₅)
    (Fc5 : SiteFrame sites37 c₅)
    (h5_0 : Fc5.nbr 0 = c₂) (h5_1 : Fc5.nbr 1 = c₃) (h5_2 : Fc5.nbr 2 = c₆)
    (h5_3 : Fc5.nbr 3 = c₇) (h5_4 : Fc5.nbr 4 = c₈)
    (hc1_s : c₁ ∈ s) (hc3_s : c₃ ∈ s) (hc6_s : c₆ ∈ s) (hc7_s : c₇ ∈ s)
    (hc2_u : c₂ ∈ UnfixedSites c₀ (insert c s)) (hc5_u : c₅ ∈ UnfixedSites c₀ (insert c s))
    (huc : ∀ w ∈ sites37, Adj37 c w → w ∈ UnfixedSites c₀ (insert c s) → w = c₁ ∨ w = c₂ ∨ w = c₃)
    (hu1 : ∀ w ∈ sites37, Adj37 c₁ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₄ ∨ w = c₂ ∨ w = c)
    (hu3 : ∀ w ∈ sites37, Adj37 c₃ w → w ∈ UnfixedSites c₀ (insert c s) →
      w = c ∨ w = c₂ ∨ w = c₅ ∨ w = c₆)
    (hu6 : ∀ w ∈ sites37, Adj37 c₆ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₃ ∨ w = c₅ ∨ w = c₇)
    (hu7 : ∀ w ∈ sites37, Adj37 c₇ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₆ ∨ w = c₅ ∨ w = c₈) :
    CanJoin c₀ s c :=
  FejesTothP7.Proofs.lem_4_5_nine_site c₀ hc₀
    FejesTothP7.Proofs.isPacking_sites37 FejesTothP7.Proofs.hFrame_sites37
    FejesTothP7.Proofs.covering_radius_Rc7
    (FejesTothP7.Proofs.lem_2_1_trivial_rearrangement c₀ hc₀)
    s c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ hs hc hcs hdistinct
    Fc2 h2_0 h2_1 h2_2 h2_3 h2_4 Fc5 h5_0 h5_1 h5_2 h5_3 h5_4
    hc1_s hc3_s hc6_s hc7_s hc2_u hc5_u huc hu1 hu3 hu6 hu7

/-! ## Section 5: Zone substitution, proof steps of Theorem 1.1 and Corollary 1.2 -/

/-- **Lemma 5.1 (Zone Substitution Lemma, combinatorial & geometric cycle structure)**:
    For every `m ≥ 1`, `Z_m(c₀)` is enumerated without repetition by a cyclic list `cyc` of length
    `(zoneWord m).length` forming a simple cycle bounding the convex polygon `P_m` containing
    `Z_0 ∪ ... ∪ Z_m`, where vertex `k` has `i ∈ {1, 2}` consecutive inner neighbors in `Z_{m-1}`
    matching `(zoneWord m)[k]`, two ring neighbors `cyc[(k-1) mod N], cyc[(k+1) mod N]` in `Z_m`,
    and `5 - i` consecutive outer neighbors in `Z_{m+1}`; together with word properties (a), (b),
    and (c) (`σ²` block decomposition and no adjacent `S-D-S` arcs through `k + 14`). -/
theorem lem_5_1_zone_substitution (c₀ : sites37) :
    (∀ m : ℕ, 1 ≤ m →
      ∃ cyc : List H2,
        cyc.Nodup ∧
        ∃ hlen : cyc.length = (zoneWord m).length,
        ({x | x ∈ cyc} : Set H2) = Zone c₀ m ∧
        (∀ (k : Fin cyc.length),
          let v := cyc.get k
          let vPrev := cyc.get ⟨(k.1 + cyc.length - 1) % cyc.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
          let vNext := cyc.get ⟨(k.1 + 1) % cyc.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
          let i : ℕ := if (zoneWord m).get (k.cast hlen) = .t1 then 1 else 2
          ∃ F : SiteFrame sites37 v,
            F.nbr 0 = vPrev ∧
            (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ i → F.nbr j ∈ Zone c₀ (m - 1)) ∧
            F.nbr (i + 1 : ℕ) = vNext ∧
            (∀ j : Fin 7, i + 2 ≤ j.1 → F.nbr j ∈ Zone c₀ (m + 1))) ∧
        (∀ (k : Fin cyc.length), ∀ x ∈ ZoneUnion c₀ m ∪ {c₀.1},
          0 ≤ H2.detH (cyc.get k)
            (cyc.get ⟨(k.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩) x)) ∧
    -- Part (a): for m ≥ 2, no two t2's are cyclically adjacent, and no three t1's are cyclically consecutive
    (∀ m : ℕ, 2 ≤ m →
      let w := zoneWord m
      ∀ (k : Fin w.length),
        (w.get k = .t2 →
          w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1) ∧
        (w.get k = .t1 →
          w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1 →
          w.get ⟨(k.1 + 2) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t2)) ∧
    -- Part (b): explicit w_2 and w_3
    (zoneWord 2 = (List.replicate 7 [.t1, .t1, .t2]).flatten) ∧
    (zoneWord 3 = (List.replicate 7 [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]).flatten) ∧
    -- Part (c): σ² block decomposition and no two S-D-S arcs are adjacent (for m ≥ 4)
    (∀ m : ℕ, 4 ≤ m →
      zoneWord m = (zoneWord (m - 2)).flatMap (fun t =>
        if t = .t1 then [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]
        else [.t1, .t1, .t2, .t1, .t2])) ∧
    (∀ m : ℕ, 4 ≤ m →
      let w := zoneWord m
      ∀ (k : Fin w.length),
        let idx (i : ℕ) : Fin w.length := ⟨i % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
        w.get (idx (k.1 + w.length - 1)) = .t2 →
        w.get k = .t1 →
        w.get (idx (k.1 + 1)) = .t2 →
        w.get (idx (k.1 + 2)) = .t1 →
        w.get (idx (k.1 + 3)) = .t1 →
        w.get (idx (k.1 + 4)) = .t2 →
        w.get (idx (k.1 + 5)) = .t1 →
        w.get (idx (k.1 + 6)) = .t2 →
        w.get (idx (k.1 + 7)) = .t1 ∧
        w.get (idx (k.1 + 8)) = .t1 ∧
        w.get (idx (k.1 + 9)) = .t2 ∧
        w.get (idx (k.1 + 10)) = .t1 ∧
        w.get (idx (k.1 + 11)) = .t1 ∧
        w.get (idx (k.1 + 12)) = .t2 ∧
        w.get (idx (k.1 + 13)) = .t1 ∧
        w.get (idx (k.1 + 14)) = .t2) :=
  FejesTothP7.Proofs.lem_5_1_zone_substitution c₀

/-- **Theorem 1.1 named step (Zone `Z₁`)**: `U₁ = Z₁` is finite and good. -/
theorem thm_1_1_step_zone1 (c₀ : sites37) :
    ∃ u1 : Finset H2, (u1 : Set H2) = ZoneUnion c₀ 1 ∧ IsGood c₀.1 u1 :=
  FejesTothP7.Proofs.thm_1_1_step_zone1 c₀

/-- **Theorem 1.1 named step (Zone `Z₂`)**: Given `U₁` good, `U₂` is finite and good. -/
theorem thm_1_1_step_zone2 (c₀ : sites37) :
    ∃ u2 : Finset H2, (u2 : Set H2) = ZoneUnion c₀ 2 ∧ IsGood c₀.1 u2 :=
  FejesTothP7.Proofs.thm_1_1_step_zone2 c₀

/-- **Theorem 1.1 named step (Zone `Z_m`, `m ≥ 1`)**: For every `m ≥ 1`, `U_m` is finite and good. -/
theorem thm_1_1_step_zone_m (c₀ : sites37) (m : ℕ) (hm : 1 ≤ m) :
    ∃ um : Finset H2, (um : Set H2) = ZoneUnion c₀ m ∧ IsGood c₀.1 um :=
  FejesTothP7.Proofs.thm_1_1_step_zone_m c₀ m hm

/-- **Corollary 1.2 intermediate ordering**: `ρ* < r < R_c < h < 2r`. -/
theorem cor_1_2_step_order_chain :
    ρ7 < r7 ∧ r7 < Rc7 ∧ Rc7 < h7 ∧ h7 < 2 * r7 :=
  FejesTothP7.Proofs.cor_1_2_step_order_chain

end FejesTothP7.Paper
