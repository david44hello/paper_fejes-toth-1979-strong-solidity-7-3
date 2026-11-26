/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.TilingMain
import FejesTothP7.Proofs.ExactIdentity
import FejesTothP7.Proofs.LocalGeom

/-!
# Grade of Saturatedness `g₇ = 3`, Order of Solidity `k₇ = 1`, and §1 Equivalence

Proves:
1. `hasGradeAtLeast_three`: every point `P ∉ sites37` overlaps at least 3 sites of `sites37`.
2. `circumcenter_overlaps_only_three`: the circumcenter `O = polarOrigin Rc7 (α7 / 2)` of
   `△(origin, polarOrigin (2*r7) 0, polarOrigin (2*r7) α7)` overlaps ONLY those 3 sites,
   yielding `HasGradeOfSaturatedness r7 sites37 3`.
3. `not_isSolidOfOrder_ge_two`: for every `m ≥ 2`, `¬ IsSolidOfOrder r7 sites37 m` (via moving
   `origin` to `O` in an `m`-truncation removing `n₀, n₁` and `m - 2` other sites, ruled out by
   cofinite rigidity `isometry_preserves_sites37_of_cofinite`).
4. `text_1_strong_solidity_iff_order_one`: `IsStronglySolid r7 sites37 ↔ IsSolidOfOrder r7 sites37 1`,
   and `isStronglySolid_of_oneVacancy_solid`: if `IsSolid r7 (sites37 \ {c₀})` for every `c₀ ∈ sites37`,
   then `IsStronglySolid r7 sites37`.
-/

noncomputable section
open Classical

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Section 1: Lower bound `g₇ ≥ 3` -/

theorem hasGradeAtLeast_three : HasGradeAtLeast r7 sites37 3 := by
  intro P hP
  rcases covering_radius_Rc7_sector P with ⟨v, hv, F, ρ, θ, hρ0, hρRc, hθ0, hθhalf, rfl⟩
  have hρ_pos : 0 < ρ := by
    by_contra hle
    push Not at hle
    have hρeq : ρ = 0 := le_antisymm hle hρ0
    have hPv : F.polar ρ θ = v := by
      rw [hρeq, SiteFrame.polar, polarOrigin_zero, F.origin_eq]
    rw [hPv] at hP; exact hP hv
  have hρ_lt : ρ < 2 * r7 := by
    have hord := eq_2_order
    linarith
  let n0 : H2 := F.nbr 0
  let n1 : H2 := F.nbr 1
  have hn0_mem : n0 ∈ sites37 := by simpa [n0, SiteFrame.nbr] using F.nbr_mem 0
  have hn1_mem : n1 ∈ sites37 := by simpa [n1, SiteFrame.nbr] using F.nbr_mem 1
  have hne_0 : v ≠ n0 := by
    intro h
    have hd : dist v n0 = 2 * r7 := by
      rw [← F.origin_eq]; change dist (F.φ origin) (F.φ (polarOrigin (2 * r7) _)) = _
      rw [F.φ.dist_eq, H2.dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
    rw [h, dist_self] at hd; linarith [r7_pos]
  have hne_1 : v ≠ n1 := by
    intro h
    have hd : dist v n1 = 2 * r7 := by
      rw [← F.origin_eq]; change dist (F.φ origin) (F.φ (polarOrigin (2 * r7) _)) = _
      rw [F.φ.dist_eq, H2.dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
    rw [h, dist_self] at hd; linarith [r7_pos]
  have hne_01 : n0 ≠ n1 := by
    intro h
    have hd : dist n0 n1 = 2 * r7 := by
      change dist (F.φ (polarOrigin (2 * r7) (((0 : ℤ) : ℝ) * α7)))
        (F.φ (polarOrigin (2 * r7) (((1 : ℤ) : ℝ) * α7))) = 2 * r7
      rw [F.φ.dist_eq]
      simpa using dist_polarOrigin_adj 0
    rw [h, dist_self] at hd; linarith [r7_pos]
  refine ⟨({v, n0, n1} : Finset H2), ?_, ?_, ?_⟩
  · intro q hq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact hv
    · exact hn0_mem
    · exact hn1_mem
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne_01]
    · simp [hne_0, hne_1]
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
    have hα_lt : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
    rcases hq with hqv | hqn0 | hqn1
    · rw [hqv]
      have hd : dist (F.polar ρ θ) v = ρ := by
        have h1 : dist (F.polar ρ θ) v = dist (F.φ (polarOrigin ρ θ)) (F.φ origin) := by
          rw [F.origin_eq]; rfl
        rw [h1, F.φ.dist_eq, H2.dist_polarOrigin_origin ρ θ hρ0]
      rw [hd]; exact hρ_lt
    · rw [hqn0]
      apply dist_lt_two_r7_iff_lorentz_lt.mpr
      change lorentz (F.φ (polarOrigin ρ θ)) (F.φ (polarOrigin (2 * r7) (((0 : ℤ) : ℝ) * α7))) < Real.cosh (2 * r7)
      rw [isometry_lorentz]; simp only [Int.cast_zero, zero_mul]
      have hcos : Real.cos α7 ≤ Real.cos θ :=
        Real.strictAntiOn_cos.antitoneOn ⟨hθ0, by linarith⟩ ⟨hα_pos.le, hα_lt.le⟩ (by linarith)
      exact (lorentz_polarOrigin_le_cosh_two_r7 hρ_pos hρ_lt.le hcos).2 (Or.inl hρ_lt)
    · rw [hqn1]
      apply dist_lt_two_r7_iff_lorentz_lt.mpr
      change lorentz (F.φ (polarOrigin ρ θ)) (F.φ (polarOrigin (2 * r7) (((1 : ℤ) : ℝ) * α7))) < Real.cosh (2 * r7)
      rw [isometry_lorentz]; simp only [Int.cast_one, one_mul]
      have hrot : lorentz (polarOrigin ρ θ) (polarOrigin (2 * r7) α7) =
          lorentz (polarOrigin ρ (α7 - θ)) (polarOrigin (2 * r7) 0) := by
        rw [H2.lorentz_polarOrigin, H2.lorentz_polarOrigin, sub_zero]
        rw [show θ - α7 = -(α7 - θ) by ring, Real.cos_neg]
      rw [hrot]
      have hcos : Real.cos α7 ≤ Real.cos (α7 - θ) :=
        Real.strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩ ⟨hα_pos.le, hα_lt.le⟩ (by linarith)
      exact (lorentz_polarOrigin_le_cosh_two_r7 hρ_pos hρ_lt.le hcos).2 (Or.inl hρ_lt)

/-! ### Section 2: Sharp inequality `Rc7 < 2 * ρ7` and circumcenter overlap classification -/

/-- Exact bound `1.801 < λ₇ < 1.803` from the minimal cubic `λ₇³ - λ₇² - 2λ₇ + 1 = 0`. -/
lemma lambda7_tight_bounds : (1.801 : ℝ) < lambdaP 7 ∧ lambdaP 7 < (1.803 : ℝ) := by
  have hcub := lambda7_cubic
  have hsq := lambdaP_sq_bounds (p := 7) (by omega)
  have hlo0 : (1.7 : ℝ) < lambdaP 7 := by
    have h1 := (lambdaP_bounds (p := 7) (by omega)).1
    have h2 : (1.7 : ℝ) < Real.sqrt 3 := by
      rw [show (1.7 : ℝ) = Real.sqrt (1.7 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hhi0 : lambdaP 7 < 2 := (lambdaP_bounds (p := 7) (by omega)).2
  constructor
  · by_contra hle; push Not at hle
    -- On [1.7, 1.801], p(x) = x^3 - x^2 - 2x + 1 is strictly increasing and p(1.801) < 0!
    have hdiff : (1.801 : ℝ) ^ 3 - (1.801 : ℝ) ^ 2 - 2 * (1.801 : ℝ) + 1 -
        (lambdaP 7 ^ 3 - lambdaP 7 ^ 2 - 2 * lambdaP 7 + 1) =
        ((1.801 : ℝ) - lambdaP 7) *
          ((1.801 : ℝ) ^ 2 + (1.801 : ℝ) * lambdaP 7 + lambdaP 7 ^ 2 - (1.801 : ℝ) - lambdaP 7 - 2) := by
      ring
    have hfac_pos : 0 < (1.801 : ℝ) ^ 2 + (1.801 : ℝ) * lambdaP 7 + lambdaP 7 ^ 2 - (1.801 : ℝ) - lambdaP 7 - 2 := by
      nlinarith
    have hneg : (1.801 : ℝ) ^ 3 - (1.801 : ℝ) ^ 2 - 2 * (1.801 : ℝ) + 1 < 0 := by norm_num
    nlinarith
  · by_contra hge; push Not at hge
    have hdiff : (lambdaP 7 ^ 3 - lambdaP 7 ^ 2 - 2 * lambdaP 7 + 1) -
        ((1.803 : ℝ) ^ 3 - (1.803 : ℝ) ^ 2 - 2 * (1.803 : ℝ) + 1) =
        (lambdaP 7 - (1.803 : ℝ)) *
          (lambdaP 7 ^ 2 + (1.803 : ℝ) * lambdaP 7 + (1.803 : ℝ) ^ 2 - lambdaP 7 - (1.803 : ℝ) - 2) := by
      ring
    have hfac_pos : 0 < lambdaP 7 ^ 2 + (1.803 : ℝ) * lambdaP 7 + (1.803 : ℝ) ^ 2 - lambdaP 7 - (1.803 : ℝ) - 2 := by
      nlinarith
    have hpos : (0 : ℝ) < (1.803 : ℝ) ^ 3 - (1.803 : ℝ) ^ 2 - 2 * (1.803 : ℝ) + 1 := by norm_num
    nlinarith

/-- Sharp metric inequality `Rc7 < 2 * ρ7` (equivalently `2 * h7 - Rc7 > 2 * r7`). -/
lemma Rc7_lt_two_mul_rho7 : Rc7 < 2 * ρ7 := by
  set L := lambdaP 7
  have hcub : L ^ 3 - L ^ 2 - 2 * L + 1 = 0 := lambda7_cubic
  have hLlo : (1.801 : ℝ) < L := lambda7_tight_bounds.1
  have hLhi : L < (1.803 : ℝ) := lambda7_tight_bounds.2
  have h4m : 0 < 4 - L ^ 2 := by nlinarith
  have h3m : 0 < L ^ 2 - 3 := by nlinarith
  -- Step 1: cosh ρ7 = (L - 1) / (4 - L^2)
  have hch_rho : Real.cosh ρ7 = (L - 1) / (4 - L ^ 2) := by
    have hhr : ρ7 = hP 7 - rP 7 := by
      have h := prop_3_1_exact_identity; unfold h7 r7 at h; linarith
    rw [hhr, Real.cosh_sub, cosh_hP_lambda (by omega), cosh_rP_lambda (by omega),
      sinh_hP_lambda (by omega), sinh_rP_lambda (by omega)]
    change ((L ^ 2 - 2) / Real.sqrt (4 - L ^ 2)) * (1 / Real.sqrt (4 - L ^ 2)) -
      (L * Real.sqrt (L ^ 2 - 3) / Real.sqrt (4 - L ^ 2)) *
        (Real.sqrt (L ^ 2 - 3) / Real.sqrt (4 - L ^ 2)) = (L - 1) / (4 - L ^ 2)
    have hrt_ne : Real.sqrt (4 - L ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h4m).ne'
    have hsq1 : Real.sqrt (4 - L ^ 2) ^ 2 = 4 - L ^ 2 := Real.sq_sqrt h4m.le
    have hsq2 : Real.sqrt (L ^ 2 - 3) ^ 2 = L ^ 2 - 3 := Real.sq_sqrt h3m.le
    rw [div_mul_div_comm, div_mul_div_comm, ← sq, ← sub_div, hsq1]
    have hnum : (L ^ 2 - 2) * 1 - L * Real.sqrt (L ^ 2 - 3) * Real.sqrt (L ^ 2 - 3) = L - 1 := by
      have hmul : Real.sqrt (L ^ 2 - 3) * Real.sqrt (L ^ 2 - 3) = L ^ 2 - 3 := Real.mul_self_sqrt h3m.le
      linear_combination -L * hmul - hcub
    rw [hnum]
  -- Step 2: cosh Rc7 ^ 2 = L^2 / (3 * (4 - L^2))
  have hch_Rc_sq : Real.cosh Rc7 ^ 2 = L ^ 2 / (3 * (4 - L ^ 2)) := by
    have hsh_Rc : Real.sinh Rc7 = Real.sinh r7 / Real.sin (Real.pi / 3) := by
      unfold Rc7; exact Real.sinh_arsinh _
    have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    have hsh_r_sq : Real.sinh r7 ^ 2 = (L ^ 2 - 3) / (4 - L ^ 2) := by
      change Real.sinh (rP 7) ^ 2 = _
      rw [sinh_rP_lambda (by omega), div_pow, Real.sq_sqrt h3m.le, Real.sq_sqrt h4m.le]
    have hch1 := Real.cosh_sq_sub_sinh_sq Rc7
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsh_Rc_sq : Real.sinh Rc7 ^ 2 = (4 / 3) * ((L ^ 2 - 3) / (4 - L ^ 2)) := by
      rw [hsh_Rc, hsin3, div_pow, div_pow, hsq3, hsh_r_sq]; ring
    have hsum : 1 + (4 / 3) * ((L ^ 2 - 3) / (4 - L ^ 2)) = L ^ 2 / (3 * (4 - L ^ 2)) := by
      field_simp [h4m.ne']; ring
    linarith
  -- Step 3: cosh Rc7 < cosh (2 * ρ7) by numerical bounds on L ∈ (1.801, 1.803)!
  have hch_rho_gt : (1.058 : ℝ) < Real.cosh ρ7 := by
    rw [hch_rho, lt_div_iff₀ h4m]; nlinarith
  have hch_2rho_gt : (1.238 : ℝ) < Real.cosh (2 * ρ7) := by
    rw [cosh_two_mul']; nlinarith
  have hch_Rc_sq_lt : Real.cosh Rc7 ^ 2 < (1.238 : ℝ) ^ 2 := by
    rw [hch_Rc_sq, div_lt_iff₀ (by linarith)]; nlinarith
  have hch_lt : Real.cosh Rc7 < Real.cosh (2 * ρ7) := by
    nlinarith [Real.cosh_pos Rc7, Real.cosh_pos (2 * ρ7)]
  have hRc_pos : 0 < Rc7 := lt_trans r7_pos eq_2_order.1
  have hρ_pos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
  have habs := Real.cosh_lt_cosh.mp hch_lt
  rw [abs_of_pos hRc_pos, abs_of_pos (by linarith)] at habs
  exact habs

/-- Circumcenter `O = polarOrigin Rc7 (α7 / 2)` of the equilateral triangle `(origin, n₀, n₁)`. -/
def triCircumcenter : H2 := polarOrigin Rc7 (α7 / 2)

lemma triCircumcenter_dist_origin : dist triCircumcenter origin = Rc7 := by
  unfold triCircumcenter
  exact H2.dist_polarOrigin_origin Rc7 _ (lt_trans r7_pos eq_2_order.1).le

lemma triCircumcenter_dist_n0 : dist triCircumcenter (polarOrigin (2 * r7) 0) = Rc7 := by
  have hRc_nn : 0 ≤ Rc7 := (lt_trans r7_pos eq_2_order.1).le
  rw [dist_eq_arcosh, ← Real.arcosh_cosh hRc_nn]
  congr 1
  unfold triCircumcenter
  rw [H2.lorentz_polarOrigin, sub_zero]
  have hch_Rc : Real.cosh Rc7 ≠ 0 := (Real.cosh_pos Rc7).ne'
  have hch_r : Real.cosh r7 ≠ 0 := (Real.cosh_pos r7).ne'
  have ht := tanh_Rc7_mul_cos_half_alpha7
  have hprod : Real.sinh Rc7 * Real.cos (α7 / 2) = Real.cosh Rc7 * (Real.sinh r7 / Real.cosh r7) := by
    have := congrArg (· * Real.cosh Rc7) ht
    field_simp [hch_Rc] at this ⊢
    linarith
  have hsh2 : Real.sinh (2 * r7) = 2 * Real.sinh r7 * Real.cosh r7 := Real.sinh_two_mul r7
  have hch2 : Real.cosh (2 * r7) = 2 * Real.cosh r7 ^ 2 - 1 := cosh_two_r7_eq
  have hcs := Real.cosh_sq_sub_sinh_sq r7
  calc Real.cosh Rc7 * Real.cosh (2 * r7) - Real.sinh Rc7 * Real.sinh (2 * r7) * Real.cos (α7 / 2)
      = Real.cosh Rc7 * Real.cosh (2 * r7) - (Real.sinh Rc7 * Real.cos (α7 / 2)) * Real.sinh (2 * r7) := by ring
    _ = Real.cosh Rc7 * (2 * Real.cosh r7 ^ 2 - 1) -
          (Real.cosh Rc7 * (Real.sinh r7 / Real.cosh r7)) * (2 * Real.sinh r7 * Real.cosh r7) := by
        rw [hprod, hsh2, hch2]
    _ = Real.cosh Rc7 * (2 * (Real.cosh r7 ^ 2 - Real.sinh r7 ^ 2) - 1) := by field_simp [hch_r]; ring
    _ = Real.cosh Rc7 := by rw [hcs]; ring

lemma triCircumcenter_dist_n1 : dist triCircumcenter (polarOrigin (2 * r7) α7) = Rc7 := by
  have hRc_nn : 0 ≤ Rc7 := (lt_trans r7_pos eq_2_order.1).le
  rw [dist_eq_arcosh, ← Real.arcosh_cosh hRc_nn]
  congr 1
  have hl : lorentz triCircumcenter (polarOrigin (2 * r7) α7) =
      lorentz triCircumcenter (polarOrigin (2 * r7) 0) := by
    unfold triCircumcenter
    rw [H2.lorentz_polarOrigin, H2.lorentz_polarOrigin, sub_zero]
    rw [show α7 / 2 - α7 = -(α7 / 2) by ring, Real.cos_neg]
  rw [hl, ← cosh_dist, triCircumcenter_dist_n0]

lemma triCircumcenter_not_mem_sites37 : triCircumcenter ∉ sites37 := by
  intro hmem
  have hRc_pos : 0 < Rc7 := lt_trans r7_pos eq_2_order.1
  have hne : triCircumcenter ≠ origin := by
    intro h; have := triCircumcenter_dist_origin; rw [h, dist_self] at this; linarith
  have hge := isPacking_sites37 triCircumcenter hmem origin origin_mem_sites37 hne
  rw [triCircumcenter_dist_origin] at hge
  linarith [eq_2_order.2.1, eq_2_order.2.2]

/-- `triCircumcenter` lies inside `ClosedPoly 1` as a positive conical combination of `origin, n₀, n₁`! -/
lemma triCircumcenter_mem_closedPoly_one : triCircumcenter ∈ ClosedPoly 1 (by omega) := by
  set n0 := polarOrigin (2 * r7) 0
  set n1 := polarOrigin (2 * r7) α7
  have hsh2_pos : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hcos_pos : 0 < Real.cos (α7 / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by unfold α7 alphaP; linarith [Real.pi_pos],
      by unfold α7 alphaP; linarith [Real.pi_pos]⟩
  have hRc_pos : 0 < Rc7 := lt_trans r7_pos eq_2_order.1
  have hshRc_pos : 0 < Real.sinh Rc7 := Real.sinh_pos_iff.mpr hRc_pos
  set A : ℝ := Real.sinh Rc7 / (2 * Real.sinh (2 * r7) * Real.cos (α7 / 2))
  set B : ℝ := Real.cosh Rc7 - 2 * A * Real.cosh (2 * r7)
  have hA_pos : 0 < A := div_pos hshRc_pos (by positivity)
  have hB_pos : 0 < B := by
    have hch_r : Real.cosh r7 ≠ 0 := (Real.cosh_pos r7).ne'
    have hch_Rc : Real.cosh Rc7 ≠ 0 := (Real.cosh_pos Rc7).ne'
    have hsh_r : Real.sinh r7 ≠ 0 := (Real.sinh_pos_iff.mpr r7_pos).ne'
    have ht := tanh_Rc7_mul_cos_half_alpha7
    have hshRc_eq : Real.sinh Rc7 = Real.cosh Rc7 * (Real.sinh r7 / Real.cosh r7) / Real.cos (α7 / 2) := by
      rw [eq_div_iff hcos_pos.ne']
      have := congrArg (· * Real.cosh Rc7) ht
      field_simp [hch_Rc] at this ⊢; linarith
    have hA_simp : 2 * A * Real.cosh (2 * r7) =
        Real.cosh Rc7 * (Real.cosh (2 * r7) / (2 * Real.cosh r7 ^ 2 * Real.cos (α7 / 2) ^ 2)) := by
      simp only [A]
      rw [hshRc_eq, Real.sinh_two_mul r7]
      field_simp [hch_r, hsh_r, hcos_pos.ne']
    have hdenom : 2 * Real.cosh r7 ^ 2 * Real.cos (α7 / 2) ^ 2 = Real.cosh (2 * r7) + 1 / 2 := by
      have hhalf : α7 / 2 = Real.pi / 7 := by unfold α7 alphaP; ring
      rw [hhalf]
      have hsin_sq : Real.cosh r7 ^ 2 * Real.sin (Real.pi / 7) ^ 2 = 1 / 4 := by
        rw [cosh_r7, div_pow]
        have hs : Real.sin (Real.pi / 7) ≠ 0 :=
          (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
        field_simp [hs]; ring
      have hcs := Real.cos_sq_add_sin_sq (Real.pi / 7)
      rw [cosh_two_r7_eq]
      nlinarith
    have hfrac_lt : Real.cosh (2 * r7) / (2 * Real.cosh r7 ^ 2 * Real.cos (α7 / 2) ^ 2) < 1 := by
      rw [hdenom, div_lt_one (by linarith [Real.cosh_pos (2 * r7)])]; linarith
    simp only [B]; rw [hA_simp]
    nlinarith [Real.cosh_pos Rc7]
  have hx_eq : triCircumcenter.x = B * origin.x + A * n0.x + A * n1.x := by
    have hcos_dbl : 1 + Real.cos α7 = 2 * Real.cos (α7 / 2) ^ 2 := by
      have h := Real.cos_two_mul (α7 / 2)
      rw [show 2 * (α7 / 2) = α7 by ring] at h; linarith
    simp only [triCircumcenter, origin, n0, n1, polarOrigin, Real.cos_zero, mul_one, mul_zero, zero_add, A]
    have h1 : Real.sinh (2 * r7) + Real.sinh (2 * r7) * Real.cos α7 =
        Real.sinh (2 * r7) * (1 + Real.cos α7) := by ring
    field_simp [hsh2_pos.ne', hcos_pos.ne']
    nlinarith
  have hy_eq : triCircumcenter.y = B * origin.y + A * n0.y + A * n1.y := by
    have hsin_dbl : Real.sin α7 = 2 * Real.sin (α7 / 2) * Real.cos (α7 / 2) := by
      have h := Real.sin_two_mul (α7 / 2)
      rw [show 2 * (α7 / 2) = α7 by ring] at h; exact h
    simp only [triCircumcenter, origin, n0, n1, polarOrigin, Real.sin_zero, mul_zero, zero_add, add_zero, A]
    field_simp [hsh2_pos.ne', hcos_pos.ne']
    nlinarith
  have hz_eq : triCircumcenter.z = B * origin.z + A * n0.z + A * n1.z := by
    simp only [triCircumcenter, origin, n0, n1, polarOrigin, mul_one, B]; ring
  have ho_mem : origin ∈ ClosedPoly 1 (by omega) := fun k => ((zoneConvexInv 1 (by omega)).origin_open k).le
  have hn0_mem : n0 ∈ ClosedPoly 1 (by omega) := by
    have hv := zoneLayer1_layerVert 0; simp only [Nat.cast_zero, zero_mul] at hv
    change polarOrigin (2 * r7) 0 ∈ ClosedPoly 1 (by omega)
    rw [← hv]; exact layerVert_mem_closedPoly (zoneConvexInv 1 (by omega)) 0
  have hn1_mem : n1 ∈ ClosedPoly 1 (by omega) := by
    have hv := zoneLayer1_layerVert 1; simp only [Nat.cast_one, one_mul] at hv
    change polarOrigin (2 * r7) α7 ∈ ClosedPoly 1 (by omega)
    rw [← hv]; exact layerVert_mem_closedPoly (zoneConvexInv 1 (by omega)) 1
  intro k
  have hlin : ∀ a b : H2, detH a b triCircumcenter =
      B * detH a b origin + A * detH a b n0 + A * detH a b n1 := by
    intro a b; unfold detH; rw [hx_eq, hy_eq, hz_eq]; ring
  rw [hlin]
  nlinarith [ho_mem k, hn0_mem k, hn1_mem k]

lemma zoneLayer_one_length : (zoneLayer 1).length = 7 := zoneLayer1_length

/-- Altitude identity: in `zoneLayer 1`, the type-2 child of edge `(n₀, n₁)` lies at distance `2 * h7` from `origin`! -/
lemma dist_origin_type2_edge0 :
    let F0 := ((zoneLayer 1).get ⟨0, by rw [zoneLayer_one_length]; omega⟩).2
    dist origin (F0 (polarOrigin (2 * r7) ((6 : ℤ) * α7))) = 2 * h7 := by
  intro F0
  set G : H2 ≃ᵢ H2 := (boostX r7).trans F0
  have hG_w : G (polarOrigin h7 (-(Real.pi / 2))) = F0 (polarOrigin (2 * r7) ((6 : ℤ) * α7)) := by
    simp only [G, IsometryEquiv.trans_apply, boostX_r7_altitude]
    congr 1
    have h6 : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
    rw [h6, polarOrigin_add_two_pi]
  have hboost_pos : boostX r7 (polarOrigin h7 (Real.pi / 2)) = polarOrigin (2 * r7) α7 := by
    have hneg := boostX_r7_altitude
    have hrx : reflXAxis (boostX r7 (polarOrigin h7 (-(Real.pi / 2)))) =
        reflXAxis (polarOrigin (2 * r7) (-α7)) := congrArg reflXAxis hneg
    have hcomm : ∀ p : H2, reflXAxis (boostX r7 p) = boostX r7 (reflXAxis p) :=
      fun _ => H2.ext rfl rfl rfl
    rw [hcomm, reflXAxis_apply_polarOrigin, reflXAxis_apply_polarOrigin, neg_neg, neg_neg] at hrx
    exact hrx
  have hF0_a : F0 (polarOrigin (2 * r7) α7) = origin := by
    have h := (zoneLayer_inner_nbrs (m := 1) (by omega) ⟨0, by rw [zoneLayer_one_length]; omega⟩).1
    simpa [F0] using h
  have hG_o : G (polarOrigin h7 (Real.pi / 2)) = origin := by
    simp only [G, IsometryEquiv.trans_apply, hboost_pos, hF0_a]
  rw [← hG_o, ← hG_w, G.dist_eq, dist_eq_arcosh, H2.lorentz_polarOrigin]
  have hcos : Real.cos (Real.pi / 2 - -(Real.pi / 2)) = -1 := by
    rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring, Real.cos_pi]
  rw [hcos]
  have h2h : Real.cosh h7 * Real.cosh h7 - Real.sinh h7 * Real.sinh h7 * -1 = Real.cosh (2 * h7) := by
    have h1 := Real.cosh_sq_sub_sinh_sq h7
    rw [cosh_two_mul']; nlinarith
  rw [h2h, Real.arcosh_cosh (by linarith [h7_pos])]

/-- **Circumcenter Overlap Classification**: `triCircumcenter` overlaps ONLY `{origin, n₀, n₁}` among all of `sites37`! -/
theorem triCircumcenter_dist_gt_of_not_tri {w : H2} (hw : w ∈ sites37)
    (h0 : w ≠ origin) (h1 : w ≠ polarOrigin (2 * r7) 0) (h2 : w ≠ polarOrigin (2 * r7) α7) :
    2 * r7 < dist triCircumcenter w := by
  -- Prove by induction on m ≥ 1 that every w ∈ zoneVerts m outside {n₀, n₁} has dist O w > 2 * r7!
  have hlayer : ∀ m : ℕ, 1 ≤ m → ∀ v ∈ zoneVerts m,
      v ≠ polarOrigin (2 * r7) 0 → v ≠ polarOrigin (2 * r7) α7 → 2 * r7 < dist triCircumcenter v := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro v hv hv0 hv1
      simp only [zoneVerts, List.mem_map] at hv
      rcases hv with ⟨e, heL, rfl⟩
      rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
      rw [zoneLayer1_get_origin i] at hv0 hv1 ⊢
      have hi7 : i.1 < 7 := lt_of_lt_of_eq i.2 zoneLayer1_length
      have hi_ne0 : i.1 ≠ 0 := fun h => hv0 (by rw [h]; simp)
      have hi_ne1 : i.1 ≠ 1 := fun h => hv1 (by rw [h]; simp)
      have hi_ge2 : 2 ≤ i.1 := by omega
      -- Angle diff between α7/2 and i*α7 is ≥ 3*α7/2 = β7 ρ7 > β7 Rc7!
      have hRc_pos : 0 < Rc7 := lt_trans r7_pos eq_2_order.1
      have hRc_le : Rc7 ≤ 2 * r7 := by linarith [eq_2_order.2.1, eq_2_order.2.2]
      have hβ_lt : β7 Rc7 < 3 * α7 / 2 := by
        have hord := cor_1_2_step_order_chain
        have hanti := text_2_beta_properties.2.2.1
        have hρ_mem : ρ7 ∈ Set.Ioc 0 (2 * r7) :=
          ⟨text_2_beta_properties.2.2.2.2.2.2.1, text_2_beta_properties.2.2.2.2.2.2.2.1.le⟩
        have hRc_mem : Rc7 ∈ Set.Ioc 0 (2 * r7) := ⟨hRc_pos, hRc_le⟩
        have h1 := hanti hρ_mem hRc_mem (lt_trans hord.1 hord.2.1)
        rw [text_2_beta_properties.2.2.2.2.2.2.2.2] at h1
        exact h1
      have hangle_ge : 3 * α7 / 2 ≤ Real.arccos (Real.cos (α7 / 2 - (i.1 : ℝ) * α7)) := by
        have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
        by_cases hi3 : i.1 ≤ 3
        · have hcos_eq : Real.cos (α7 / 2 - (i.1 : ℝ) * α7) = Real.cos (((i.1 : ℝ) - 1 / 2) * α7) := by
            rw [← Real.cos_neg]; congr 1; ring
          rw [hcos_eq, Real.arccos_cos (by
            have : (2 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast hi_ge2
            nlinarith) (by
            have : (i.1 : ℝ) ≤ 3 := by exact_mod_cast hi3
            unfold α7 alphaP; nlinarith [Real.pi_pos])]
          have : (2 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast hi_ge2
          nlinarith
        · have hi_ge4 : 4 ≤ i.1 := by omega
          have hcos_eq : Real.cos (α7 / 2 - (i.1 : ℝ) * α7) = Real.cos ((7 + 1 / 2 - (i.1 : ℝ)) * α7) := by
            rw [← Real.cos_add_two_pi]
            congr 1; unfold α7 alphaP; ring
          rw [hcos_eq, Real.arccos_cos (by
            have : (i.1 : ℝ) ≤ 6 := by exact_mod_cast (show i.1 ≤ 6 by omega)
            nlinarith) (by
            have : (4 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast hi_ge4
            unfold α7 alphaP; nlinarith [Real.pi_pos])]
          have : (i.1 : ℝ) ≤ 6 := by exact_mod_cast (show i.1 ≤ 6 by omega)
          nlinarith
      have hpol := lem_2_2_polar (IsometryEquiv.refl H2) Rc7 (α7 / 2) ((i.1 : ℝ) * α7) hRc_pos hRc_le
      have hnot_lt : ¬ dist triCircumcenter (polarOrigin (2 * r7) ((i.1 : ℝ) * α7)) < 2 * r7 := by
        intro hlt
        have := hpol.1.mp hlt; linarith
      have hnot_eq : dist triCircumcenter (polarOrigin (2 * r7) ((i.1 : ℝ) * α7)) ≠ 2 * r7 := by
        intro heq
        have := hpol.2.mp heq; linarith
      exact lt_of_le_of_ne (not_lt.mp hnot_lt) hnot_eq.symm
    | succ k hk ih =>
      intro v hv _ _
      have hsucc : zoneLayer (k + 1) = (zoneLayer k).flatMap nextLayerEntry := by
        cases k with | zero => omega | succ n => rfl
      simp only [zoneVerts, hsucc, List.mem_map, List.mem_flatMap] at hv
      rcases hv with ⟨e', ⟨e, heL, he'c⟩, rfl⟩
      rcases List.mem_iff_get.mp heL with ⟨idx, rfl⟩
      set hL := zoneLayer_length_pos k hk
      set hAdj := zoneLayer_cyclicAdj k hk
      set hDet := fun a ha => (zoneLayer_mem_Delta237_and_detH k a ha).2
      have hInv := zoneConvexInv k hk
      have hO_poly : triCircumcenter ∈ ClosedPoly k hk :=
        closedPoly_mono (by omega) hk triCircumcenter_mem_closedPoly_one
      have huk_mem : layerVert (zoneLayer k) hL idx.1 ∈ ClosedPoly k hk :=
        layerVert_mem_closedPoly hInv idx.1
      have hget_mod : (zoneLayer k).get ⟨idx.1 % (zoneLayer k).length, Nat.mod_lt _ hAdj.1⟩ =
          (zoneLayer k).get idx := by congr 1; ext; exact Nat.mod_eq_of_lt idx.2
      rcases hidx_eq : (zoneLayer k).get idx with ⟨t, F⟩
      rw [hidx_eq] at he'c
      have hu_eq : layerVert (zoneLayer k) hL idx.1 = F origin := by unfold layerVert; rw [hget_mod, hidx_eq]
      have htype1 : ∀ (a : ℤ), ((t = .t1 ∧ a = 4) ∨ a = 5) →
          2 * r7 < dist triCircumcenter (F (polarOrigin (2 * r7) ((a : ℝ) * α7))) := by
        intro a ha
        have hf := isFoot_type1_child hAdj hDet idx.1 huk_mem (j := a) (by
          rcases ha with ⟨ht, rfl⟩ | rfl
          · left; exact ⟨by rw [hget_mod, hidx_eq]; exact ht, rfl⟩
          · right; rfl)
        simp only [hget_mod, hidx_eq] at hf
        have hO_ne_u : triCircumcenter ≠ F origin := by
          intro heq
          have hu_s : F origin ∈ sites37 := by
            rw [← hu_eq, ← V_all_eq_sites37]
            exact mem_V_all_of_mem_zoneVerts hk (layerVert_mem_zoneVerts k hk idx.1)
          exact triCircumcenter_not_mem_sites37 (heq ▸ hu_s)
        have hlt := hf.2 triCircumcenter hO_poly (by rw [hu_eq]; exact hO_ne_u)
        have hl : lorentz (F (polarOrigin (2 * r7) ((a : ℝ) * α7))) (F origin) = Real.cosh (2 * r7) := by
          rw [isometry_lorentz, lorentz_symm, lorentz_origin_polarOrigin]
        rw [hu_eq, hl, lorentz_symm] at hlt
        rw [← cosh_dist] at hlt
        have habs := Real.cosh_lt_cosh.mp hlt
        rw [abs_of_pos (by linarith [r7_pos]), abs_of_nonneg dist_nonneg] at habs
        exact habs
      have htype2 : 2 * r7 < dist triCircumcenter (F (polarOrigin (2 * r7) ((6 : ℤ) * α7))) := by
        by_cases hspec : k = 1 ∧ idx.1 = 0
        · rcases hspec with ⟨rfl, hidx0⟩
          have hF_eq : F = ((zoneLayer 1).get ⟨0, by rw [zoneLayer_one_length]; omega⟩).2 := by
            have hfin : idx = ⟨0, by rw [zoneLayer_one_length]; omega⟩ := Fin.ext hidx0
            rw [hfin] at hidx_eq
            exact (congrArg Prod.snd hidx_eq).symm
          rw [hF_eq]
          have hd_ow := dist_origin_type2_edge0
          have htri := dist_triangle origin triCircumcenter
            (((zoneLayer 1).get ⟨0, by rw [zoneLayer_one_length]; omega⟩).2 (polarOrigin (2 * r7) ((6 : ℤ) * α7)))
          rw [dist_comm origin triCircumcenter, triCircumcenter_dist_origin] at htri
          have hgap := Rc7_lt_two_mul_rho7
          have hid := prop_3_1_exact_identity
          linarith
        · -- Not (k = 1 ∧ idx = 0): at least one endpoint of edge idx is outside {n₀, n₁}, so dist O u > 2*r7!
          set u := layerVert (zoneLayer k) hL idx.1
          set uNext := layerVert (zoneLayer k) hL (idx.1 + 1)
          set M := mid u uNext
          set w' := F (polarOrigin (2 * r7) ((6 : ℤ) * α7))
          have he_next : uNext = F (polarOrigin (2 * r7) 0) := by
            have ha := hAdj.2 ⟨idx.1 % (zoneLayer k).length, Nat.mod_lt _ hAdj.1⟩
            have h1 := adjFrame_origin_eq ha
            rw [hget_mod, hidx_eq] at h1
            simpa [uNext, layerVert, Nat.mod_add_mod] using h1
          have hend_gt : 2 * r7 < dist triCircumcenter u ∨ 2 * r7 < dist triCircumcenter uNext := by
            by_cases hk1 : k = 1
            · subst hk1
              have hidx_ne0 : idx.1 ≠ 0 := fun h => hspec ⟨rfl, h⟩
              have hi7 : idx.1 < 7 := lt_of_lt_of_eq idx.2 zoneLayer_one_length
              have hu_pol : u = polarOrigin (2 * r7) ((idx.1 : ℝ) * α7) := zoneLayer1_layerVert idx.1
              have hun_pol : uNext = polarOrigin (2 * r7) (((idx.1 + 1 : ℕ) : ℝ) * α7) :=
                zoneLayer1_layerVert (idx.1 + 1)
              have hne_z1 : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b →
                  polarOrigin (2 * r7) ((a : ℝ) * α7) ≠ polarOrigin (2 * r7) ((b : ℝ) * α7) := by
                intro a b ha7 hb7 hab hsame
                have hnd := zoneVerts_nodup 1
                rw [List.nodup_iff_injective_get] at hnd
                have heq_get : (zoneVerts 1).get ⟨a, by rw [zoneVerts_length, zoneLayer_one_length]; exact ha7⟩ =
                    (zoneVerts 1).get ⟨b, by rw [zoneVerts_length, zoneLayer_one_length]; exact hb7⟩ := by
                  simp only [zoneVerts, List.get_eq_getElem, List.getElem_map]
                  have ha := zoneLayer1_get_origin ⟨a, by rw [zoneLayer_one_length]; exact ha7⟩
                  have hb := zoneLayer1_get_origin ⟨b, by rw [zoneLayer_one_length]; exact hb7⟩
                  simpa [List.get_eq_getElem] using ha.trans (hsame.trans hb.symm)
                exact hab (congrArg Fin.val (hnd heq_get))
              by_cases hidx1 : idx.1 = 1
              · right
                apply ih uNext (layerVert_mem_zoneVerts 1 (by omega) (idx.1 + 1))
                · rw [hun_pol, hidx1]; simpa using hne_z1 2 0 (by omega) (by omega) (by omega)
                · rw [hun_pol, hidx1]
                  have h1 := hne_z1 2 1 (by omega) (by omega) (by omega)
                  simpa using h1
              · left
                apply ih u (layerVert_mem_zoneVerts 1 (by omega) idx.1)
                · rw [hu_pol]; simpa using hne_z1 idx.1 0 hi7 (by omega) hidx_ne0
                · rw [hu_pol]
                  have h1 := hne_z1 idx.1 1 hi7 (by omega) hidx1
                  simpa using h1
            · -- k ≥ 2: u ∈ zoneVerts k is disjoint from zoneVerts 1 (which contains n₀, n₁)!
              left
              have hn0_z1 : polarOrigin (2 * r7) 0 ∈ zoneVerts 1 := by
                have hv := zoneLayer1_layerVert 0; simp only [Nat.cast_zero, zero_mul] at hv
                rw [← hv]; exact layerVert_mem_zoneVerts 1 (by omega) 0
              have hn1_z1 : polarOrigin (2 * r7) α7 ∈ zoneVerts 1 := by
                have hv := zoneLayer1_layerVert 1; simp only [Nat.cast_one, one_mul] at hv
                rw [← hv]; exact layerVert_mem_zoneVerts 1 (by omega) 1
              apply ih u (layerVert_mem_zoneVerts k hk idx.1)
              · intro heq; exact zoneVerts_disjoint (by omega) hk (by omega) hn0_z1
                  (heq ▸ layerVert_mem_zoneVerts k hk idx.1)
              · intro heq; exact zoneVerts_disjoint (by omega) hk (by omega) hn1_z1
                  (heq ▸ layerVert_mem_zoneVerts k hk idx.1)
          have hd_uM : dist u M = r7 := by
            rw [dist_mid_left, hu_eq, he_next, F.dist_eq, H2.dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
            ring
          have hd_uNextM : dist uNext M = r7 := by
            rw [dist_comm, dist_mid_right, hu_eq, he_next, F.dist_eq,
              H2.dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
            ring
          have hd_MO : r7 < dist M triCircumcenter := by
            rcases hend_gt with hgt | hgt
            · have := dist_triangle triCircumcenter M u; rw [dist_comm u M] at hd_uM; rw [dist_comm M triCircumcenter]; linarith
            · have := dist_triangle triCircumcenter M uNext; rw [dist_comm uNext M] at hd_uNextM; rw [dist_comm M triCircumcenter]; linarith
          set G : H2 ≃ᵢ H2 := (boostX r7).trans F
          have hG_o : G origin = M := by
            simp only [G, IsometryEquiv.trans_apply, boostX_apply_origin]
            rw [show M = mid (F origin) (F (polarOrigin (2 * r7) 0)) by rw [← hu_eq, ← he_next], mid_frame_edge]
          have hG_u : G (polarOrigin (-r7) 0) = u := by
            simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, neg_add_cancel,
              polarOrigin_zero, hu_eq]
          have hG_uNext : G (polarOrigin r7 0) = uNext := by
            simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, ← two_mul, he_next]
          have hG_w : G (polarOrigin h7 (-(Real.pi / 2))) = w' := by
            simp only [G, IsometryEquiv.trans_apply, boostX_r7_altitude, w']
            congr 1
            have h6 : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
            rw [h6, polarOrigin_add_two_pi]
          have hG_det : ∀ a b c, detH (G a) (G b) (G c) = detH a b c := by
            intro a b c; simp only [G, IsometryEquiv.trans_apply]
            have hF_det : ∀ p q r, detH (F p) (F q) (F r) = detH p q r :=
              hDet (t, F) (by rw [← hidx_eq]; exact List.get_mem _ _)
            rw [hF_det, H2.detH_boostX]
          set O0 := G.symm triCircumcenter
          have hO_eq : triCircumcenter = G O0 := by simp [O0]
          have hO0_y : 0 ≤ O0.y := by
            have hyk : 0 ≤ detH u uNext triCircumcenter := hO_poly idx.1
            rw [← hG_u, ← hG_uNext, hO_eq, hG_det] at hyk
            have hdet : detH (polarOrigin (-r7) 0) (polarOrigin r7 0) O0 =
                2 * Real.sinh r7 * Real.cosh r7 * O0.y := by
              unfold detH polarOrigin
              simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, Real.sinh_neg, Real.cosh_neg]
              ring
            rw [hdet] at hyk
            have hpos : 0 < 2 * Real.sinh r7 * Real.cosh r7 :=
              mul_pos (mul_pos zero_lt_two (Real.sinh_pos_iff.mpr r7_pos)) (Real.cosh_pos r7)
            nlinarith
          have hO0_z_gt : Real.cosh r7 < O0.z := by
            have hl : lorentz M triCircumcenter = O0.z := by
              rw [← hG_o, hO_eq, isometry_lorentz]; unfold lorentz origin; ring
            rw [← hl, ← cosh_dist]
            exact Real.cosh_lt_cosh.mpr (by rw [abs_of_pos r7_pos, abs_of_nonneg dist_nonneg]; exact hd_MO)
          have hlor_gt : Real.cosh (2 * r7) < lorentz triCircumcenter w' := by
            rw [lorentz_symm, ← hG_w, hO_eq, isometry_lorentz]
            have hl : lorentz (polarOrigin h7 (-(Real.pi / 2))) O0 = Real.cosh h7 * O0.z + Real.sinh h7 * O0.y := by
              unfold lorentz polarOrigin
              simp only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]; ring
            rw [hl]
            have hch_prod : Real.cosh h7 * Real.cosh r7 = Real.cosh (2 * r7) := by
              rw [cosh_h7_eq, div_mul_cancel₀ _ (Real.cosh_pos r7).ne']
            have hsh_nn : 0 ≤ Real.sinh h7 * O0.y := mul_nonneg (Real.sinh_pos_iff.mpr h7_pos).le hO0_y
            nlinarith [Real.cosh_pos h7]
          rw [← cosh_dist] at hlor_gt
          have habs := Real.cosh_lt_cosh.mp hlor_gt
          rw [abs_of_pos (by linarith [r7_pos]), abs_of_nonneg dist_nonneg] at habs
          exact habs
      cases t with
      | t1 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
        rcases he'c with rfl | rfl | rfl
        · rw [stepFrame_origin_eq]; exact htype1 4 (Or.inl ⟨rfl, rfl⟩)
        · rw [stepFrame_origin_eq]; exact htype1 5 (Or.inr rfl)
        · rw [stepFrame_origin_eq]; exact htype2
      | t2 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
        rcases he'c with rfl | rfl
        · rw [stepFrame_origin_eq]; exact htype1 5 (Or.inr rfl)
        · rw [stepFrame_origin_eq]; exact htype2
  have hwV : w ∈ V_all := V_all_eq_sites37.symm ▸ hw
  rcases hwV with rfl | hwm
  · exact absurd rfl h0
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hwm
    rcases hwm with ⟨m, hm, hwm⟩
    exact hlayer m hm w hwm h1 h2

theorem hasGradeOfSaturatedness_three : HasGradeOfSaturatedness r7 sites37 3 := by
  refine ⟨hasGradeAtLeast_three, fun m hm => ?_⟩
  rcases hm triCircumcenter triCircumcenter_not_mem_sites37 with ⟨F, hFsub, hFcard, hFdist⟩
  have hsub3 : F ⊆ ({origin, polarOrigin (2 * r7) 0, polarOrigin (2 * r7) α7} : Finset H2) := by
    intro q hq
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    have hgt := triCircumcenter_dist_gt_of_not_tri (hFsub hq) hnot.1 hnot.2.1 hnot.2.2
    linarith [hFdist q hq]
  have hle : F.card ≤ ({origin, polarOrigin (2 * r7) 0, polarOrigin (2 * r7) α7} : Finset H2).card :=
    Finset.card_le_card hsub3
  have hcard3 : ({origin, polarOrigin (2 * r7) 0, polarOrigin (2 * r7) α7} : Finset H2).card ≤ 3 := by
    exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
  omega

/-! ### Section 3: Order of Solidity `k₇ ≤ 1` (all `m ≥ 2` at once!) & §1 Equivalence -/

/-- `sites37` is infinite (so we can pick `m - 2` extra sites outside any finite set). -/
lemma exists_finset_sites37_disjoint (B : Finset H2) (n : ℕ) :
    ∃ A : Finset H2, (A : Set H2) ⊆ sites37 ∧ Disjoint A B ∧ A.card = n := by
  induction n with
  | zero => exact ⟨∅, by simp, Finset.disjoint_empty_left _, rfl⟩
  | succ k ih =>
    rcases ih with ⟨A, hAsub, hAdisj, hAcard⟩
    rcases exists_adj_pair_outside_finset (A ∪ B) with ⟨u, hu, _, _, huNot, _, _⟩
    have huA : u ∉ A := fun h => huNot (Finset.mem_union_left B h)
    have huB : u ∉ B := fun h => huNot (Finset.mem_union_right A h)
    refine ⟨insert u A, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · exact hu
      · exact hAsub hxA
    · rw [Finset.disjoint_insert_left]; exact ⟨huB, hAdisj⟩
    · rw [Finset.card_insert_of_notMem huA, hAcard]

/-- **Upper bound on order of solidity**: `¬ IsSolidOfOrder r7 sites37 m` for ALL `m ≥ 2`! -/
theorem not_isSolidOfOrder_ge_two (m : ℕ) (hm : 2 ≤ m) : ¬ IsSolidOfOrder r7 sites37 m := by
  intro hord
  set n0 := polarOrigin (2 * r7) 0
  set n1 := polarOrigin (2 * r7) α7
  have hn0_s : n0 ∈ sites37 := by
    rw [← V_all_eq_sites37]
    have hv := zoneLayer1_layerVert 0; simp only [Nat.cast_zero, zero_mul] at hv
    change polarOrigin (2 * r7) 0 ∈ V_all
    rw [← hv]; exact mem_V_all_of_mem_zoneVerts (by omega) (layerVert_mem_zoneVerts 1 (by omega) 0)
  have hn1_s : n1 ∈ sites37 := by
    rw [← V_all_eq_sites37]
    have hv := zoneLayer1_layerVert 1; simp only [Nat.cast_one, one_mul] at hv
    change polarOrigin (2 * r7) α7 ∈ V_all
    rw [← hv]; exact mem_V_all_of_mem_zoneVerts (by omega) (layerVert_mem_zoneVerts 1 (by omega) 1)
  have hne_01 : n0 ≠ n1 := by
    intro h; have hd := dist_polarOrigin_adj 0; simp only [zero_add] at hd
    change dist n0 n1 = 2 * r7 at hd; rw [h, dist_self] at hd; linarith [r7_pos]
  rcases exists_finset_sites37_disjoint ({origin, n0, n1} : Finset H2) (m - 2) with ⟨A, hAsub, hAdisj, hAcard⟩
  let K : Finset H2 := insert n0 (insert n1 A)
  have hn0A : n0 ∉ A := fun h => Finset.disjoint_left.mp hAdisj h (by simp)
  have hn1A : n1 ∉ A := fun h => Finset.disjoint_left.mp hAdisj h (by simp)
  have hoA : origin ∉ A := fun h => Finset.disjoint_left.mp hAdisj h (by simp)
  have hne_o0 : origin ≠ n0 := by
    intro h; have hd : dist origin n0 = 2 * r7 := H2.dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])
    rw [← h, dist_self] at hd; linarith [r7_pos]
  have hne_o1 : origin ≠ n1 := by
    intro h; have hd : dist origin n1 = 2 * r7 := H2.dist_origin_polarOrigin (2 * r7) α7 (by linarith [r7_pos])
    rw [← h, dist_self] at hd; linarith [r7_pos]
  have hoK : origin ∉ K := by simp [K, hne_o0, hne_o1, hoA]
  have hK_sub : (K : Set H2) ⊆ sites37 := by
    intro x hx
    simp only [K, Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hxA
    · exact hn0_s
    · exact hn1_s
    · exact hAsub hxA
  have hK_card : K.card = m := by
    simp only [K]
    rw [Finset.card_insert_of_notMem (by simp [hne_01, hn0A]), Finset.card_insert_of_notMem hn1A, hAcard]
    omega
  set C' : Set H2 := sites37 \ (K : Set H2)
  have htrunc : IsKTruncation sites37 m C' := ⟨K, hK_sub, hK_card, rfl⟩
  have hrearr : IsRearrangement r7 C' {origin} {triCircumcenter} := by
    refine ⟨?_, by simp, ?_, ?_⟩
    · intro x hx; rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      rw [hx]; exact ⟨origin_mem_sites37, hoK⟩
    · simp only [Finset.coe_singleton, Set.disjoint_singleton_right]
      intro hmem; exact triCircumcenter_not_mem_sites37 hmem.1.1
    · intro x hx y hy hxy
      simp only [Set.mem_union, Set.mem_sdiff, Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      rcases hx with ⟨⟨hxs, hxK⟩, hxo⟩ | rfl <;> rcases hy with ⟨⟨hys, hyK⟩, hyo⟩ | rfl
      · exact isPacking_sites37 x hxs y hys hxy
      · rw [dist_comm]
        have hx0 : x ≠ n0 := fun h => hxK (by simp [K, h])
        have hx1 : x ≠ n1 := fun h => hxK (by simp [K, h])
        exact (triCircumcenter_dist_gt_of_not_tri hxs hxo hx0 hx1).le
      · have hy0 : y ≠ n0 := fun h => hyK (by simp [K, h])
        have hy1 : y ≠ n1 := fun h => hyK (by simp [K, h])
        exact (triCircumcenter_dist_gt_of_not_tri hys hyo hy0 hy1).le
      · exact absurd rfl hxy
  rcases hord.2 C' htrunc {origin} {triCircumcenter} hrearr with ⟨C'', ⟨K'', _, _, rfl⟩, ⟨φ, hφ⟩⟩
  have hsub : φ '' (sites37 \ (insert origin K : Finset H2)) ⊆ sites37 := by
    rintro y ⟨x, ⟨hxs, hxK⟩, rfl⟩
    have hmem : x ∈ (C' \ (↑({origin} : Finset H2) : Set H2)) ∪ (↑({triCircumcenter} : Finset H2) : Set H2) := by
      left
      refine ⟨⟨hxs, ?_⟩, ?_⟩
      · intro hxK'; exact hxK (by simp [hxK'])
      · intro hxo; rw [Finset.coe_singleton, Set.mem_singleton_iff] at hxo; exact hxK (by simp [hxo])
    have h1 : φ x ∈ sites37 \ (K'' : Set H2) := by rw [← hφ]; exact ⟨x, hmem, rfl⟩
    exact h1.1
  have hpres := isometry_preserves_sites37_of_cofinite (insert origin K) hsub
  have hφO : φ triCircumcenter ∈ sites37 := by
    have h1 : φ triCircumcenter ∈ sites37 \ (K'' : Set H2) := by
      rw [← hφ]; exact ⟨triCircumcenter, Or.inr (by simp), rfl⟩
    exact h1.1
  have hO_in : triCircumcenter ∈ sites37 := by
    rw [← hpres] at hφO
    rcases hφO with ⟨z, hz, heq⟩
    rwa [← φ.injective heq]
  exact triCircumcenter_not_mem_sites37 hO_in

/-- **Plain solidity from 1-vacancy solidity**: if `sites37 \ {c₀}` is solid for every `c₀ ∈ sites37`,
    then `sites37` itself is solid (and hence strongly solid)! -/
theorem isStronglySolid_of_oneVacancy_solid
    (h1 : ∀ c₀ ∈ sites37, IsSolid r7 (sites37 \ {c₀})) :
    IsStronglySolid r7 sites37 := by
  refine ⟨⟨isPacking_sites37, ?_⟩, h1⟩
  intro s X hX
  rcases exists_adj_pair_outside_finset (s ∪ X) with ⟨c₀, hc₀, _, _, hc0Not, _, _⟩
  have hc0s : c₀ ∉ s := fun h => hc0Not (Finset.mem_union_left X h)
  have hc0X : c₀ ∉ X := fun h => hc0Not (Finset.mem_union_right s h)
  have hrearr1 : IsRearrangement r7 (oneVacancy c₀) s X := by
    rcases hX with ⟨hs_sub, hcard, hdisj, hpack⟩
    refine ⟨?_, hcard, ?_, ?_⟩
    · intro x hx; exact ⟨hs_sub hx, fun h => hc0s (h ▸ hx)⟩
    · exact hdisj.mono_left (Set.sdiff_subset_sdiff_left Set.sdiff_subset)
    · intro x hx y hy hxy
      apply hpack x _ y _ hxy
      · rcases hx with ⟨⟨hxs, _⟩, hxns⟩ | hxX
        · exact Or.inl ⟨hxs, hxns⟩
        · exact Or.inr hxX
      · rcases hy with ⟨⟨hys, _⟩, hyns⟩ | hyX
        · exact Or.inl ⟨hys, hyns⟩
        · exact Or.inr hyX
  have htriv1 := (h1 c₀ hc₀).2 s X hrearr1
  have hX_sites : (X : Set H2) ⊆ sites37 := (lem_2_1_trivial_rearrangement c₀ hc₀ s X hrearr1).mp htriv1
  have hX_sub_s : X ⊆ s := by
    intro x hx
    by_contra hxns
    exact Set.disjoint_left.mp hX.2.2.1 ⟨hX_sites hx, hxns⟩ hx
  have hX_eq_s : X = s := Finset.eq_of_subset_of_card_le hX_sub_s hX.2.1.ge
  refine ⟨IsometryEquiv.refl H2, ?_⟩
  rw [hX_eq_s]
  ext y
  simp only [Set.mem_image, Set.mem_union, Set.mem_sdiff, Finset.mem_coe]
  constructor
  · rintro ⟨x, (⟨hxs, _⟩ | hxs), hxy⟩
    · change x = y at hxy; rwa [← hxy]
    · change x = y at hxy; rw [← hxy]; exact hX.1 hxs
  · intro hys
    refine ⟨y, ?_, rfl⟩
    by_cases h : y ∈ s
    · exact Or.inr h
    · exact Or.inl ⟨hys, h⟩

/-- **Section 1 Equivalence (M1)**: `IsStronglySolid r7 sites37 ↔ IsSolidOfOrder r7 sites37 1`. -/
theorem text_1_strong_solidity_iff_order_one :
    IsStronglySolid r7 sites37 ↔ IsSolidOfOrder r7 sites37 1 := by
  constructor
  · intro hSS
    refine ⟨isPacking_sites37, ?_⟩
    intro C' htrunc s X hX
    rcases htrunc with ⟨K, hKsub, hKcard, rfl⟩
    rcases Finset.card_eq_one.mp hKcard with ⟨c₀, rfl⟩
    have hc₀ : c₀ ∈ sites37 := hKsub (by simp)
    have htriv : Congruent (((sites37 \ {c₀}) \ (s : Set H2)) ∪ (X : Set H2)) (sites37 \ {c₀}) :=
      (hSS.2 c₀ hc₀).2 s X (by simpa only [Finset.coe_singleton] using hX)
    exact ⟨sites37 \ {c₀}, ⟨{c₀}, hKsub, by simp, by simp⟩,
      by simpa only [Finset.coe_singleton] using htriv⟩
  · intro hord
    apply isStronglySolid_of_oneVacancy_solid
    intro c₀ hc₀
    refine ⟨fun x hx y hy hxy => isPacking_sites37 x hx.1 y hy.1 hxy, ?_⟩
    intro s X hX
    have htrunc : IsKTruncation sites37 1 (sites37 \ {c₀}) :=
      ⟨{c₀}, by intro x hx; rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx; rwa [hx], by simp, by simp⟩
    rcases hord.2 (sites37 \ {c₀}) htrunc s X hX with ⟨C'', ⟨K'', hK''sub, hK''card, rfl⟩, ⟨φ, hφ⟩⟩
    rcases Finset.card_eq_one.mp hK''card with ⟨c₁, rfl⟩
    have hc₁ : c₁ ∈ sites37 := hK''sub (by simp)
    rcases delta237_direct_transitive hc₁ hc₀ with ⟨g, _, hgc1, hg_pres, _⟩
    refine ⟨φ.trans g, ?_⟩
    rw [show (⇑(φ.trans g) : H2 → H2) = g ∘ φ from rfl, Set.image_comp, hφ]
    ext y
    simp only [Set.mem_image, Set.mem_sdiff, Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxs, hxc1⟩, rfl⟩
      refine ⟨by rw [← hg_pres]; exact ⟨x, hxs, rfl⟩, ?_⟩
      intro heq; exact hxc1 (g.injective (heq.trans hgc1.symm))
    · rintro ⟨hys, hyc0⟩
      rw [← hg_pres] at hys
      rcases hys with ⟨x, hxs, rfl⟩
      refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
      intro heq; subst heq; exact hyc0 hgc1

/-- **Corollary 1.2** given Theorem 1.1 (`IsStronglySolid r7 sites37`). -/
theorem cor_1_2_of_strong_solidity (hSS : IsStronglySolid r7 sites37) :
    HasGradeOfSaturatedness r7 sites37 3 ∧ HasOrderOfSolidity r7 sites37 1 := by
  refine ⟨hasGradeOfSaturatedness_three, ?_, ?_⟩
  · exact text_1_strong_solidity_iff_order_one.mp hSS
  · intro m hm
    by_contra hgt
    push Not at hgt
    exact not_isSolidOfOrder_ge_two m (by omega) hm

end FejesTothP7.Proofs
