/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.ExactIdentity

/-!
# 5-Decimal Numerical Bounds for `{7, 3}` Constants

We prove `text_2_numerical_bounds`:
- `|2 * r7 - 1.09055| < 5e-6`
- `|h7 - 0.90380| < 5e-6`
- `|Rc7 - 0.62067| < 5e-6`
- `|ρ7 - 0.35853| < 5e-6`

using only Lean's three standard axioms via `Real.exp_bound` (`n = 10`) and a 10-digit
enclosure of `λ = 2 cos(π / 7)` from its minimal cubic `λ³ - λ² - 2λ + 1 = 0`.
-/

noncomputable section

namespace FejesTothP7.Proofs

private def coshPoly10 (x : ℝ) : ℝ :=
  1 + x ^ 2 / 2 + x ^ 4 / 24 + x ^ 6 / 720 + x ^ 8 / 40320

private def sinhPoly10 (x : ℝ) : ℝ :=
  x + x ^ 3 / 6 + x ^ 5 / 120 + x ^ 7 / 5040 + x ^ 9 / 362880

private lemma cosh_sub_poly10_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.cosh x - coshPoly10 x| ≤ x ^ 10 * 11 / 36288000 := by
  have hx_abs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hnx_abs : |-x| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; exact hx1
  have hb1 := Real.exp_bound hx_abs (n := 10) (by norm_num)
  have hb2 := Real.exp_bound hnx_abs (n := 10) (by norm_num)
  rw [abs_of_nonneg hx0] at hb1
  rw [abs_neg, abs_of_nonneg hx0] at hb2
  have hsum1 : (∑ m ∈ Finset.range 10, x ^ m / (m.factorial : ℝ)) =
      coshPoly10 x + sinhPoly10 x := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
      coshPoly10, sinhPoly10]
    norm_num; ring
  have hsum2 : (∑ m ∈ Finset.range 10, (-x) ^ m / (m.factorial : ℝ)) =
      coshPoly10 x - sinhPoly10 x := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
      coshPoly10, sinhPoly10]
    norm_num; ring
  have hconst : ((Nat.succ 10 : ℕ) : ℝ) / (((Nat.factorial 10 : ℕ) : ℝ) * (10 : ℕ)) =
      11 / 36288000 := by
    simp only [Nat.factorial]; norm_num
  rw [hsum1, hconst] at hb1
  rw [hsum2, hconst] at hb2
  rw [Real.cosh_eq]
  have h1 := abs_le.mp hb1
  have h2 := abs_le.mp hb2
  rw [abs_le]
  constructor <;> linarith

private lemma sinh_sub_poly10_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sinh x - sinhPoly10 x| ≤ x ^ 10 * 11 / 36288000 := by
  have hx_abs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hnx_abs : |-x| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; exact hx1
  have hb1 := Real.exp_bound hx_abs (n := 10) (by norm_num)
  have hb2 := Real.exp_bound hnx_abs (n := 10) (by norm_num)
  rw [abs_of_nonneg hx0] at hb1
  rw [abs_neg, abs_of_nonneg hx0] at hb2
  have hsum1 : (∑ m ∈ Finset.range 10, x ^ m / (m.factorial : ℝ)) =
      coshPoly10 x + sinhPoly10 x := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
      coshPoly10, sinhPoly10]
    norm_num; ring
  have hsum2 : (∑ m ∈ Finset.range 10, (-x) ^ m / (m.factorial : ℝ)) =
      coshPoly10 x - sinhPoly10 x := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
      coshPoly10, sinhPoly10]
    norm_num; ring
  have hconst : ((Nat.succ 10 : ℕ) : ℝ) / (((Nat.factorial 10 : ℕ) : ℝ) * (10 : ℕ)) =
      11 / 36288000 := by
    simp only [Nat.factorial]; norm_num
  rw [hsum1, hconst] at hb1
  rw [hsum2, hconst] at hb2
  rw [Real.sinh_eq]
  have h1 := abs_le.mp hb1
  have h2 := abs_le.mp hb2
  rw [abs_le]
  constructor <;> linarith

private lemma lambda7_enclosure :
    (1801937735 / 1000000000 : ℝ) < lambdaP 7 ∧ lambdaP 7 < (1801937736 / 1000000000 : ℝ) := by
  have hcub := lambda7_cubic
  have hlo3 := (lambdaP_bounds (le_refl 7)).1
  have hhi2 := (lambdaP_bounds (le_refl 7)).2
  have hgt17 : (17 / 10 : ℝ) < lambdaP 7 := by
    have : (17 / 10 : ℝ) < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hmono : ∀ a b : ℝ, (17 / 10 : ℝ) ≤ a → a ≤ 2 → (17 / 10 : ℝ) ≤ b → b ≤ 2 →
      a ^ 3 - a ^ 2 - 2 * a + 1 < b ^ 3 - b ^ 2 - 2 * b + 1 → a < b := by
    intro a b ha1 ha2 hb1 hb2 hlt
    by_contra hle; push Not at hle
    have hdiff : (b ^ 3 - b ^ 2 - 2 * b + 1) - (a ^ 3 - a ^ 2 - 2 * a + 1) =
        (b - a) * (b ^ 2 + b * a + a ^ 2 - b - a - 2) := by ring
    have hfac : 0 < b ^ 2 + b * a + a ^ 2 - b - a - 2 := by nlinarith
    nlinarith
  constructor
  · apply hmono (1801937735 / 1000000000) (lambdaP 7) (by norm_num) (by norm_num) hgt17.le hhi2.le
    rw [hcub]; norm_num
  · apply hmono (lambdaP 7) (1801937736 / 1000000000) hgt17.le hhi2.le (by norm_num) (by norm_num)
    rw [hcub]; norm_num

/-- **Section 2.1 numerical bounds**: 5-decimal accuracy for `2 r7`, `h7`, `Rc7`, and `ρ7`. -/
theorem text_2_numerical_bounds :
    |2 * r7 - 1.09055| < 5e-6 ∧
    |h7 - 0.90380| < 5e-6 ∧
    |Rc7 - 0.62067| < 5e-6 ∧
    |ρ7 - 0.35853| < 5e-6 := by
  have h7le : 7 ≤ 7 := le_refl 7
  obtain ⟨hl_lo, hl_hi⟩ := lambda7_enclosure
  have hlam2_lo : (1801937735 / 1000000000 : ℝ) ^ 2 < lambdaP 7 ^ 2 := by nlinarith
  have hlam2_hi : lambdaP 7 ^ 2 < (1801937736 / 1000000000 : ℝ) ^ 2 := by nlinarith
  have h4ml_pos : 0 < 4 - lambdaP 7 ^ 2 := by linarith [(lambdaP_sq_bounds h7le).2]
  have hlam3_pos : 0 < lambdaP 7 ^ 2 - 3 := by linarith [(lambdaP_sq_bounds h7le).1]
  have hcosh_lt_iff : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → (Real.cosh a < Real.cosh b ↔ a < b) := by
    intro a b ha hb
    rw [← Real.arcosh_lt_arcosh (Real.cosh_pos a) (Real.cosh_pos b),
        Real.arcosh_cosh ha, Real.arcosh_cosh hb]
  -- 1) |2 * r7 - 1.09055| < 5e-6
  have hr_bound : |2 * r7 - 1.09055| < 5e-6 := by
    have hcr_sq : Real.cosh r7 ^ 2 = 1 / (4 - lambdaP 7 ^ 2) := by
      rw [show r7 = rP 7 from rfl, cosh_rP_lambda h7le, div_pow, one_pow, Real.sq_sqrt h4ml_pos.le]
    have hlo : (0.5452725 : ℝ) < r7 := by
      rw [← hcosh_lt_iff (by norm_num) r7_pos.le]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.5452725) (by norm_num) (by norm_num))).2
      have hch_ub : Real.cosh 0.5452725 < 1.1523818 := by
        unfold coshPoly10 at h1; linarith
      have hch_sq_ub : Real.cosh 0.5452725 ^ 2 < 1.1523818 ^ 2 := by
        nlinarith [Real.cosh_pos (0.5452725 : ℝ)]
      have hch_sq_lt : Real.cosh 0.5452725 ^ 2 < Real.cosh r7 ^ 2 := by
        rw [hcr_sq, lt_div_iff₀ h4ml_pos]
        nlinarith
      nlinarith [Real.cosh_pos (0.5452725 : ℝ), Real.cosh_pos r7]
    have hhi : r7 < (0.5452775 : ℝ) := by
      rw [← hcosh_lt_iff r7_pos.le (by norm_num)]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.5452775) (by norm_num) (by norm_num))).1
      have hch_lb : 1.1523832 < Real.cosh 0.5452775 := by
        unfold coshPoly10 at h1; linarith
      have hch_sq_lb : 1.1523832 ^ 2 < Real.cosh 0.5452775 ^ 2 := by
        nlinarith [Real.cosh_pos (0.5452775 : ℝ)]
      have hch_sq_gt : Real.cosh r7 ^ 2 < Real.cosh 0.5452775 ^ 2 := by
        rw [hcr_sq, div_lt_iff₀ h4ml_pos]
        nlinarith
      nlinarith [Real.cosh_pos (0.5452775 : ℝ), Real.cosh_pos r7]
    rw [abs_lt]; constructor <;> linarith
  -- 2) |h7 - 0.90380| < 5e-6
  have hh_bound : |h7 - 0.90380| < 5e-6 := by
    have hh_pos : 0 < h7 := hP_pos h7le
    have hch_sq : Real.cosh h7 ^ 2 = (lambdaP 7 ^ 2 - 2) ^ 2 / (4 - lambdaP 7 ^ 2) := by
      rw [show h7 = hP 7 from rfl, cosh_hP_lambda h7le, div_pow, Real.sq_sqrt h4ml_pos.le]
    have hnum_lo : ((1801937735 / 1000000000 : ℝ) ^ 2 - 2) ^ 2 < (lambdaP 7 ^ 2 - 2) ^ 2 := by
      nlinarith
    have hnum_hi : (lambdaP 7 ^ 2 - 2) ^ 2 < ((1801937736 / 1000000000 : ℝ) ^ 2 - 2) ^ 2 := by
      nlinarith
    have hlo : (0.903795 : ℝ) < h7 := by
      rw [← hcosh_lt_iff (by norm_num) hh_pos.le]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.903795) (by norm_num) (by norm_num))).2
      have hch_ub : Real.cosh 0.903795 < 1.436995 := by
        unfold coshPoly10 at h1; linarith
      have hch_sq_ub : Real.cosh 0.903795 ^ 2 < 1.436995 ^ 2 := by
        nlinarith [Real.cosh_pos (0.903795 : ℝ)]
      have hch_sq_lt : Real.cosh 0.903795 ^ 2 < Real.cosh h7 ^ 2 := by
        rw [hch_sq, lt_div_iff₀ h4ml_pos]
        nlinarith
      nlinarith [Real.cosh_pos (0.903795 : ℝ), Real.cosh_pos h7]
    have hhi : h7 < (0.903805 : ℝ) := by
      rw [← hcosh_lt_iff hh_pos.le (by norm_num)]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.903805) (by norm_num) (by norm_num))).1
      have hch_lb : 1.437000 < Real.cosh 0.903805 := by
        unfold coshPoly10 at h1; linarith
      have hch_sq_lb : 1.437000 ^ 2 < Real.cosh 0.903805 ^ 2 := by
        nlinarith [Real.cosh_pos (0.903805 : ℝ)]
      have hch_sq_gt : Real.cosh h7 ^ 2 < Real.cosh 0.903805 ^ 2 := by
        rw [hch_sq, div_lt_iff₀ h4ml_pos]
        nlinarith
      nlinarith [Real.cosh_pos (0.903805 : ℝ), Real.cosh_pos h7]
    rw [abs_lt]; constructor <;> linarith
  -- 3) |Rc7 - 0.62067| < 5e-6
  have hRc_bound : |Rc7 - 0.62067| < 5e-6 := by
    have hRc_pos : 0 < Rc7 := lt_trans r7_pos eq_2_order.1
    have hsh_sq : Real.sinh Rc7 ^ 2 = 4 * (lambdaP 7 ^ 2 - 3) / (3 * (4 - lambdaP 7 ^ 2)) := by
      rw [eq_1_consts.2.2.2.2, Real.sin_pi_div_three, show r7 = rP 7 from rfl, sinh_rP_lambda h7le]
      rw [div_pow, div_pow, div_pow, Real.sq_sqrt hlam3_pos.le, Real.sq_sqrt h4ml_pos.le,
          Real.sq_sqrt (by norm_num)]
      field_simp [h4ml_pos.ne']; norm_num
    have hlo : (0.620665 : ℝ) < Rc7 := by
      rw [← Real.sinh_lt_sinh]
      have h1 := (abs_le.mp (sinh_sub_poly10_abs_le (x := 0.620665) (by norm_num) (by norm_num))).2
      have hsh_ub : Real.sinh 0.620665 < 0.661293 := by
        unfold sinhPoly10 at h1; linarith
      have hsh_pos : 0 < Real.sinh 0.620665 := Real.sinh_pos_iff.mpr (by norm_num)
      have hsh_sq_ub : Real.sinh 0.620665 ^ 2 < 0.661293 ^ 2 := by nlinarith
      have hsh_Rc_pos : 0 < Real.sinh Rc7 := Real.sinh_pos_iff.mpr hRc_pos
      have hsq_lt : Real.sinh 0.620665 ^ 2 < Real.sinh Rc7 ^ 2 := by
        rw [hsh_sq, lt_div_iff₀ (by linarith)]
        nlinarith
      nlinarith
    have hhi : Rc7 < (0.620675 : ℝ) := by
      rw [← Real.sinh_lt_sinh]
      have h1 := (abs_le.mp (sinh_sub_poly10_abs_le (x := 0.620675) (by norm_num) (by norm_num))).1
      have hsh_lb : 0.661299 < Real.sinh 0.620675 := by
        unfold sinhPoly10 at h1; linarith
      have hsh_sq_lb : 0.661299 ^ 2 < Real.sinh 0.620675 ^ 2 := by nlinarith
      have hsh_Rc_pos : 0 < Real.sinh Rc7 := Real.sinh_pos_iff.mpr hRc_pos
      have hsq_gt : Real.sinh Rc7 ^ 2 < Real.sinh 0.620675 ^ 2 := by
        rw [hsh_sq, div_lt_iff₀ (by linarith)]
        nlinarith
      nlinarith
    rw [abs_lt]; constructor <;> linarith
  -- 4) |ρ7 - 0.35853| < 5e-6
  have hρ_bound : |ρ7 - 0.35853| < 5e-6 := by
    have hρ_pos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
    have hcosh_ρ : Real.cosh ρ7 = (lambdaP 7 - 1) / (4 - lambdaP 7 ^ 2) := by
      have hρ_eq : ρ7 = hP 7 - rP 7 := by
        have h := prop_3_1_exact_identity; unfold h7 r7 at h; linarith
      rw [hρ_eq, Real.cosh_sub, cosh_hP_lambda h7le, cosh_rP_lambda h7le,
          sinh_hP_lambda h7le, sinh_rP_lambda h7le]
      have hrt4 : Real.sqrt (4 - lambdaP 7 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h4ml_pos).ne'
      field_simp [hrt4, h4ml_pos.ne']
      rw [Real.sq_sqrt h4ml_pos.le, Real.sq_sqrt hlam3_pos.le]
      linear_combination -(4 - lambdaP 7 ^ 2) * lambda7_cubic
    have hlo : (0.358525 : ℝ) < ρ7 := by
      rw [← hcosh_lt_iff (by norm_num) hρ_pos.le, hcosh_ρ, lt_div_iff₀ h4ml_pos]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.358525) (by norm_num) (by norm_num))).2
      have hch_ub : Real.cosh 0.358525 < 1.064961493 := by
        unfold coshPoly10 at h1; linarith
      nlinarith
    have hhi : ρ7 < (0.358535 : ℝ) := by
      rw [← hcosh_lt_iff hρ_pos.le (by norm_num), hcosh_ρ, div_lt_iff₀ h4ml_pos]
      have h1 := (abs_le.mp (cosh_sub_poly10_abs_le (x := 0.358535) (by norm_num) (by norm_num))).1
      have hch_lb : 1.064964 < Real.cosh 0.358535 := by
        unfold coshPoly10 at h1; linarith
      nlinarith
    rw [abs_lt]; constructor <;> linarith
  exact ⟨hr_bound, hh_bound, hRc_bound, hρ_bound⟩

end FejesTothP7.Proofs
