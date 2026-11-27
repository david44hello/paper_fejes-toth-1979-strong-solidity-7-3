module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Defs.H2
public import FejesTothP7.Defs.Constants
public import FejesTothP7.Defs.Tiling
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# Exact Trigonometric Identities, Constants, and Tip Distances for `{7, 3}`

We establish the cubic identity `λ^3 - λ^2 - 2λ + 1 = 0` for `λ = 2 cos(π / 7)`,
the hyperbolic trigonometric relations for `r7, h7, Rc7`, the ordering
`ρ7 < r7 < Rc7 < h7 < 2 * r7`, the properties of `β7`, the exact identity `h7 = r7 + ρ7`,
and the tip-point distances `eq_5_tip_distances`.
-/

noncomputable section

open Filter Set

namespace FejesTothP7.Proofs

/-! ### Elementary hyperbolic helpers -/

lemma cosh_two_mul' (x : ℝ) : Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
  rw [Real.cosh_two_mul]
  linarith [Real.cosh_sq_sub_sinh_sq x]

lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

lemma strictMono_tanh : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_lt_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have hsub : Real.sinh (y - x) = Real.sinh y * Real.cosh x - Real.cosh y * Real.sinh x :=
    Real.sinh_sub y x
  have hpos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (by linarith)
  linarith

lemma continuous_tanh : Continuous Real.tanh := by
  have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-! ### General `{p, 3}` (`p ≥ 7`) algebraic identities in `λ_p = 2 cos(π / p)` -/

/-- `λ_p = 2 cos(π / p)`. -/
def lambdaP (p : ℕ) : ℝ := 2 * Real.cos (Real.pi / (p : ℝ))

lemma pi_div_p_pos {p : ℕ} (hp : 7 ≤ p) : 0 < Real.pi / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  exact div_pos Real.pi_pos hp0

lemma pi_div_p_lt_pi_div_six {p : ℕ} (hp : 7 ≤ p) : Real.pi / (p : ℝ) < Real.pi / 6 := by
  have hp6 : (6 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 6 < p)
  exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hp6

lemma sin_pi_div_p_pos {p : ℕ} (hp : 7 ≤ p) : 0 < Real.sin (Real.pi / (p : ℝ)) := by
  apply Real.sin_pos_of_pos_of_lt_pi (pi_div_p_pos hp)
  linarith [pi_div_p_lt_pi_div_six hp, Real.pi_pos]

lemma sin_pi_div_p_lt_half {p : ℕ} (hp : 7 ≤ p) : Real.sin (Real.pi / (p : ℝ)) < 1 / 2 := by
  rw [← Real.sin_pi_div_six]
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · linarith [pi_div_p_pos hp, Real.pi_pos]
  · linarith [pi_div_p_lt_pi_div_six hp, Real.pi_pos]
  · exact pi_div_p_lt_pi_div_six hp

lemma one_lt_inv_two_sin_pi_div_p {p : ℕ} (hp : 7 ≤ p) :
    1 < 1 / (2 * Real.sin (Real.pi / (p : ℝ))) := by
  have hpos : 0 < 2 * Real.sin (Real.pi / (p : ℝ)) := by linarith [sin_pi_div_p_pos hp]
  rw [one_lt_div hpos]
  linarith [sin_pi_div_p_lt_half hp]

lemma rP_pos {p : ℕ} (hp : 7 ≤ p) : 0 < rP p :=
  Real.arcosh_pos (one_lt_inv_two_sin_pi_div_p hp)

lemma lambdaP_bounds {p : ℕ} (hp : 7 ≤ p) :
    Real.sqrt 3 < lambdaP p ∧ lambdaP p < 2 := by
  unfold lambdaP
  have hpos := pi_div_p_pos hp
  have hlt := pi_div_p_lt_pi_div_six hp
  have hcos_gt : Real.sqrt 3 / 2 < Real.cos (Real.pi / (p : ℝ)) := by
    rw [← Real.cos_pi_div_six]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi hpos.le (by linarith [Real.pi_pos]) hlt
  have hcos_lt : Real.cos (Real.pi / (p : ℝ)) < 1 := by
    rw [← Real.cos_zero]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_pos]) hpos
  constructor <;> linarith

lemma lambdaP_sq_bounds {p : ℕ} (hp : 7 ≤ p) :
    3 < lambdaP p ^ 2 ∧ lambdaP p ^ 2 < 4 := by
  obtain ⟨hlo, hhi⟩ := lambdaP_bounds hp
  have h3pos : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor
  · have h1 : Real.sqrt 3 ^ 2 < lambdaP p ^ 2 := by nlinarith
    rwa [Real.sq_sqrt (by norm_num)] at h1
  · nlinarith

lemma four_sin_sq_eq {p : ℕ} :
    4 * Real.sin (Real.pi / (p : ℝ)) ^ 2 = 4 - lambdaP p ^ 2 := by
  unfold lambdaP
  have hcs := Real.sin_sq_add_cos_sq (Real.pi / (p : ℝ))
  nlinarith

lemma two_sin_eq_sqrt {p : ℕ} (hp : 7 ≤ p) :
    2 * Real.sin (Real.pi / (p : ℝ)) = Real.sqrt (4 - lambdaP p ^ 2) := by
  have hpos : 0 ≤ 2 * Real.sin (Real.pi / (p : ℝ)) := by linarith [sin_pi_div_p_pos hp]
  rw [← Real.sqrt_sq hpos]
  congr 1
  have h := four_sin_sq_eq (p := p)
  linarith

lemma cosh_rP {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (rP p) = 1 / (2 * Real.sin (Real.pi / (p : ℝ))) :=
  Real.cosh_arcosh (one_lt_inv_two_sin_pi_div_p hp).le

lemma cosh_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (rP p) = 1 / Real.sqrt (4 - lambdaP p ^ 2) := by
  rw [cosh_rP hp, two_sin_eq_sqrt hp]

lemma sinh_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.sinh (rP p) = Real.sqrt (lambdaP p ^ 2 - 3) / Real.sqrt (4 - lambdaP p ^ 2) := by
  have hpos : 0 ≤ Real.sinh (rP p) := Real.sinh_nonneg_iff.mpr (rP_pos hp).le
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
  have hrhs : 0 ≤ Real.sqrt (lambdaP p ^ 2 - 3) / Real.sqrt (4 - lambdaP p ^ 2) := by positivity
  rw [← Real.sqrt_sq hpos, ← Real.sqrt_sq hrhs]
  congr 1
  have hch := Real.cosh_sq_sub_sinh_sq (rP p)
  have hcr := cosh_rP_lambda hp
  rw [div_pow, Real.sq_sqrt h3.le, Real.sq_sqrt hsq.le]
  have hcr2 : Real.cosh (rP p) ^ 2 = 1 / (4 - lambdaP p ^ 2) := by
    rw [hcr, div_pow, one_pow, Real.sq_sqrt hsq.le]
  have hsh2 : Real.sinh (rP p) ^ 2 = Real.cosh (rP p) ^ 2 - 1 := by linarith
  rw [hsh2, hcr2]
  field_simp [hsq.ne']
  ring

lemma cosh_two_rP_eq {p : ℕ} :
    Real.cosh (2 * rP p) = 2 * Real.cosh (rP p) ^ 2 - 1 :=
  cosh_two_mul' (rP p)

lemma cosh_two_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (2 * rP p) = (lambdaP p ^ 2 - 2) / (4 - lambdaP p ^ 2) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  rw [cosh_two_rP_eq, cosh_rP_lambda hp, div_pow, one_pow, Real.sq_sqrt hsq.le]
  field_simp [hsq.ne']
  ring

lemma cosh_two_rP_cos_alpha {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (2 * rP p) = Real.cos (alphaP p) / (1 - Real.cos (alphaP p)) := by
  have h2a : alphaP p = 2 * (Real.pi / (p : ℝ)) := by unfold alphaP; ring
  rw [h2a, Real.cos_two_mul]
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h2 : 2 * Real.cos (Real.pi / (p : ℝ)) ^ 2 - 1 = (lambdaP p ^ 2 - 2) / 2 := by
    unfold lambdaP; ring
  have h1 : 1 - (2 * Real.cos (Real.pi / (p : ℝ)) ^ 2 - 1) = (4 - lambdaP p ^ 2) / 2 := by
    linarith [h2]
  rw [cosh_two_rP_lambda hp, h1, h2]
  field_simp [hsq.ne']

lemma sinh_two_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.sinh (2 * rP p) = 2 * Real.sqrt (lambdaP p ^ 2 - 3) / (4 - lambdaP p ^ 2) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  rw [Real.sinh_two_mul, sinh_rP_lambda hp, cosh_rP_lambda hp]
  field_simp [(Real.sqrt_pos.mpr hsq).ne']
  rw [Real.sq_sqrt hsq.le]

lemma tanh_two_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.tanh (2 * rP p) = 2 * Real.sqrt (lambdaP p ^ 2 - 3) / (lambdaP p ^ 2 - 2) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h2 : 0 < lambdaP p ^ 2 - 2 := by linarith [(lambdaP_sq_bounds hp).1]
  rw [Real.tanh_eq_sinh_div_cosh, sinh_two_rP_lambda hp, cosh_two_rP_lambda hp]
  field_simp [hsq.ne', h2.ne']

lemma cosh_rP_lt_div {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (rP p) < Real.cosh (2 * rP p) / Real.cosh (rP p) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
  have hcr_pos : 0 < Real.cosh (rP p) := Real.cosh_pos _
  rw [lt_div_iff₀ hcr_pos]
  rw [cosh_two_rP_lambda hp, cosh_rP_lambda hp, div_mul_div_comm, one_mul,
      Real.mul_self_sqrt hsq.le]
  rw [div_lt_div_iff_of_pos_right hsq]
  linarith

lemma one_lt_cosh_hP_arg {p : ℕ} (hp : 7 ≤ p) :
    1 < Real.cosh (2 * rP p) / Real.cosh (rP p) :=
  lt_trans (Real.one_lt_cosh.mpr (rP_pos hp).ne') (cosh_rP_lt_div hp)

lemma hP_pos {p : ℕ} (hp : 7 ≤ p) : 0 < hP p :=
  Real.arcosh_pos (one_lt_cosh_hP_arg hp)

lemma cosh_hP {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (hP p) = Real.cosh (2 * rP p) / Real.cosh (rP p) :=
  Real.cosh_arcosh (one_lt_cosh_hP_arg hp).le

lemma cosh_hP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.cosh (hP p) = (lambdaP p ^ 2 - 2) / Real.sqrt (4 - lambdaP p ^ 2) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have hrt : 0 < Real.sqrt (4 - lambdaP p ^ 2) := Real.sqrt_pos.mpr hsq
  rw [cosh_hP hp, cosh_two_rP_lambda hp, cosh_rP_lambda hp]
  have hmul : Real.sqrt (4 - lambdaP p ^ 2) * Real.sqrt (4 - lambdaP p ^ 2) = 4 - lambdaP p ^ 2 :=
    Real.mul_self_sqrt hsq.le
  field_simp [hsq.ne', hrt.ne']
  nlinarith [hmul]

lemma sinh_hP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.sinh (hP p) = lambdaP p * Real.sqrt (lambdaP p ^ 2 - 3) / Real.sqrt (4 - lambdaP p ^ 2) := by
  have hpos : 0 ≤ Real.sinh (hP p) := Real.sinh_nonneg_iff.mpr (hP_pos hp).le
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
  have hlam : 0 < lambdaP p := lt_trans (Real.sqrt_pos.mpr (by norm_num)) (lambdaP_bounds hp).1
  have hrhs : 0 ≤ lambdaP p * Real.sqrt (lambdaP p ^ 2 - 3) / Real.sqrt (4 - lambdaP p ^ 2) := by
    positivity
  rw [← Real.sqrt_sq hpos, ← Real.sqrt_sq hrhs]
  congr 1
  have hch := Real.cosh_sq_sub_sinh_sq (hP p)
  have hch2 : Real.cosh (hP p) ^ 2 = (lambdaP p ^ 2 - 2) ^ 2 / (4 - lambdaP p ^ 2) := by
    rw [cosh_hP_lambda hp, div_pow, Real.sq_sqrt hsq.le]
  have hsh2 : Real.sinh (hP p) ^ 2 = Real.cosh (hP p) ^ 2 - 1 := by linarith
  rw [hsh2, hch2, div_pow, mul_pow, Real.sq_sqrt h3.le, Real.sq_sqrt hsq.le]
  field_simp [hsq.ne']
  ring

lemma rP_lt_hP {p : ℕ} (hp : 7 ≤ p) : rP p < hP p := by
  rw [← Real.arcosh_cosh (rP_pos hp).le, ← Real.arcosh_cosh (hP_pos hp).le]
  rw [Real.arcosh_lt_arcosh (Real.cosh_pos _) (Real.cosh_pos _)]
  rw [cosh_hP hp]
  exact cosh_rP_lt_div hp

lemma hP_lt_two_rP {p : ℕ} (hp : 7 ≤ p) : hP p < 2 * rP p := by
  have h2r : 0 ≤ 2 * rP p := by linarith [rP_pos hp]
  rw [← Real.arcosh_cosh (hP_pos hp).le, ← Real.arcosh_cosh h2r]
  rw [Real.arcosh_lt_arcosh (Real.cosh_pos _) (Real.cosh_pos _)]
  rw [cosh_hP hp]
  have hcr : 1 < Real.cosh (rP p) := Real.one_lt_cosh.mpr (rP_pos hp).ne'
  have hc2r : 0 < Real.cosh (2 * rP p) := Real.cosh_pos _
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

lemma two_cos_three_pi_div_p {p : ℕ} :
    2 * Real.cos (3 * Real.pi / (p : ℝ)) = lambdaP p ^ 3 - 3 * lambdaP p := by
  have h3 : 3 * Real.pi / (p : ℝ) = 3 * (Real.pi / (p : ℝ)) := by ring
  rw [h3, Real.cos_three_mul]
  unfold lambdaP
  ring

lemma tanh_two_rP_mul_cos_three_pos {p : ℕ} (hp : 7 ≤ p) :
    0 < Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ)) := by
  apply mul_pos
  · exact tanh_pos_of_pos (by linarith [rP_pos hp])
  · apply Real.cos_pos_of_mem_Ioo
    have hpos := pi_div_p_pos hp
    have hlt := pi_div_p_lt_pi_div_six hp
    have h3 : 3 * Real.pi / (p : ℝ) = 3 * (Real.pi / (p : ℝ)) := by ring
    rw [h3]
    constructor <;> linarith [Real.pi_pos]

lemma tanh_two_rP_mul_cos_three_lt_one {p : ℕ} (hp : 7 ≤ p) :
    Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ)) < 1 := by
  have ht1 : Real.tanh (2 * rP p) < 1 := Real.tanh_lt_one _
  have ht0 : 0 < Real.tanh (2 * rP p) := tanh_pos_of_pos (by linarith [rP_pos hp])
  have hc1 : Real.cos (3 * Real.pi / (p : ℝ)) ≤ 1 := Real.cos_le_one _
  nlinarith

lemma rhoStarP_pos {p : ℕ} (hp : 7 ≤ p) : 0 < rhoStarP p := by
  unfold rhoStarP
  have hpos := tanh_two_rP_mul_cos_three_pos hp
  have hlt := tanh_two_rP_mul_cos_three_lt_one hp
  have h1 : 0 < Real.artanh (Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ))) :=
    Real.artanh_pos ⟨hpos, hlt⟩
  linarith

lemma tanh_half_rhoStarP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.tanh (rhoStarP p / 2) =
      (lambdaP p ^ 3 - 3 * lambdaP p) * Real.sqrt (lambdaP p ^ 2 - 3) / (lambdaP p ^ 2 - 2) := by
  unfold rhoStarP
  have hhalf : 2 * Real.artanh (Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ))) / 2 =
      Real.artanh (Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ))) := by ring
  rw [hhalf, Real.tanh_artanh]
  · rw [tanh_two_rP_lambda hp]
    have hc3 : Real.cos (3 * Real.pi / (p : ℝ)) = (lambdaP p ^ 3 - 3 * lambdaP p) / 2 := by
      linarith [two_cos_three_pi_div_p (p := p)]
    rw [hc3]
    ring
  · exact ⟨by linarith [tanh_two_rP_mul_cos_three_pos hp], tanh_two_rP_mul_cos_three_lt_one hp⟩

/-- Universal identity for all `p ≥ 7`: `tanh((h_p - r_p) / 2) = sqrt(λ_p² - 3) / (λ_p + 1)`. -/
lemma tanh_half_hP_sub_rP_lambda {p : ℕ} (hp : 7 ≤ p) :
    Real.tanh ((hP p - rP p) / 2) = Real.sqrt (lambdaP p ^ 2 - 3) / (lambdaP p + 1) := by
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
  have hlo := (lambdaP_bounds hp).1
  have hhi := (lambdaP_bounds hp).2
  have hlam : 0 < lambdaP p := lt_trans (Real.sqrt_pos.mpr (by norm_num)) hlo
  have h1 : 0 < lambdaP p + 1 := by linarith
  have h2 : 0 < 2 - lambdaP p := by linarith
  have hmul_sq : Real.sqrt (4 - lambdaP p ^ 2) * Real.sqrt (4 - lambdaP p ^ 2) = 4 - lambdaP p ^ 2 :=
    Real.mul_self_sqrt hsq.le
  have hmul_3 : Real.sqrt (lambdaP p ^ 2 - 3) * Real.sqrt (lambdaP p ^ 2 - 3) = lambdaP p ^ 2 - 3 :=
    Real.mul_self_sqrt h3.le
  have hcosh_sub : Real.cosh (hP p - rP p) =
      ((lambdaP p ^ 2 - 2) - lambdaP p * (lambdaP p ^ 2 - 3)) / (4 - lambdaP p ^ 2) := by
    rw [Real.cosh_sub, cosh_hP_lambda hp, cosh_rP_lambda hp, sinh_hP_lambda hp, sinh_rP_lambda hp]
    have hrt_ne : Real.sqrt (4 - lambdaP p ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
    field_simp [hrt_ne, hsq.ne']
    rw [Real.sq_sqrt hsq.le, Real.sq_sqrt h3.le]
  have hsinh_sub : Real.sinh (hP p - rP p) =
      (2 + lambdaP p - lambdaP p ^ 2) * Real.sqrt (lambdaP p ^ 2 - 3) / (4 - lambdaP p ^ 2) := by
    rw [Real.sinh_sub, sinh_hP_lambda hp, cosh_rP_lambda hp, cosh_hP_lambda hp, sinh_rP_lambda hp]
    have hrt_ne : Real.sqrt (4 - lambdaP p ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
    field_simp [hrt_ne, hsq.ne']
    rw [Real.sq_sqrt hsq.le]
    ring
  have hhalf_id : Real.tanh ((hP p - rP p) / 2) =
      Real.sinh (hP p - rP p) / (Real.cosh (hP p - rP p) + 1) := by
    have hch_pos : 0 < Real.cosh ((hP p - rP p) / 2) := Real.cosh_pos _
    have hx : hP p - rP p = 2 * ((hP p - rP p) / 2) := by ring
    rw [Real.tanh_eq_sinh_div_cosh]
    conv_rhs => rw [hx, Real.sinh_two_mul, cosh_two_mul']
    field_simp [hch_pos.ne']
    ring
  rw [hhalf_id, hsinh_sub, hcosh_sub]
  have hdenom : ((lambdaP p ^ 2 - 2) - lambdaP p * (lambdaP p ^ 2 - 3)) / (4 - lambdaP p ^ 2) + 1 =
      (2 - lambdaP p) * (lambdaP p + 1) ^ 2 / (4 - lambdaP p ^ 2) := by
    field_simp [hsq.ne']
    ring
  rw [hdenom]
  have hnum : 2 + lambdaP p - lambdaP p ^ 2 = (2 - lambdaP p) * (lambdaP p + 1) := by ring
  rw [hnum]
  field_simp [hsq.ne', h1.ne', h2.ne']

/-! ### The exact `p = 7` cubic and `Proposition 3.1` -/

/-- `λ = 2 cos(π / 7)` satisfies the minimal cubic `λ³ - λ² - 2λ + 1 = 0`. -/
lemma lambda7_cubic : lambdaP 7 ^ 3 - lambdaP 7 ^ 2 - 2 * lambdaP 7 + 1 = 0 := by
  have hcos_eq : Real.cos (4 * (Real.pi / 7)) = -Real.cos (3 * (Real.pi / 7)) := by
    have h1 : 4 * (Real.pi / 7) = Real.pi - 3 * (Real.pi / 7) := by ring
    rw [h1, Real.cos_pi_sub]
  have hc3 : Real.cos (3 * (Real.pi / 7)) =
      4 * Real.cos (Real.pi / 7) ^ 3 - 3 * Real.cos (Real.pi / 7) := Real.cos_three_mul _
  have hc4 : Real.cos (4 * (Real.pi / 7)) =
      2 * (2 * Real.cos (Real.pi / 7) ^ 2 - 1) ^ 2 - 1 := by
    have h4 : 4 * (Real.pi / 7) = 2 * (2 * (Real.pi / 7)) := by ring
    rw [h4, Real.cos_two_mul, Real.cos_two_mul]
  have hfac : (lambdaP 7 + 2) * (lambdaP 7 ^ 3 - lambdaP 7 ^ 2 - 2 * lambdaP 7 + 1) = 0 := by
    unfold lambdaP
    have h7c : ((7 : ℕ) : ℝ) = 7 := by norm_num
    rw [h7c]
    nlinarith [hcos_eq, hc3, hc4]
  have hpos : 0 < lambdaP 7 + 2 := by
    linarith [(lambdaP_bounds (by norm_num : 7 ≤ 7)).1, Real.sqrt_nonneg 3]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · linarith
  · exact h0

/-- **Proposition 3.1 (Exact `p = 7` identity)**: `h7 = r7 + ρ7`. -/
theorem prop_3_1_exact_identity : h7 = r7 + ρ7 := by
  unfold h7 r7 ρ7
  have h7le : 7 ≤ 7 := le_refl 7
  have h1 : Real.tanh ((hP 7 - rP 7) / 2) = Real.tanh (rhoStarP 7 / 2) := by
    rw [tanh_half_hP_sub_rP_lambda h7le, tanh_half_rhoStarP_lambda h7le]
    have hlam1 : 0 < lambdaP 7 + 1 := by
      linarith [(lambdaP_bounds h7le).1, Real.sqrt_nonneg 3]
    have hlam2 : 0 < lambdaP 7 ^ 2 - 2 := by linarith [(lambdaP_sq_bounds h7le).1]
    rw [div_eq_div_iff hlam1.ne' hlam2.ne']
    have hcub := lambda7_cubic
    linear_combination -Real.sqrt (lambdaP 7 ^ 2 - 3) * (lambdaP 7 + 2) * hcub
  have h2 : (hP 7 - rP 7) / 2 = rhoStarP 7 / 2 := Real.tanh_injective h1
  linarith

/-! ### Equations (1), (2), properties of `β7`, and Corollary 1.2 ordering -/

/-- **Equation (1)**: Hyperbolic trigonometric identities for `r7, h7, Rc7`. -/
theorem eq_1_consts :
    Real.cosh r7 = 1 / (2 * Real.sin (Real.pi / 7)) ∧
    Real.cosh (2 * r7) = 2 * Real.cosh r7 ^ 2 - 1 ∧
    Real.cosh (2 * r7) = Real.cos α7 / (1 - Real.cos α7) ∧
    Real.cosh h7 = Real.cosh (2 * r7) / Real.cosh r7 ∧
    Real.sinh Rc7 = Real.sinh r7 / Real.sin (Real.pi / 3) := by
  have h7le : 7 ≤ 7 := le_refl 7
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [r7] using cosh_rP h7le
  · exact cosh_two_rP_eq
  · simpa [r7, α7] using cosh_two_rP_cos_alpha h7le
  · simpa [r7, h7] using cosh_hP h7le
  · unfold Rc7
    exact Real.sinh_arsinh _

/-- **Equation (2)**: `r7 < Rc7 < h7 < 2 * r7`. -/
theorem eq_2_order : r7 < Rc7 ∧ Rc7 < h7 ∧ h7 < 2 * r7 := by
  have h7le : 7 ≤ 7 := le_refl 7
  have hr_pos : 0 < r7 := r7_pos
  have hsh_r_pos : 0 < Real.sinh r7 := Real.sinh_pos_iff.mpr hr_pos
  have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hsin3_pos : 0 < Real.sin (Real.pi / 3) := by rw [hsin3]; positivity
  have hsin3_lt_one : Real.sin (Real.pi / 3) < 1 := by
    rw [hsin3]
    have : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have h1 : r7 < Rc7 := by
    rw [← Real.sinh_lt_sinh]
    unfold Rc7
    rw [Real.sinh_arsinh, lt_div_iff₀ hsin3_pos]
    nlinarith
  have h2 : Rc7 < h7 := by
    rw [← Real.sinh_lt_sinh]
    unfold Rc7 h7
    rw [Real.sinh_arsinh, hsin3]
    rw [show r7 = rP 7 from rfl, sinh_rP_lambda h7le, sinh_hP_lambda h7le]
    have hsq : 0 < 4 - lambdaP 7 ^ 2 := by linarith [(lambdaP_sq_bounds h7le).2]
    have h3 : 0 < lambdaP 7 ^ 2 - 3 := by linarith [(lambdaP_sq_bounds h7le).1]
    have hrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hrt4 : 0 < Real.sqrt (4 - lambdaP 7 ^ 2) := Real.sqrt_pos.mpr hsq
    have hrt_lam3 : 0 < Real.sqrt (lambdaP 7 ^ 2 - 3) := Real.sqrt_pos.mpr h3
    have hgoal : 2 / Real.sqrt 3 < lambdaP 7 := by
      rw [div_lt_iff₀ hrt3]
      have hlo := (lambdaP_bounds h7le).1
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hfactor : Real.sqrt (lambdaP 7 ^ 2 - 3) / Real.sqrt (4 - lambdaP 7 ^ 2) / (Real.sqrt 3 / 2) =
        (2 / Real.sqrt 3) * (Real.sqrt (lambdaP 7 ^ 2 - 3) / Real.sqrt (4 - lambdaP 7 ^ 2)) := by
      ring
    rw [hfactor]
    have hrhs : lambdaP 7 * Real.sqrt (lambdaP 7 ^ 2 - 3) / Real.sqrt (4 - lambdaP 7 ^ 2) =
        lambdaP 7 * (Real.sqrt (lambdaP 7 ^ 2 - 3) / Real.sqrt (4 - lambdaP 7 ^ 2)) := by ring
    rw [hrhs]
    exact mul_lt_mul_of_pos_right hgoal (div_pos hrt_lam3 hrt4)
  have h3 : h7 < 2 * r7 := by simpa [h7, r7] using hP_lt_two_rP h7le
  exact ⟨h1, h2, h3⟩

/-- **Corollary 1.2 intermediate ordering**: `ρ7 < r7 < Rc7 < h7 < 2 * r7`. -/
theorem cor_1_2_step_order_chain :
    ρ7 < r7 ∧ r7 < Rc7 ∧ Rc7 < h7 ∧ h7 < 2 * r7 := by
  obtain ⟨h1, h2, h3⟩ := eq_2_order
  have hid := prop_3_1_exact_identity
  exact ⟨by linarith, h1, h2, h3⟩

/-- **Section 2.1 properties of `β7` and `ρ7`**. -/
theorem text_2_beta_properties :
    (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 =
      Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) ∧
    Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) = Real.cos α7 ∧
    StrictAntiOn β7 (Set.Ioc 0 (2 * r7)) ∧
    Tendsto β7 (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) ∧
    β7 (2 * r7) = α7 ∧
    (∀ ρ ∈ Set.Ioo 0 (2 * r7), α7 < β7 ρ) ∧
    0 < ρ7 ∧ ρ7 < 2 * r7 ∧ β7 ρ7 = 3 * α7 / 2 := by
  have h7le : 7 ≤ 7 := le_refl 7
  have hr_pos : 0 < r7 := r7_pos
  have hsh2r : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith)
  have hch2r : 0 < Real.cosh (2 * r7) := Real.cosh_pos _
  have hcoth_pos : 0 < Real.cosh (2 * r7) / Real.sinh (2 * r7) := div_pos hch2r hsh2r
  -- (1) coth(2r) * tanh(r) = cosh(2r) / (cosh(2r) + 1)
  have h1 : (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 =
      Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) := by
    have hchr : 0 < Real.cosh r7 := Real.cosh_pos _
    have hshr : 0 < Real.sinh r7 := Real.sinh_pos_iff.mpr hr_pos
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, cosh_two_mul']
    have hden : 2 * Real.cosh r7 ^ 2 - 1 + 1 = 2 * Real.cosh r7 ^ 2 := by ring
    rw [hden]
    field_simp [hshr.ne', hchr.ne']
  -- (2) cosh(2r) / (cosh(2r) + 1) = cos α7
  have h2 : Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) = Real.cos α7 := by
    have hca : Real.cosh (2 * r7) = Real.cos α7 / (1 - Real.cos α7) := eq_1_consts.2.2.1
    have h1m : 0 < 1 - Real.cos α7 := by
      have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
      have hα_lt : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
      have : Real.cos α7 < 1 := by
        rw [← Real.cos_zero]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hα_lt.le hα_pos
      linarith
    rw [hca]
    field_simp [h1m.ne']
    ring
  -- Helper: on (0, 2r], the argument of arccos lies in (0, cos α7] ⊂ [-1, 1]
  have harg_mem : ∀ ρ ∈ Set.Ioc 0 (2 * r7),
      (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro ρ ⟨hρ0, hρ2⟩
    have ht_pos : 0 < Real.tanh (ρ / 2) := tanh_pos_of_pos (by linarith)
    have ht_le : Real.tanh (ρ / 2) ≤ Real.tanh r7 := strictMono_tanh.monotone (by linarith)
    have hmul_le : (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) ≤ Real.cos α7 := by
      calc (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2)
          ≤ (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 :=
            mul_le_mul_of_nonneg_left ht_le hcoth_pos.le
        _ = Real.cos α7 := h1.trans h2
    constructor
    · linarith [mul_pos hcoth_pos ht_pos]
    · exact le_trans hmul_le (Real.cos_le_one _)
  -- (3) StrictAntiOn β7 (Ioc 0 (2r))
  have h3 : StrictAntiOn β7 (Set.Ioc 0 (2 * r7)) := by
    intro x hx y hy hxy
    unfold β7 betaP
    show Real.arccos ((Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (y / 2)) <
         Real.arccos ((Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (x / 2))
    apply Real.strictAntiOn_arccos (harg_mem x hx) (harg_mem y hy)
    apply mul_lt_mul_of_pos_left _ hcoth_pos
    exact strictMono_tanh (by linarith)
  -- (4) Tendsto β7 (nhdsWithin 0 (Ioi 0)) (nhds (π/2))
  have h4 : Tendsto β7 (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have hcont : Continuous β7 := by
      unfold β7 betaP
      exact Real.continuous_arccos.comp
        (continuous_const.mul (continuous_tanh.comp (continuous_id.div_const 2)))
    have h0 : β7 0 = Real.pi / 2 := by
      unfold β7 betaP
      simp [Real.tanh_zero, Real.arccos_zero]
    rw [← h0]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- (5) β7 (2 * r7) = α7
  have h5 : β7 (2 * r7) = α7 := by
    unfold β7 betaP
    have hhalf : 2 * r7 / 2 = r7 := by ring
    change Real.arccos ((Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (2 * r7 / 2)) = α7
    rw [hhalf, h1, h2]
    apply Real.arccos_cos
    · unfold α7 alphaP; positivity
    · unfold α7 alphaP; linarith [Real.pi_pos]
  -- (6) ∀ ρ ∈ Ioo 0 (2r), α7 < β7 ρ
  have h6 : ∀ ρ ∈ Set.Ioo 0 (2 * r7), α7 < β7 ρ := by
    intro ρ ⟨hρ0, hρ2⟩
    rw [← h5]
    exact h3 ⟨hρ0, hρ2.le⟩ ⟨by linarith, le_refl _⟩ hρ2
  -- (7)-(9) 0 < ρ7, ρ7 < 2r7, β7 ρ7 = 3α7/2
  have h7_pos : 0 < ρ7 := by simpa [ρ7] using rhoStarP_pos h7le
  have h8_lt : ρ7 < 2 * r7 := by
    obtain ⟨hρr, _, _, _⟩ := cor_1_2_step_order_chain
    linarith
  have h9 : β7 ρ7 = 3 * α7 / 2 := by
    unfold β7 betaP ρ7 rhoStarP
    have hhalf : 2 * Real.artanh (Real.tanh (2 * rP 7) * Real.cos (3 * Real.pi / (7 : ℕ))) / 2 =
        Real.artanh (Real.tanh (2 * rP 7) * Real.cos (3 * Real.pi / (7 : ℕ))) := by ring
    rw [hhalf, Real.tanh_artanh]
    · have hcancel : (Real.cosh (2 * rP 7) / Real.sinh (2 * rP 7)) * Real.tanh (2 * rP 7) = 1 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        have hch : Real.cosh (2 * rP 7) ≠ 0 := (Real.cosh_pos _).ne'
        have hsh : Real.sinh (2 * rP 7) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith [rP_pos h7le])).ne'
        field_simp [hch, hsh]
      rw [← mul_assoc, hcancel, one_mul]
      have h3a : 3 * Real.pi / ((7 : ℕ) : ℝ) = 3 * α7 / 2 := by
        unfold α7 alphaP; norm_num; ring
      rw [h3a]
      apply Real.arccos_cos
      · unfold α7 alphaP; positivity
      · unfold α7 alphaP; linarith [Real.pi_pos]
    · exact ⟨by linarith [tanh_two_rP_mul_cos_three_pos h7le], tanh_two_rP_mul_cos_three_lt_one h7le⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7_pos, h8_lt, h9⟩

/-! ### Hyperboloid polar helper lemmas and Equation (5) (Tip distances) -/

/-- Lorentz pairing of two points in polar coordinates about the origin: the hyperbolic law of cosines. -/
lemma lorentz_polarOrigin (ρ₁ θ₁ ρ₂ θ₂ : ℝ) :
    H2.lorentz (H2.polarOrigin ρ₁ θ₁) (H2.polarOrigin ρ₂ θ₂) =
      Real.cosh ρ₁ * Real.cosh ρ₂ - Real.sinh ρ₁ * Real.sinh ρ₂ * Real.cos (θ₁ - θ₂) := by
  unfold H2.lorentz H2.polarOrigin
  dsimp
  rw [Real.cos_sub]
  ring

/-- Distance from `origin` to `polarOrigin ρ θ` is `ρ` (for `0 ≤ ρ`). -/
lemma dist_origin_polarOrigin (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    dist H2.origin (H2.polarOrigin ρ θ) = ρ := by
  rw [H2.dist_eq_arcosh]
  have hl : H2.lorentz H2.origin (H2.polarOrigin ρ θ) = Real.cosh ρ := by
    unfold H2.lorentz H2.origin H2.polarOrigin; dsimp; ring
  rw [hl, Real.arcosh_cosh hρ]

/-- Midpoint of `polarOrigin (2 * r7) φ` and `polarOrigin (2 * r7) (φ + α7)`
    sits at `polarOrigin h7 (φ + α7 / 2)`. -/
lemma mid_polarOrigin_consec (φ : ℝ) :
    H2.mid (H2.polarOrigin (2 * r7) φ) (H2.polarOrigin (2 * r7) (φ + α7)) =
      H2.polarOrigin h7 (φ + α7 / 2) := by
  have h7le : 7 ≤ 7 := le_refl 7
  have hlr : H2.lorentz (H2.polarOrigin (2 * r7) φ) (H2.polarOrigin (2 * r7) (φ + α7)) =
      Real.cosh (2 * r7) := by
    rw [lorentz_polarOrigin]
    have hsub : φ - (φ + α7) = -α7 := by ring
    rw [hsub, Real.cos_neg]
    have hca : Real.cos α7 = Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) :=
      text_2_beta_properties.2.1.symm
    rw [hca]
    have hsh2 : Real.sinh (2 * r7) ^ 2 = Real.cosh (2 * r7) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (2 * r7)]
    have hden : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
    have hmul : Real.sinh (2 * r7) * Real.sinh (2 * r7) = Real.cosh (2 * r7) ^ 2 - 1 := by
      linarith [hsh2, sq (Real.sinh (2 * r7))]
    field_simp [hden.ne']
    nlinarith [hmul]
  have hdenom : Real.sqrt (2 * (Real.cosh (2 * r7) + 1)) = 2 * Real.cosh r7 := by
    have hcr : 0 ≤ 2 * Real.cosh r7 := by linarith [Real.cosh_pos r7]
    rw [← Real.sqrt_sq hcr]
    congr 1
    rw [cosh_two_mul']
    ring
  have hcr_pos : 0 < Real.cosh r7 := Real.cosh_pos r7
  have hcos_half : Real.cos (α7 / 2) = Real.sinh h7 / Real.sinh (2 * r7) * Real.cosh r7 := by
    have hα2 : α7 / 2 = Real.pi / 7 := by unfold α7 alphaP; ring
    rw [hα2]
    have hsq : 0 < 4 - lambdaP 7 ^ 2 := by linarith [(lambdaP_sq_bounds h7le).2]
    have h3 : 0 < lambdaP 7 ^ 2 - 3 := by linarith [(lambdaP_sq_bounds h7le).1]
    have hrt4 : 0 < Real.sqrt (4 - lambdaP 7 ^ 2) := Real.sqrt_pos.mpr hsq
    have hrt3 : 0 < Real.sqrt (lambdaP 7 ^ 2 - 3) := Real.sqrt_pos.mpr h3
    rw [show h7 = hP 7 from rfl, show r7 = rP 7 from rfl,
        sinh_hP_lambda h7le, sinh_two_rP_lambda h7le, cosh_rP_lambda h7le]
    have hlam : Real.cos (Real.pi / 7) = lambdaP 7 / 2 := by
      unfold lambdaP; norm_num
    rw [hlam]
    have hmul4 : Real.sqrt (4 - lambdaP 7 ^ 2) * Real.sqrt (4 - lambdaP 7 ^ 2) = 4 - lambdaP 7 ^ 2 :=
      Real.mul_self_sqrt hsq.le
    field_simp [hsq.ne', hrt4.ne', hrt3.ne']
    rw [Real.sq_sqrt hsq.le]
  have hsin_sum : Real.sin φ + Real.sin (φ + α7) = 2 * Real.sin (φ + α7 / 2) * Real.cos (α7 / 2) := by
    have h1 := Real.sin_sub (φ + α7 / 2) (α7 / 2)
    have h2 := Real.sin_add (φ + α7 / 2) (α7 / 2)
    have ha : φ + α7 / 2 - α7 / 2 = φ := by ring
    have hb : φ + α7 / 2 + α7 / 2 = φ + α7 := by ring
    rw [ha] at h1; rw [hb] at h2; linarith
  have hcos_sum : Real.cos φ + Real.cos (φ + α7) = 2 * Real.cos (φ + α7 / 2) * Real.cos (α7 / 2) := by
    have h1 := Real.cos_sub (φ + α7 / 2) (α7 / 2)
    have h2 := Real.cos_add (φ + α7 / 2) (α7 / 2)
    have ha : φ + α7 / 2 - α7 / 2 = φ := by ring
    have hb : φ + α7 / 2 + α7 / 2 = φ + α7 := by ring
    rw [ha] at h1; rw [hb] at h2; linarith
  have hsh2_ne : Real.sinh (2 * r7) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith [r7_pos])).ne'
  ext
  · dsimp only [H2.mid]
    rw [hlr, hdenom]
    dsimp only [H2.polarOrigin]
    have hx : Real.sinh (2 * r7) * Real.cos φ + Real.sinh (2 * r7) * Real.cos (φ + α7) =
        Real.sinh (2 * r7) * (Real.cos φ + Real.cos (φ + α7)) := by ring
    rw [hx, hcos_sum, hcos_half]
    field_simp [hcr_pos.ne', hsh2_ne]
  · dsimp only [H2.mid]
    rw [hlr, hdenom]
    dsimp only [H2.polarOrigin]
    have hy : Real.sinh (2 * r7) * Real.sin φ + Real.sinh (2 * r7) * Real.sin (φ + α7) =
        Real.sinh (2 * r7) * (Real.sin φ + Real.sin (φ + α7)) := by ring
    rw [hy, hsin_sum, hcos_half]
    field_simp [hcr_pos.ne', hsh2_ne]
  · dsimp only [H2.mid]
    rw [hlr, hdenom]
    dsimp only [H2.polarOrigin]
    rw [eq_1_consts.2.2.2.1]
    field_simp [hcr_pos.ne']
    ring

/-- Linearity of `lorentz` with respect to `H2.mid`. -/
lemma lorentz_mid_right (m a b : H2) :
    H2.lorentz m (H2.mid a b) =
      (H2.lorentz m a + H2.lorentz m b) / Real.sqrt (2 * (H2.lorentz a b + 1)) := by
  change m.z * ((a.z + b.z) / Real.sqrt (2 * (H2.lorentz a b + 1)))
    - m.x * ((a.x + b.x) / Real.sqrt (2 * (H2.lorentz a b + 1)))
    - m.y * ((a.y + b.y) / Real.sqrt (2 * (H2.lorentz a b + 1))) =
    ((m.z * a.z - m.x * a.x - m.y * a.y) + (m.z * b.z - m.x * b.x - m.y * b.y)) /
      Real.sqrt (2 * (H2.lorentz a b + 1))
  ring

/-- Midpoint commutes with every isometry `φ : H2 ≃ᵢ H2`. -/
lemma isometry_mid (φ : H2 ≃ᵢ H2) (p q : H2) :
    φ (H2.mid p q) = H2.mid (φ p) (φ q) := by
  have hl_eq : ∀ a b : H2, H2.lorentz (φ a) (φ b) = H2.lorentz a b := by
    intro a b
    rw [← H2.cosh_dist, ← H2.cosh_dist, φ.dist_eq]
  have hmid_lorentz : ∀ a b : H2,
      H2.lorentz (H2.mid a b) a = Real.sqrt ((H2.lorentz a b + 1) / 2) ∧
      H2.lorentz (H2.mid a b) b = Real.sqrt ((H2.lorentz a b + 1) / 2) := by
    intro a b
    have hpos : 0 < H2.lorentz a b + 1 := by linarith [H2.one_le_lorentz a b]
    have h2pos : 0 < 2 * (H2.lorentz a b + 1) := by linarith
    have hval : (H2.lorentz a b + 1) / Real.sqrt (2 * (H2.lorentz a b + 1)) =
        Real.sqrt ((H2.lorentz a b + 1) / 2) := by
      have hlhs_pos : 0 ≤ (H2.lorentz a b + 1) / Real.sqrt (2 * (H2.lorentz a b + 1)) := by
        positivity
      rw [← Real.sqrt_sq hlhs_pos]
      congr 1
      rw [div_pow, Real.sq_sqrt h2pos.le]
      field_simp [hpos.ne']
    constructor
    · rw [H2.lorentz_symm, lorentz_mid_right, H2.lorentz_self, H2.lorentz_symm a b, add_comm, H2.lorentz_symm b a]
      exact hval
    · rw [H2.lorentz_symm, lorentz_mid_right, H2.lorentz_self, H2.lorentz_symm b a]
      exact hval
  rw [← H2.lorentz_eq_one_iff]
  rw [lorentz_mid_right, hl_eq, hl_eq, hl_eq, (hmid_lorentz p q).1, (hmid_lorentz p q).2]
  have hpos : 0 < H2.lorentz p q + 1 := by linarith [H2.one_le_lorentz p q]
  have h2pos : 0 < 2 * (H2.lorentz p q + 1) := by linarith
  have hnum : 2 * Real.sqrt ((H2.lorentz p q + 1) / 2) = Real.sqrt (2 * (H2.lorentz p q + 1)) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 * Real.sqrt ((H2.lorentz p q + 1) / 2) by positivity)]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← two_mul, hnum, div_self (Real.sqrt_pos.mpr h2pos).ne']

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
    Real.arcosh (Real.cosh r7 ^ 2) < 2 * r7 := by
  dsimp only
  have hM : H2.mid (F.nbr 1) (F.nbr 2) = F.polar h7 (3 * α7 / 2) := by
    unfold SiteFrame.nbr SiteFrame.polar
    rw [← isometry_mid]
    congr 1
    have h1 : ((1 : ℤ) : ℝ) * α7 = α7 := by norm_num
    have h2 : ((2 : ℤ) : ℝ) * α7 = α7 + α7 := by norm_num; ring
    have h3 : α7 + α7 / 2 = 3 * α7 / 2 := by ring
    rw [h1, h2, ← h3]
    exact mid_polarOrigin_consec α7
  have hTM : dist F.tip12 (H2.mid (F.nbr 1) (F.nbr 2)) = r7 := by
    rw [hM]
    unfold SiteFrame.tip12 SiteFrame.polar
    rw [F.φ.dist_eq, H2.dist_eq_arcosh, lorentz_polarOrigin]
    have hsub : 3 * α7 / 2 - 3 * α7 / 2 = 0 := by ring
    rw [hsub, Real.cos_zero, mul_one, ← Real.cosh_sub]
    have hhr : h7 - ρ7 = r7 := by linarith [prop_3_1_exact_identity]
    rw [show ρ7 - h7 = -(h7 - ρ7) by ring, Real.cosh_neg, hhr, Real.arcosh_cosh r7_pos.le]
  have hβρ : Real.cos (3 * α7 / 2) =
      (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ7 / 2) := by
    have hβ := text_2_beta_properties.2.2.2.2.2.2.2.2
    rw [← hβ]
    unfold β7 betaP
    have harg : (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ7 / 2) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hpos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
      have hlt : ρ7 < 2 * r7 := text_2_beta_properties.2.2.2.2.2.2.2.1
      have hsh2 : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
      have hcoth : 0 < Real.cosh (2 * r7) / Real.sinh (2 * r7) := div_pos (Real.cosh_pos _) hsh2
      have ht_pos : 0 < Real.tanh (ρ7 / 2) := tanh_pos_of_pos (by linarith)
      have ht_le : Real.tanh (ρ7 / 2) ≤ Real.tanh r7 := strictMono_tanh.monotone (by linarith)
      constructor
      · linarith [mul_pos hcoth ht_pos]
      · calc (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ7 / 2)
            ≤ (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 :=
              mul_le_mul_of_nonneg_left ht_le hcoth.le
          _ = Real.cos α7 := text_2_beta_properties.1.trans text_2_beta_properties.2.1
          _ ≤ 1 := Real.cos_le_one _
    exact Real.cos_arccos harg.1 harg.2
  have hl_2r : ∀ φ : ℝ, Real.cos (3 * α7 / 2 - φ) = Real.cos (3 * α7 / 2) →
      dist (H2.polarOrigin ρ7 (3 * α7 / 2)) (H2.polarOrigin (2 * r7) φ) = 2 * r7 := by
    intro φ hcos
    rw [H2.dist_eq_arcosh, lorentz_polarOrigin, hcos, hβρ]
    have hsh2 : Real.sinh (2 * r7) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith [r7_pos])).ne'
    have hch_half : Real.cosh (ρ7 / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hsimp : Real.cosh ρ7 * Real.cosh (2 * r7) -
        Real.sinh ρ7 * Real.sinh (2 * r7) *
          ((Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ7 / 2)) =
        Real.cosh (2 * r7) := by
      have hρ : ρ7 = 2 * (ρ7 / 2) := by ring
      rw [Real.tanh_eq_sinh_div_cosh]
      conv_lhs => rw [hρ, cosh_two_mul', Real.sinh_two_mul]
      field_simp [hsh2, hch_half]
      have hch_sh := Real.cosh_sq_sub_sinh_sq (ρ7 / 2)
      nlinarith
    rw [hsimp, Real.arcosh_cosh (by linarith [r7_pos])]
  -- Clean 4-line hyperbolic Pythagorean proof for dist(T, n₁) = dist(T, n₂) = arcosh(cosh² r7)
  have hln1_eq_n2 : H2.lorentz F.tip12 (F.nbr 1) = H2.lorentz F.tip12 (F.nbr 2) := by
    rw [← H2.cosh_dist, ← H2.cosh_dist]
    congr 1
    unfold SiteFrame.tip12 SiteFrame.polar SiteFrame.nbr
    rw [F.φ.dist_eq, F.φ.dist_eq, H2.dist_eq_arcosh, H2.dist_eq_arcosh,
        lorentz_polarOrigin, lorentz_polarOrigin]
    have h1 : 3 * α7 / 2 - ((1 : ℤ) : ℝ) * α7 = α7 / 2 := by norm_num; ring
    have h2 : 3 * α7 / 2 - ((2 : ℤ) : ℝ) * α7 = -(α7 / 2) := by norm_num; ring
    rw [h1, h2, Real.cos_neg]
  have hln1n2 : H2.lorentz (F.nbr 1) (F.nbr 2) = Real.cosh (2 * r7) := by
    rw [← H2.cosh_dist]
    unfold SiteFrame.nbr
    rw [F.φ.dist_eq, H2.cosh_dist, lorentz_polarOrigin]
    have hsub : ((1 : ℤ) : ℝ) * α7 - ((2 : ℤ) : ℝ) * α7 = -α7 := by norm_num; ring
    rw [hsub, Real.cos_neg, ← text_2_beta_properties.2.1]
    have hsh2 : Real.sinh (2 * r7) * Real.sinh (2 * r7) = Real.cosh (2 * r7) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (2 * r7), sq (Real.sinh (2 * r7))]
    have hden : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
    field_simp [hden.ne']
    nlinarith [hsh2]
  have hln_val : H2.lorentz F.tip12 (F.nbr 1) = Real.cosh r7 ^ 2 := by
    have hlM : H2.lorentz F.tip12 (H2.mid (F.nbr 1) (F.nbr 2)) = Real.cosh r7 := by
      rw [← H2.cosh_dist, hTM]
    rw [lorentz_mid_right, hln1n2, ← hln1_eq_n2] at hlM
    have hdenom : Real.sqrt (2 * (Real.cosh (2 * r7) + 1)) = 2 * Real.cosh r7 := by
      have hcr : 0 ≤ 2 * Real.cosh r7 := by linarith [Real.cosh_pos r7]
      rw [← Real.sqrt_sq hcr]
      congr 1; rw [cosh_two_mul']; ring
    rw [hdenom] at hlM
    have hcr : 0 < Real.cosh r7 := Real.cosh_pos r7
    rw [div_eq_iff (by linarith : (2 * Real.cosh r7) ≠ 0)] at hlM
    nlinarith
  refine ⟨hTM, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SiteFrame.tip12 SiteFrame.polar SiteFrame.nbr
    rw [F.φ.dist_eq]
    apply hl_2r
    norm_num
  · unfold SiteFrame.tip12 SiteFrame.polar SiteFrame.nbr
    rw [F.φ.dist_eq]
    apply hl_2r
    have h : 3 * α7 / 2 - ((3 : ℤ) : ℝ) * α7 = -(3 * α7 / 2) := by norm_num; ring
    rw [h, Real.cos_neg]
  · rw [H2.dist_eq_arcosh, hln_val]
  · rw [H2.dist_eq_arcosh, ← hln1_eq_n2, hln_val]
  · rw [← Real.arcosh_cosh (by linarith [r7_pos] : 0 ≤ 2 * r7)]
    have hcr : 1 < Real.cosh r7 := Real.one_lt_cosh.mpr r7_pos.ne'
    rw [Real.arcosh_lt_arcosh (by nlinarith) (Real.cosh_pos _)]
    rw [cosh_two_mul']
    nlinarith

end FejesTothP7.Proofs
