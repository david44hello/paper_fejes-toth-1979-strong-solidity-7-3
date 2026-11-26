/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Defs.Tiling
import FejesTothP7.Proofs.H2Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Basic Properties of the `(2, 3, 7)` Reflection Group and Local Triangle Geometry

Proves:
1. Key trigonometric identities for `r7` and `α7 = 2π/7`.
2. Equilateral side-length identity `dist (polarOrigin (2*r7) θ) (polarOrigin (2*r7) (θ + α7)) = 2*r7`.
3. Action of `rot7 = R1_237.trans R2_237` and `halfTurn = R1_237.trans R3_237` in `Delta237`.
4. Half-space separation lemmas for outer edges of the zone-expansion fan (`tanh(2r) cos(π/7) > cos(3π/7)`).
-/

noncomputable section

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Trigonometric identities for `r7` and `α7` -/

lemma cosh_r7 : Real.cosh r7 = 1 / (2 * Real.sin (Real.pi / 7)) := by
  unfold r7 rP
  push_cast
  exact Real.cosh_arcosh one_lt_inv_two_sin_pi_div_seven.le

lemma cos_alpha7_eq : Real.cos α7 = 1 - 2 * Real.sin (Real.pi / 7) ^ 2 := by
  have h : α7 = 2 * (Real.pi / 7) := by unfold α7 alphaP; ring
  rw [h, Real.cos_two_mul']
  linarith [Real.cos_sq_add_sin_sq (Real.pi / 7)]

lemma cosh_two_r7_eq : Real.cosh (2 * r7) = 2 * Real.cosh r7 ^ 2 - 1 := by
  have h1 := Real.cosh_two_mul r7
  have h2 := Real.cosh_sq_sub_sinh_sq r7
  linarith

lemma cosh_two_r7_eq_cos_div :
    Real.cosh (2 * r7) = Real.cos α7 / (1 - Real.cos α7) := by
  have hsin_pos : 0 < Real.sin (Real.pi / 7) := sin_pi_div_seven_pos
  have h1 : 1 - Real.cos α7 = 2 * Real.sin (Real.pi / 7) ^ 2 := by
    rw [cos_alpha7_eq]; ring
  rw [cosh_two_r7_eq, cosh_r7, h1, cos_alpha7_eq]
  field_simp [hsin_pos.ne']

lemma cos_alpha7_eq_cosh_div :
    Real.cos α7 = Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) := by
  have hsin_pos : 0 < Real.sin (Real.pi / 7) := sin_pi_div_seven_pos
  have h1m : 0 < 1 - Real.cos α7 := by
    have h : 1 - Real.cos α7 = 2 * Real.sin (Real.pi / 7) ^ 2 := by rw [cos_alpha7_eq]; ring
    rw [h]; positivity
  have hch_pos : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
  rw [cosh_two_r7_eq_cos_div]
  field_simp [h1m.ne', hch_pos.ne']
  ring

/-- Crucial equilateral identity: `cosh(2r)² - sinh(2r)² cos α = cosh(2r)`. -/
lemma lorentz_equilateral_const :
    Real.cosh (2 * r7) ^ 2 - Real.sinh (2 * r7) ^ 2 * Real.cos α7 = Real.cosh (2 * r7) := by
  have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
  have hcos := cos_alpha7_eq_cosh_div
  have hpos : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
  rw [hcos]
  have hsh2 : Real.sinh (2 * r7) ^ 2 = Real.cosh (2 * r7) ^ 2 - 1 := by linarith
  rw [hsh2]
  field_simp [hpos.ne']
  ring

/-- Adjacent rays at distance `2 r7` separated by angle `± α7` lie at distance `2 r7`. -/
lemma dist_polarOrigin_adj (θ : ℝ) :
    dist (polarOrigin (2 * r7) θ) (polarOrigin (2 * r7) (θ + α7)) = 2 * r7 := by
  rw [dist_eq_arcosh, lorentz_polarOrigin]
  have hsub : θ - (θ + α7) = -α7 := by ring
  rw [hsub, Real.cos_neg]
  have heq : Real.cosh (2 * r7) * Real.cosh (2 * r7) -
      Real.sinh (2 * r7) * Real.sinh (2 * r7) * Real.cos α7 = Real.cosh (2 * r7) := by
    linear_combination lorentz_equilateral_const
  rw [heq, Real.arcosh_cosh (by linarith [r7_pos])]

lemma dist_polarOrigin_adj_sub (θ : ℝ) :
    dist (polarOrigin (2 * r7) θ) (polarOrigin (2 * r7) (θ - α7)) = 2 * r7 := by
  have h := dist_polarOrigin_adj (θ - α7)
  rw [sub_add_cancel, dist_comm] at h
  exact h

/-! ### Explicit generators `rot7` and `halfTurn` in `Delta237` -/

/-- Counterclockwise rotation by `α7 = 2π / 7` about `origin`. -/
def rot7 : H2 ≃ᵢ H2 := R1_237.trans R2_237

/-- Half-turn (`180°` rotation) around `mid(origin, polarOrigin (2 * r7) 0)`. -/
def halfTurn : H2 ≃ᵢ H2 := R1_237.trans R3_237

lemma R1_237_mem : R1_237 ∈ Delta237 :=
  Subgroup.subset_closure (by simp)

lemma R2_237_mem : R2_237 ∈ Delta237 :=
  Subgroup.subset_closure (by simp)

lemma R3_237_mem : R3_237 ∈ Delta237 :=
  Subgroup.subset_closure (by simp)

/-- Note: in `Equiv.Perm` / `H2 ≃ᵢ H2`, `(a * b) x = a (b x)` while `(b.trans a) x = a (b x)`. -/
lemma trans_eq_mul_rev (a b : H2 ≃ᵢ H2) : a.trans b = b * a := rfl

lemma rot7_mem : rot7 ∈ Delta237 :=
  Delta237.mul_mem R2_237_mem R1_237_mem

lemma halfTurn_mem : halfTurn ∈ Delta237 :=
  Delta237.mul_mem R3_237_mem R1_237_mem

lemma rot7_eq_rotOrigin : rot7 = rotOrigin α7 := by
  have hpt : ∀ p : H2, rot7 p = rotOrigin α7 p := by
    intro p
    rcases exists_polarOrigin p with ⟨θ, hp⟩
    rw [hp]
    simp only [rot7, R1_237, R2_237, reflRay, IsometryEquiv.trans_apply,
      reflXAxis_apply_polarOrigin, rotOrigin_apply_polarOrigin]
    congr 1; unfold α7 alphaP; ring
  ext p
  · exact congrArg H2.x (hpt p)
  · exact congrArg H2.y (hpt p)
  · exact congrArg H2.z (hpt p)

lemma rot7_apply_polarOrigin (ρ θ : ℝ) :
    rot7 (polarOrigin ρ θ) = polarOrigin ρ (θ + α7) := by
  rw [rot7_eq_rotOrigin, rotOrigin_apply_polarOrigin]

lemma rot7_inv_eq_rotOrigin : rot7⁻¹ = rotOrigin (-α7) := by
  have hpt : ∀ p : H2, (rot7⁻¹ : H2 ≃ᵢ H2) p = rotOrigin (-α7) p := by
    intro p
    rcases exists_polarOrigin p with ⟨θ, hp⟩
    have hmul : rot7 (rotOrigin (-α7) p) = p := by
      rw [hp, rotOrigin_apply_polarOrigin, rot7_apply_polarOrigin]
      congr 1; ring
    have h := congrArg (fun x => (rot7⁻¹ : H2 ≃ᵢ H2) x) hmul
    simpa using h.symm
  ext p
  · exact congrArg H2.x (hpt p)
  · exact congrArg H2.y (hpt p)
  · exact congrArg H2.z (hpt p)

lemma rot7_zpow_apply_polarOrigin (k : ℤ) (ρ θ : ℝ) :
    (rot7 ^ k) (polarOrigin ρ θ) = polarOrigin ρ (θ + (k : ℝ) * α7) := by
  revert θ
  induction k using Int.induction_on with
  | zero => intro θ; simp
  | succ n ih =>
    intro θ
    rw [zpow_add_one, IsometryEquiv.mul_apply, rot7_apply_polarOrigin, ih (θ + α7)]
    congr 1; push_cast; ring
  | pred n ih =>
    intro θ
    rw [zpow_sub_one, IsometryEquiv.mul_apply, rot7_inv_eq_rotOrigin, rotOrigin_apply_polarOrigin, ih (θ + -α7)]
    congr 1; push_cast; ring

/-- Exact closed-form coordinates of `R3_237 p = reflPerpX r7 p`. -/
lemma R3_237_coords (p : H2) :
    (R3_237 p).x = -p.x * Real.cosh (2 * r7) + p.z * Real.sinh (2 * r7) ∧
    (R3_237 p).y = p.y ∧
    (R3_237 p).z = -p.x * Real.sinh (2 * r7) + p.z * Real.cosh (2 * r7) := by
  have hsh2 : Real.sinh (2 * r7) = 2 * Real.sinh r7 * Real.cosh r7 := Real.sinh_two_mul r7
  have hch2 : Real.cosh (2 * r7) = Real.cosh r7 ^ 2 + Real.sinh r7 ^ 2 := Real.cosh_two_mul r7
  refine ⟨?_, ?_, ?_⟩
  · simp only [R3_237, reflPerpX, IsometryEquiv.trans_apply, boostX_x, boostX_z,
      reflXAxis_x, reflXAxis_z, rotOrigin_x, rotOrigin_z, Real.cos_pi, Real.sin_pi,
      Real.cosh_neg, Real.sinh_neg]
    rw [hch2, hsh2]; ring
  · simp only [R3_237, reflPerpX, IsometryEquiv.trans_apply, boostX_y,
      reflXAxis_y, rotOrigin_y, Real.cos_pi, Real.sin_pi]
    ring
  · simp only [R3_237, reflPerpX, IsometryEquiv.trans_apply, boostX_x, boostX_z,
      reflXAxis_x, reflXAxis_z, rotOrigin_x, rotOrigin_z, Real.cos_pi, Real.sin_pi,
      Real.cosh_neg, Real.sinh_neg]
    rw [hch2, hsh2]; ring

lemma halfTurn_coords (p : H2) :
    (halfTurn p).x = -p.x * Real.cosh (2 * r7) + p.z * Real.sinh (2 * r7) ∧
    (halfTurn p).y = -p.y ∧
    (halfTurn p).z = -p.x * Real.sinh (2 * r7) + p.z * Real.cosh (2 * r7) := by
  have h := R3_237_coords (R1_237 p)
  simpa [halfTurn, R1_237] using h

lemma halfTurn_origin : halfTurn origin = polarOrigin (2 * r7) 0 := by
  have h := halfTurn_coords origin
  ext
  · rw [h.1]; simp [origin, polarOrigin]
  · rw [h.2.1]; simp [origin, polarOrigin]
  · rw [h.2.2]; simp [origin, polarOrigin]

lemma halfTurn_polarOrigin_zero : halfTurn (polarOrigin (2 * r7) 0) = origin := by
  have h := halfTurn_coords (polarOrigin (2 * r7) 0)
  have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
  ext
  · rw [h.1]; simp [origin, polarOrigin]; ring
  · rw [h.2.1]; simp [origin, polarOrigin]
  · rw [h.2.2]; simp [origin, polarOrigin]; linarith

lemma halfTurn_polarOrigin_alpha7 :
    halfTurn (polarOrigin (2 * r7) α7) = polarOrigin (2 * r7) (-α7) := by
  have h := halfTurn_coords (polarOrigin (2 * r7) α7)
  have hcos := cos_alpha7_eq_cosh_div
  have hpos : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
  have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
  have h1 : -Real.sinh (2 * r7) * Real.cos α7 * Real.cosh (2 * r7) +
      Real.cosh (2 * r7) * Real.sinh (2 * r7) = Real.sinh (2 * r7) * Real.cos α7 := by
    rw [hcos]; field_simp [hpos.ne']; ring
  have h2 : -Real.sinh (2 * r7) * Real.cos α7 * Real.sinh (2 * r7) +
      Real.cosh (2 * r7) * Real.cosh (2 * r7) = Real.cosh (2 * r7) := by
    linear_combination lorentz_equilateral_const
  ext
  · rw [h.1]; simp only [polarOrigin, Real.cos_neg]; linarith
  · rw [h.2.1]; simp only [polarOrigin, Real.sin_neg]; ring
  · rw [h.2.2]; simp only [polarOrigin]; linarith

lemma halfTurn_polarOrigin_neg_alpha7 :
    halfTurn (polarOrigin (2 * r7) (-α7)) = polarOrigin (2 * r7) α7 := by
  have h := halfTurn_coords (polarOrigin (2 * r7) (-α7))
  have hcos := cos_alpha7_eq_cosh_div
  have hpos : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
  have h1 : -Real.sinh (2 * r7) * Real.cos α7 * Real.cosh (2 * r7) +
      Real.cosh (2 * r7) * Real.sinh (2 * r7) = Real.sinh (2 * r7) * Real.cos α7 := by
    rw [hcos]; field_simp [hpos.ne']; ring
  have h2 : -Real.sinh (2 * r7) * Real.cos α7 * Real.sinh (2 * r7) +
      Real.cosh (2 * r7) * Real.cosh (2 * r7) = Real.cosh (2 * r7) := by
    linear_combination lorentz_equilateral_const
  ext
  · rw [h.1]; simp only [polarOrigin, Real.cos_neg]; linarith
  · rw [h.2.1]; simp only [polarOrigin, Real.sin_neg]; ring
  · rw [h.2.2]; simp only [polarOrigin, Real.cos_neg]; linarith

lemma detH_halfTurn (p q r : H2) :
    detH (halfTurn p) (halfTurn q) (halfTurn r) = detH p q r := by
  have hR1 : ∀ a b c, detH (R1_237 a) (R1_237 b) (R1_237 c) = -detH a b c := detH_reflXAxis
  have hR3 : ∀ a b c, detH (R3_237 a) (R3_237 b) (R3_237 c) = -detH a b c := by
    intro a b c
    simp only [R3_237, reflPerpX, IsometryEquiv.trans_apply, detH_boostX, detH_reflXAxis, detH_rotOrigin]
  simp only [halfTurn, IsometryEquiv.trans_apply, hR3, hR1, neg_neg]

lemma detH_rot7 (p q r : H2) :
    detH (rot7 p) (rot7 q) (rot7 r) = detH p q r := by
  rw [rot7_eq_rotOrigin]; exact detH_rotOrigin α7 p q r

/-! ### Half-space separation for outer edges of the zone fan -/

lemma tanh_two_r7_gt_half : (1 / 2 : ℝ) < Real.sinh (2 * r7) / Real.cosh (2 * r7) := by
  have hpi : Real.pi < 3.15 := by linarith [Real.pi_lt_d2]
  have hsin_lt : Real.sin (Real.pi / 7) < 0.45 := by
    have h1 : Real.sin (Real.pi / 7) < Real.pi / 7 := Real.sin_lt (by positivity)
    linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 7) := sin_pi_div_seven_pos
  have hchr : (10 / 9 : ℝ) < Real.cosh r7 := by
    rw [cosh_r7, lt_div_iff₀ (by linarith : 0 < 2 * Real.sin (Real.pi / 7))]
    linarith
  have hch2r : (4 / 3 : ℝ) < Real.cosh (2 * r7) := by
    rw [cosh_two_r7_eq]
    nlinarith
  have hch2_pos : 0 < Real.cosh (2 * r7) := Real.cosh_pos _
  have hsh2_pos : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hch2_pos]
  have hsq : Real.cosh (2 * r7) ^ 2 < 4 * Real.sinh (2 * r7) ^ 2 := by
    have hc := Real.cosh_sq_sub_sinh_sq (2 * r7)
    nlinarith
  nlinarith

lemma cos_three_pi_div_seven_lt_quarter : Real.cos (3 * Real.pi / 7) < 1 / 4 := by
  have h : Real.cos (3 * Real.pi / 7) = Real.sin (Real.pi / 14) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1; ring
  rw [h]
  have h1 : Real.sin (Real.pi / 14) < Real.pi / 14 := Real.sin_lt (by positivity)
  have hpi : Real.pi < 3.15 := by linarith [Real.pi_lt_d2]
  linarith

lemma cos_pi_div_seven_gt_half : (1 / 2 : ℝ) < Real.cos (Real.pi / 7) := by
  rw [← Real.cos_pi_div_three]
  exact Real.strictAntiOn_cos ⟨by positivity, by linarith [Real.pi_pos]⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])

/-- **Outer-edge half-space separation (Kind A)**:
    For `a = polarOrigin (2*r7) (-2*α7)` and `w = polarOrigin (2*r7) (-α7)`,
    EVERY point `y ∈ H2` with `0 ≤ y.y` (the entire upper half-plane `H^+(origin, polarOrigin (2*r7) 0)`)
    lies strictly on the positive side of `a → w` (`0 < detH a w y`)! -/
theorem detH_outer_edge_A_pos (y : H2) (hy : 0 ≤ y.y) :
    0 < detH (polarOrigin (2 * r7) (-(2 * α7))) (polarOrigin (2 * r7) (-α7)) y := by
  set a := polarOrigin (2 * r7) (-(2 * α7))
  set w := polarOrigin (2 * r7) (-α7)
  have hsh_pos : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hch_pos : 0 < Real.cosh (2 * r7) := Real.cosh_pos _
  -- Expand detH a w y = A * y.x + B * y.y + C * y.z
  have hexp : detH a w y =
      (-Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (2 * α7) - Real.sin α7)) * y.x +
      (Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos α7 - Real.cos (2 * α7))) * y.y +
      (Real.sinh (2 * r7) ^ 2 * Real.sin α7) * y.z := by
    unfold detH
    simp only [a, w, polarOrigin, Real.cos_neg, Real.sin_neg]
    have hsin_sub : Real.cos (2 * α7) * Real.sin α7 - Real.sin (2 * α7) * Real.cos α7 = -Real.sin α7 := by
      have := Real.sin_sub α7 (2 * α7)
      have h1 : α7 - 2 * α7 = -α7 := by ring
      rw [h1, Real.sin_neg] at this
      linarith
    linear_combination -Real.sinh (2 * r7) ^ 2 * y.z * hsin_sub
  rw [hexp]
  -- Check B > 0: cos α7 > cos (2 α7) since 0 < α7 < 2 α7 < π
  have hB : 0 ≤ Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos α7 - Real.cos (2 * α7)) := by
    have hcos : Real.cos (2 * α7) < Real.cos α7 := by
      apply Real.strictAntiOn_cos
      · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
      · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
      · unfold α7 alphaP; linarith [Real.pi_pos]
    have : 0 < Real.cos α7 - Real.cos (2 * α7) := by linarith
    positivity
  -- Check C > |A|:
  -- sin (2 α7) - sin α7 = 2 * cos (3π/7) * sin (π/7), sin α7 = 2 * sin (π/7) * cos (π/7)
  have hsin_diff : Real.sin (2 * α7) - Real.sin α7 = 2 * Real.cos (3 * Real.pi / 7) * Real.sin (Real.pi / 7) := by
    have h1 : 2 * α7 = 3 * Real.pi / 7 + Real.pi / 7 := by unfold α7 alphaP; ring
    have h2 : α7 = 3 * Real.pi / 7 - Real.pi / 7 := by unfold α7 alphaP; ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]; ring
  have hsin_a : Real.sin α7 = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
    have h : α7 = 2 * (Real.pi / 7) := by unfold α7 alphaP; ring
    rw [h, Real.sin_two_mul]
  have hcos3_pos : 0 < Real.cos (3 * Real.pi / 7) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin7_pos : 0 < Real.sin (Real.pi / 7) := sin_pi_div_seven_pos
  have hC_gt_A : Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (2 * α7) - Real.sin α7) <
      Real.sinh (2 * r7) ^ 2 * Real.sin α7 := by
    rw [hsin_diff, hsin_a]
    have h1 := tanh_two_r7_gt_half
    have h2 := cos_pi_div_seven_gt_half
    have h3 := cos_three_pi_div_seven_lt_quarter
    have h4 : Real.cosh (2 * r7) * Real.cos (3 * Real.pi / 7) < Real.sinh (2 * r7) * Real.cos (Real.pi / 7) := by
      have hsh_gt : Real.cosh (2 * r7) / 2 < Real.sinh (2 * r7) := by
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
        have := (lt_div_iff₀ hch_pos).mp h1
        linarith
      nlinarith
    have hfac : 0 < 2 * Real.sinh (2 * r7) * Real.sin (Real.pi / 7) := by positivity
    nlinarith
  have hA_pos : 0 < Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (2 * α7) - Real.sin α7) := by
    rw [hsin_diff]; positivity
  have hyx_lt : |y.x| < y.z := by
    rw [abs_lt]; constructor <;> nlinarith [y.on_sheet, y.hz]
  have hBy : 0 ≤ Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos α7 - Real.cos (2 * α7)) * y.y :=
    mul_nonneg hB hy
  have hxz : -(Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (2 * α7) - Real.sin α7)) * y.z ≤
      (-Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (2 * α7) - Real.sin α7)) * y.x := by
    have h1 := (abs_lt.mp hyx_lt).2
    nlinarith
  nlinarith [y.hz]

/-- **Outer-edge half-space separation (Kind B, middle edge of type-1 fan)**:
    For `b = polarOrigin (2*r7) (-3*α7)` and `a = polarOrigin (2*r7) (-2*α7)`,
    EVERY point `y ∈ H2` with `0 ≤ y.y` lies strictly on the positive side of `b → a` (`0 < detH b a y`)! -/
theorem detH_outer_edge_B_pos (y : H2) (hy : 0 ≤ y.y) :
    0 < detH (polarOrigin (2 * r7) (-(3 * α7))) (polarOrigin (2 * r7) (-(2 * α7))) y := by
  set b := polarOrigin (2 * r7) (-(3 * α7))
  set a := polarOrigin (2 * r7) (-(2 * α7))
  have hsh_pos : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hch_pos : 0 < Real.cosh (2 * r7) := Real.cosh_pos _
  have hexp : detH b a y =
      (-Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.sin (3 * α7) - Real.sin (2 * α7))) * y.x +
      (Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos (2 * α7) - Real.cos (3 * α7))) * y.y +
      (Real.sinh (2 * r7) ^ 2 * Real.sin α7) * y.z := by
    unfold detH
    simp only [b, a, polarOrigin, Real.cos_neg, Real.sin_neg]
    have hsin_sub : Real.cos (3 * α7) * Real.sin (2 * α7) - Real.sin (3 * α7) * Real.cos (2 * α7) =
        -Real.sin α7 := by
      have := Real.sin_sub (2 * α7) (3 * α7)
      have h1 : 2 * α7 - 3 * α7 = -α7 := by ring
      rw [h1, Real.sin_neg] at this
      linarith
    linear_combination -Real.sinh (2 * r7) ^ 2 * y.z * hsin_sub
  rw [hexp]
  -- Notice: cos (2α7) - cos (3α7) > 0 since 2α7 = 4π/7 < 6π/7 = 3α7 < π!
  have hB : 0 ≤ Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos (2 * α7) - Real.cos (3 * α7)) := by
    have hcos : Real.cos (3 * α7) < Real.cos (2 * α7) := by
      apply Real.strictAntiOn_cos
      · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
      · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
      · unfold α7 alphaP; linarith [Real.pi_pos]
    have : 0 < Real.cos (2 * α7) - Real.cos (3 * α7) := by linarith
    positivity
  -- And sin (3α7) - sin (2α7) = sin (π/7) - sin (3π/7) < 0, with |sin (3α7) - sin (2α7)| = 2 cos (5π/7) * ... = -2 cos(5π/7) sin(π/7)
  -- Actually: sin (2α7) - sin (3α7) = 2 * cos (2π/7) * sin (π/7) wait:
  -- 3α7 = 6π/7, 2α7 = 4π/7 => sin(6π/7) - sin(4π/7) = 2 cos(5π/7) sin(π/7) = -2 cos(2π/7) sin(π/7)!
  -- Wait: cos(2π/7) < cos(π/7), check tanh(2r) cos(π/7) > cos(2π/7)??
  -- Wait: cos(2π/7) ≈ 0.6235, tanh(2r) cos(π/7) = tanh h7 ≈ 0.7182! YES, 0.7182 > 0.6235!
  -- Wait: let's check simpler! At y with y.y ≥ 0, we ALSO know y.x vs y.z, OR prove C > |A| cleanly:
  -- Here |A| / C = coth(2r) * cos(2π/7) / cos(π/7) = 0.6235 / 0.7182 = 0.868 < 1!
  have hsin_diff : Real.sin (3 * α7) - Real.sin (2 * α7) =
      -(2 * Real.cos (2 * Real.pi / 7) * Real.sin (Real.pi / 7)) := by
    have h1 : 3 * α7 = 5 * Real.pi / 7 + Real.pi / 7 := by unfold α7 alphaP; ring
    have h2 : 2 * α7 = 5 * Real.pi / 7 - Real.pi / 7 := by unfold α7 alphaP; ring
    have h3 : Real.cos (5 * Real.pi / 7) = -Real.cos (2 * Real.pi / 7) := by
      have : 5 * Real.pi / 7 = Real.pi - 2 * Real.pi / 7 := by ring
      rw [this, Real.cos_pi_sub]
    rw [h1, h2, Real.sin_add, Real.sin_sub, h3]; ring
  have hsin_a : Real.sin α7 = 2 * Real.sin (Real.pi / 7) * Real.cos (Real.pi / 7) := by
    have h : α7 = 2 * (Real.pi / 7) := by unfold α7 alphaP; ring
    rw [h, Real.sin_two_mul]
  -- Exact algebraic check of sinh(2r) * cos(π/7) > cosh(2r) * cos(2π/7)!
  -- Notice: cos(2π/7) = cos α7 = cosh(2r) / (cosh(2r) + 1)!!
  -- So cosh(2r) * cos(2π/7) < sinh(2r) * cos(π/7)
  -- ⟺ cosh(2r)² / (cosh(2r) + 1) < sinh(2r) * cos(π/7)
  -- Square both sides (using sinh² = cosh² - 1, cos²(π/7) = (1 + cos α7)/2 = (2 cosh(2r) + 1)/(2(cosh(2r) + 1))):
  -- LHS² = c⁴ / (c + 1)²
  -- RHS² = (c² - 1) * (2c + 1) / (2(c + 1)) = (c - 1)(2c + 1) / 2
  -- Wait: 2 c⁴ < (c - 1)(2c + 1)(c + 1)²?
  -- Check at c = 1.655: 2 * 1.655⁴ = 15.00; (0.655)(4.31)(2.655)² = 19.90!! YES!!
  -- Factor: (c - 1)(2c + 1)(c + 1)² - 2 c⁴ = (2c² - c - 1)(c² + 2c + 1) - 2c⁴
  --       = (2c⁴ + 3c³ - c² - 3c - 1) - 2c⁴ = 3c³ - c² - 3c - 1!
  -- And for c > 4/3: 3c³ - c² - 3c - 1 > 3(64/27) - 16/9 - 4 - 1 = 64/9 - 16/9 - 45/9 = 3/9 = 1/3 > 0!!
  -- WHOA!! WHAT AN INSANE 5-LINE POLYNOMIAL PROOF!!
  have hc_gt : (4 / 3 : ℝ) < Real.cosh (2 * r7) := by
    have hpi : Real.pi < 3.15 := by linarith [Real.pi_lt_d2]
    have hsin_lt : Real.sin (Real.pi / 7) < 0.45 := by
      have h1 : Real.sin (Real.pi / 7) < Real.pi / 7 := Real.sin_lt (by positivity)
      linarith
    have hchr : (10 / 9 : ℝ) < Real.cosh r7 := by
      rw [cosh_r7, lt_div_iff₀ (by linarith [sin_pi_div_seven_pos] : 0 < 2 * Real.sin (Real.pi / 7))]
      linarith
    rw [cosh_two_r7_eq]; nlinarith
  have hcos_half_sq : Real.cos (Real.pi / 7) ^ 2 = (2 * Real.cosh (2 * r7) + 1) / (2 * (Real.cosh (2 * r7) + 1)) := by
    have h1 : Real.cos α7 = 2 * Real.cos (Real.pi / 7) ^ 2 - 1 := by
      have : α7 = 2 * (Real.pi / 7) := by unfold α7 alphaP; ring
      rw [this, Real.cos_two_mul]
    rw [cos_alpha7_eq_cosh_div] at h1
    have hpos : 0 < Real.cosh (2 * r7) + 1 := by linarith
    field_simp [hpos.ne'] at h1 ⊢
    linarith
  have hcos2_eq : Real.cos (2 * Real.pi / 7) = Real.cosh (2 * r7) / (Real.cosh (2 * r7) + 1) := by
    have : 2 * Real.pi / 7 = α7 := rfl
    rw [this, cos_alpha7_eq_cosh_div]
  have hineq : Real.cosh (2 * r7) * Real.cos (2 * Real.pi / 7) < Real.sinh (2 * r7) * Real.cos (Real.pi / 7) := by
    have hcos7_pos : 0 < Real.cos (Real.pi / 7) := by linarith [cos_pi_div_seven_gt_half]
    have hcos2_pos : 0 < Real.cos (2 * Real.pi / 7) := by
      rw [hcos2_eq]; positivity
    have hsq : (Real.cosh (2 * r7) * Real.cos (2 * Real.pi / 7)) ^ 2 <
        (Real.sinh (2 * r7) * Real.cos (Real.pi / 7)) ^ 2 := by
      rw [mul_pow, mul_pow, hcos2_eq, hcos_half_sq]
      have hsh2 : Real.sinh (2 * r7) ^ 2 = Real.cosh (2 * r7) ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (2 * r7)]
      rw [hsh2]
      set c := Real.cosh (2 * r7)
      have hc1 : 0 < c + 1 := by linarith
      rw [div_pow, ← mul_div_assoc, ← mul_div_assoc]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hpoly : (c ^ 2 - 1) * (2 * c + 1) * (c + 1) ^ 2 - c ^ 2 * c ^ 2 * (2 * (c + 1)) =
          (c + 1) * ((c - 4 / 3) * (3 * c ^ 2 + 3 * c + 1) + 1 / 3) := by ring
      have hpos_poly : 0 < (c + 1) * ((c - 4 / 3) * (3 * c ^ 2 + 3 * c + 1) + 1 / 3) := by
        have h1 : 0 < c - 4 / 3 := by linarith
        have h2 : 0 < 3 * c ^ 2 + 3 * c + 1 := by nlinarith
        positivity
      linarith
    have hpos1 : 0 < Real.cosh (2 * r7) * Real.cos (2 * Real.pi / 7) := by positivity
    have hpos2 : 0 < Real.sinh (2 * r7) * Real.cos (Real.pi / 7) := by positivity
    nlinarith
  have hC_gt_A : Real.sinh (2 * r7) * Real.cosh (2 * r7) * (2 * Real.cos (2 * Real.pi / 7) * Real.sin (Real.pi / 7)) <
      Real.sinh (2 * r7) ^ 2 * Real.sin α7 := by
    rw [hsin_a]
    have hfac : 0 < 2 * Real.sinh (2 * r7) * Real.sin (Real.pi / 7) := by
      have := sin_pi_div_seven_pos; positivity
    nlinarith
  have hA_pos : 0 < Real.sinh (2 * r7) * Real.cosh (2 * r7) * (2 * Real.cos (2 * Real.pi / 7) * Real.sin (Real.pi / 7)) := by
    have hcos2_pos : 0 < Real.cos (2 * Real.pi / 7) := by rw [hcos2_eq]; positivity
    have := sin_pi_div_seven_pos; positivity
  rw [hsin_diff]
  have hyx_lt : |y.x| < y.z := by
    rw [abs_lt]; constructor <;> nlinarith [y.on_sheet, y.hz]
  have hBy : 0 ≤ Real.sinh (2 * r7) * Real.cosh (2 * r7) * (Real.cos (2 * α7) - Real.cos (3 * α7)) * y.y :=
    mul_nonneg hB hy
  have hxz : -(Real.sinh (2 * r7) * Real.cosh (2 * r7) * (2 * Real.cos (2 * Real.pi / 7) * Real.sin (Real.pi / 7))) * y.z ≤
      (-Real.sinh (2 * r7) * Real.cosh (2 * r7) * -(2 * Real.cos (2 * Real.pi / 7) * Real.sin (Real.pi / 7))) * y.x := by
    have h1 := (abs_lt.mp hyx_lt).1
    nlinarith
  nlinarith [y.hz]

end FejesTothP7.Proofs
