module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Defs.H2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# Elementary Hyperbolic Geometry Toolkit on `H2`

Provides:
1. Polar coordinate identities and the exact Hyperbolic Law of Cosines.
2. Surjectivity of polar coordinates about `H2.origin` and isometry transitivities.
3. Classification of hyperbolic isometries `H2 ≃ᵢ H2` as `O⁺(2, 1)` (preserving `lorentz`,
   preserving `|detH|`, and uniquely determined by any three non-collinear points).
4. Exact geodesic interpolation `geodInterp`, strict quasiconvexity of `dist q ·` along geodesics,
   and midpoint properties (`mid`).
-/

noncomputable section

namespace FejesTothP7.H2

/-! ### Coordinate projections for basic isometries -/

@[simp] lemma reflXAxis_x (p : H2) : (reflXAxis p).x = p.x := rfl
@[simp] lemma reflXAxis_y (p : H2) : (reflXAxis p).y = -p.y := rfl
@[simp] lemma reflXAxis_z (p : H2) : (reflXAxis p).z = p.z := rfl

@[simp] lemma rotOrigin_x (φ : ℝ) (p : H2) :
    (rotOrigin φ p).x = p.x * Real.cos φ - p.y * Real.sin φ := rfl
@[simp] lemma rotOrigin_y (φ : ℝ) (p : H2) :
    (rotOrigin φ p).y = p.x * Real.sin φ + p.y * Real.cos φ := rfl
@[simp] lemma rotOrigin_z (φ : ℝ) (p : H2) : (rotOrigin φ p).z = p.z := rfl

@[simp] lemma boostX_x (t : ℝ) (p : H2) :
    (boostX t p).x = p.x * Real.cosh t + p.z * Real.sinh t := rfl
@[simp] lemma boostX_y (t : ℝ) (p : H2) : (boostX t p).y = p.y := rfl
@[simp] lemma boostX_z (t : ℝ) (p : H2) :
    (boostX t p).z = p.x * Real.sinh t + p.z * Real.cosh t := rfl

/-! ### Polar coordinates and Law of Cosines -/

/-- Hyperbolic Law of Cosines at the origin: exact identity for `lorentz`. -/
lemma lorentz_polarOrigin (ρ₁ θ₁ ρ₂ θ₂ : ℝ) :
    lorentz (polarOrigin ρ₁ θ₁) (polarOrigin ρ₂ θ₂) =
      Real.cosh ρ₁ * Real.cosh ρ₂ - Real.sinh ρ₁ * Real.sinh ρ₂ * Real.cos (θ₁ - θ₂) := by
  unfold lorentz polarOrigin
  rw [Real.cos_sub]
  ring

lemma lorentz_origin_polarOrigin (ρ θ : ℝ) :
    lorentz origin (polarOrigin ρ θ) = Real.cosh ρ := by
  simp [lorentz, origin, polarOrigin]

lemma dist_origin_polarOrigin (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    dist origin (polarOrigin ρ θ) = ρ := by
  rw [dist_eq_arcosh, lorentz_origin_polarOrigin, Real.arcosh_cosh hρ]

lemma dist_polarOrigin_origin (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    dist (polarOrigin ρ θ) origin = ρ := by
  rw [dist_comm, dist_origin_polarOrigin ρ θ hρ]

lemma polarOrigin_zero (θ : ℝ) : polarOrigin 0 θ = origin := by
  ext <;> simp [polarOrigin, origin]

lemma polarOrigin_add_two_pi (ρ θ : ℝ) :
    polarOrigin ρ (θ + 2 * Real.pi) = polarOrigin ρ θ := by
  ext <;> simp [polarOrigin, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma rotOrigin_apply_origin (φ : ℝ) : rotOrigin φ origin = origin := by
  ext <;> simp [origin]

lemma rotOrigin_apply_polarOrigin (φ ρ θ : ℝ) :
    rotOrigin φ (polarOrigin ρ θ) = polarOrigin ρ (θ + φ) := by
  ext
  · simp only [rotOrigin_x, polarOrigin]; rw [Real.cos_add]; ring
  · simp only [rotOrigin_y, polarOrigin]; rw [Real.sin_add]; ring
  · rfl

lemma reflXAxis_apply_origin : reflXAxis origin = origin := by
  ext <;> simp [origin]

lemma reflXAxis_apply_polarOrigin (ρ θ : ℝ) :
    reflXAxis (polarOrigin ρ θ) = polarOrigin ρ (-θ) := by
  ext <;> simp [polarOrigin]

lemma boostX_apply_origin (t : ℝ) : boostX t origin = polarOrigin t 0 := by
  ext <;> simp [origin, polarOrigin]

lemma boostX_apply_polarOrigin_zero (t s : ℝ) :
    boostX t (polarOrigin s 0) = polarOrigin (s + t) 0 := by
  ext
  · simp only [boostX_x, polarOrigin, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
    rw [Real.sinh_add]
  · simp [polarOrigin]
  · simp only [boostX_z, polarOrigin, Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
    rw [Real.cosh_add]; ring

lemma reflPerpX_apply_origin (d : ℝ) :
    reflPerpX d origin = polarOrigin (2 * d) 0 := by
  simp only [reflPerpX, IsometryEquiv.trans_apply, boostX_apply_origin]
  have h1 : rotOrigin Real.pi (polarOrigin (-d) 0) = polarOrigin (-d) Real.pi := by
    simpa using rotOrigin_apply_polarOrigin Real.pi (-d) 0
  rw [h1, reflXAxis_apply_polarOrigin]
  have h2 : polarOrigin (-d) (-Real.pi) = polarOrigin d 0 := by
    ext <;> simp [polarOrigin]
  rw [h2, boostX_apply_polarOrigin_zero]
  rw [two_mul]

/-- Every point `p : H2` admits polar coordinates `(dist origin p, θ)` about `origin`. -/
lemma exists_polarOrigin (p : H2) :
    ∃ θ : ℝ, p = polarOrigin (dist origin p) θ := by
  set ρ := dist origin p
  have hρ : 0 ≤ ρ := dist_nonneg
  have hch : Real.cosh ρ = p.z := by
    have := cosh_dist origin p
    change Real.cosh ρ = _ at this
    simpa [lorentz, origin] using this
  have hsh_sq : Real.sinh ρ ^ 2 = p.x ^ 2 + p.y ^ 2 := by
    have h1 := Real.cosh_sq_sub_sinh_sq ρ
    have h2 := p.on_sheet
    have h3 : Real.cosh ρ ^ 2 = p.z ^ 2 := by rw [hch]
    nlinarith
  by_cases hρ0 : ρ = 0
  · refine ⟨0, ?_⟩
    have hp : p = origin := eq_of_dist_eq_zero (by rwa [dist_comm])
    rw [hp, hρ0, polarOrigin_zero]
  · have hsh_pos : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr (lt_of_le_of_ne hρ (Ne.symm hρ0))
    set u := p.x / Real.sinh ρ
    set v := p.y / Real.sinh ρ
    have huv : u ^ 2 + v ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← hsh_sq, div_self (pow_ne_zero 2 hsh_pos.ne')]
    have hu_le : -1 ≤ u := by nlinarith [sq_nonneg v]
    have hu_ge : u ≤ 1 := by nlinarith [sq_nonneg v]
    by_cases hv : 0 ≤ v
    · refine ⟨Real.arccos u, ?_⟩
      ext
      · simp [polarOrigin, Real.cos_arccos hu_le hu_ge, u, mul_div_cancel₀ _ hsh_pos.ne']
      · simp only [polarOrigin, Real.sin_arccos]
        have hsq : Real.sqrt (1 - u ^ 2) = v := by
          rw [show 1 - u ^ 2 = v ^ 2 by linarith, Real.sqrt_sq hv]
        rw [hsq]
        simp [v, mul_div_cancel₀ _ hsh_pos.ne']
      · simp [polarOrigin, hch]
    · refine ⟨-Real.arccos u, ?_⟩
      ext
      · simp [polarOrigin, Real.cos_neg, Real.cos_arccos hu_le hu_ge, u, mul_div_cancel₀ _ hsh_pos.ne']
      · simp only [polarOrigin, Real.sin_neg, Real.sin_arccos]
        have hv' : 0 ≤ -v := by linarith
        have hsq : Real.sqrt (1 - u ^ 2) = -v := by
          rw [show 1 - u ^ 2 = (-v) ^ 2 by linarith, Real.sqrt_sq hv']
        rw [hsq]
        simp [v, mul_div_cancel₀ _ hsh_pos.ne']
      · simp [polarOrigin, hch]

/-! ### Isometry classification and `detH` invariance -/

/-- Every hyperbolic isometry preserves `lorentz`. -/
lemma isometry_lorentz (φ : H2 ≃ᵢ H2) (p q : H2) :
    lorentz (φ p) (φ q) = lorentz p q := by
  rw [← cosh_dist, ← cosh_dist, φ.dist_eq]

/-- `rotOrigin` preserves `detH`. -/
lemma detH_rotOrigin (φ : ℝ) (p q r : H2) :
    detH (rotOrigin φ p) (rotOrigin φ q) (rotOrigin φ r) = detH p q r := by
  unfold detH
  simp only [rotOrigin_x, rotOrigin_y, rotOrigin_z]
  have hcs := Real.cos_sq_add_sin_sq φ
  linear_combination
    (p.x * (q.y * r.z - q.z * r.y) - p.y * (q.x * r.z - q.z * r.x) + p.z * (q.x * r.y - q.y * r.x)) * hcs

/-- `boostX` preserves `detH`. -/
lemma detH_boostX (t : ℝ) (p q r : H2) :
    detH (boostX t p) (boostX t q) (boostX t r) = detH p q r := by
  unfold detH
  simp only [boostX_x, boostX_y, boostX_z]
  have hch := Real.cosh_sq_sub_sinh_sq t
  linear_combination
    (p.x * (q.y * r.z - q.z * r.y) - p.y * (q.x * r.z - q.z * r.x) + p.z * (q.x * r.y - q.y * r.x)) * hch

/-- `reflXAxis` negates `detH`. -/
lemma detH_reflXAxis (p q r : H2) :
    detH (reflXAxis p) (reflXAxis q) (reflXAxis r) = -detH p q r := by
  unfold detH
  simp only [reflXAxis_x, reflXAxis_y, reflXAxis_z]
  ring

/-- Helper: there is a direct (orientation-preserving) isometry moving `p` to `origin`. -/
lemma exists_direct_to_origin (p : H2) :
    ∃ g : H2 ≃ᵢ H2, g p = origin ∧ ∀ a b c : H2, detH (g a) (g b) (g c) = detH a b c := by
  rcases exists_polarOrigin p with ⟨θ, hp⟩
  set ρ := dist origin p
  refine ⟨(rotOrigin (-θ)).trans (boostX (-ρ)), ?_, ?_⟩
  · simp only [IsometryEquiv.trans_apply]
    rw [hp, rotOrigin_apply_polarOrigin, add_neg_cancel, boostX_apply_polarOrigin_zero,
      add_neg_cancel, polarOrigin_zero]
  · intro a b c
    simp only [IsometryEquiv.trans_apply, detH_boostX, detH_rotOrigin]

/-- Any isometry fixing `origin`, `polarOrigin 1 0`, and `polarOrigin 1 (π / 2)` is the identity. -/
lemma isometry_eq_refl_of_fix_basis (ψ : H2 ≃ᵢ H2)
    (h0 : ψ origin = origin)
    (h1 : ψ (polarOrigin 1 0) = polarOrigin 1 0)
    (h2 : ψ (polarOrigin 1 (Real.pi / 2)) = polarOrigin 1 (Real.pi / 2)) :
    ∀ p : H2, ψ p = p := by
  intro p
  have hz : (ψ p).z = p.z := by
    have h := isometry_lorentz ψ p origin
    rw [h0] at h
    simpa [lorentz, origin] using h
  have hsh1 : Real.sinh 1 ≠ 0 := (Real.sinh_pos_iff.mpr zero_lt_one).ne'
  have hx : (ψ p).x = p.x := by
    have h := isometry_lorentz ψ p (polarOrigin 1 0)
    rw [h1] at h
    simp only [lorentz, polarOrigin, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero] at h
    rw [hz] at h
    have hmul : (ψ p).x * Real.sinh 1 = p.x * Real.sinh 1 := by linarith
    exact mul_right_cancel₀ hsh1 hmul
  have hy : (ψ p).y = p.y := by
    have h := isometry_lorentz ψ p (polarOrigin 1 (Real.pi / 2))
    rw [h2] at h
    simp only [lorentz, polarOrigin, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_one, mul_zero,
      sub_zero] at h
    rw [hz] at h
    have hmul : (ψ p).y * Real.sinh 1 = p.y * Real.sinh 1 := by linarith
    exact mul_right_cancel₀ hsh1 hmul
  ext
  · exact hx
  · exact hy
  · exact hz

/-- Classification of hyperbolic isometries: every `φ : H2 ≃ᵢ H2` preserves `detH` up to a
    global sign `s ∈ {1, -1}` (orientation-preserving or orientation-reversing). -/
theorem isometry_detH_sign (φ : H2 ≃ᵢ H2) :
    (∀ p q r : H2, detH (φ p) (φ q) (φ r) = detH p q r) ∨
    (∀ p q r : H2, detH (φ p) (φ q) (φ r) = -detH p q r) := by
  rcases exists_direct_to_origin (φ origin) with ⟨g₁, hg₁_o, hg₁_det⟩
  set ψ₁ := φ.trans g₁
  have hψ₁_o : ψ₁ origin = origin := by simp [ψ₁, hg₁_o]
  set e₁ := polarOrigin 1 0
  set e₂ := polarOrigin 1 (Real.pi / 2)
  rcases exists_polarOrigin (ψ₁ e₁) with ⟨θ₁, hθ₁⟩
  have hd1 : dist origin (ψ₁ e₁) = 1 := by
    rw [← hψ₁_o, ψ₁.dist_eq, dist_origin_polarOrigin 1 0 zero_le_one]
  rw [hd1] at hθ₁
  set ψ₂ := ψ₁.trans (rotOrigin (-θ₁))
  have hψ₂_o : ψ₂ origin = origin := by
    simp [ψ₂, hψ₁_o, rotOrigin_apply_origin]
  have hψ₂_e1 : ψ₂ e₁ = e₁ := by
    simp only [ψ₂, IsometryEquiv.trans_apply]
    rw [hθ₁, rotOrigin_apply_polarOrigin, add_neg_cancel]
  have hz2 : (ψ₂ e₂).z = Real.cosh 1 := by
    have h := isometry_lorentz ψ₂ e₂ origin
    rw [hψ₂_o] at h
    simpa [lorentz, origin, e₂, polarOrigin] using h
  have hsh1 : Real.sinh 1 ≠ 0 := (Real.sinh_pos_iff.mpr zero_lt_one).ne'
  have hx2 : (ψ₂ e₂).x = 0 := by
    have h := isometry_lorentz ψ₂ e₂ e₁
    rw [hψ₂_e1] at h
    unfold lorentz at h
    have he1x : e₁.x = Real.sinh 1 := by simp [e₁, polarOrigin]
    have he1y : e₁.y = 0 := by simp [e₁, polarOrigin]
    have he1z : e₁.z = Real.cosh 1 := by simp [e₁, polarOrigin]
    have he2x : e₂.x = 0 := by simp [e₂, polarOrigin]
    have he2y : e₂.y = Real.sinh 1 := by simp [e₂, polarOrigin]
    have he2z : e₂.z = Real.cosh 1 := by simp [e₂, polarOrigin]
    rw [he1x, he1y, he1z, he2x, he2y, he2z, hz2] at h
    have hmul : (ψ₂ e₂).x * Real.sinh 1 = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_right hsh1
  have hy2_sq : (ψ₂ e₂).y ^ 2 = Real.sinh 1 ^ 2 := by
    have hs := (ψ₂ e₂).on_sheet
    have hch := Real.cosh_sq_sub_sinh_sq 1
    rw [hz2, hx2] at hs
    nlinarith
  have hy2_cases : (ψ₂ e₂).y = Real.sinh 1 ∨ (ψ₂ e₂).y = -Real.sinh 1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hy2_sq
  have hψ₂_det : ∀ p q r : H2, detH (ψ₂ p) (ψ₂ q) (ψ₂ r) = detH (φ p) (φ q) (φ r) := by
    intro p q r
    simp only [ψ₂, ψ₁, IsometryEquiv.trans_apply, detH_rotOrigin, hg₁_det]
  rcases hy2_cases with hy_pos | hy_neg
  · left
    have hψ₂_e2 : ψ₂ e₂ = e₂ := by
      ext
      · rw [hx2]; simp [e₂, polarOrigin]
      · rw [hy_pos]; simp [e₂, polarOrigin]
      · rw [hz2]; simp [e₂, polarOrigin]
    have hid := isometry_eq_refl_of_fix_basis ψ₂ hψ₂_o hψ₂_e1 hψ₂_e2
    intro p q r
    rw [← hψ₂_det p q r, hid p, hid q, hid r]
  · right
    set ψ₃ := ψ₂.trans reflXAxis
    have hψ₃_o : ψ₃ origin = origin := by simp [ψ₃, hψ₂_o, reflXAxis_apply_origin]
    have hψ₃_e1 : ψ₃ e₁ = e₁ := by
      simp only [ψ₃, IsometryEquiv.trans_apply, hψ₂_e1, e₁, reflXAxis_apply_polarOrigin, neg_zero]
    have hψ₃_e2 : ψ₃ e₂ = e₂ := by
      ext
      · change (ψ₂ e₂).x = e₂.x; rw [hx2]; simp [e₂, polarOrigin]
      · change -(ψ₂ e₂).y = e₂.y; rw [hy_neg]; simp [e₂, polarOrigin]
      · change (ψ₂ e₂).z = e₂.z; rw [hz2]; simp [e₂, polarOrigin]
    have hid := isometry_eq_refl_of_fix_basis ψ₃ hψ₃_o hψ₃_e1 hψ₃_e2
    intro p q r
    have h3 : detH (ψ₃ p) (ψ₃ q) (ψ₃ r) = -detH (φ p) (φ q) (φ r) := by
      simp only [ψ₃, IsometryEquiv.trans_apply, detH_reflXAxis, hψ₂_det]
    rw [hid p, hid q, hid r] at h3
    linarith

/-! ### Midpoint properties -/

lemma lorentz_mid_left (p q : H2) :
    lorentz p (mid p q) = Real.sqrt ((lorentz p q + 1) / 2) := by
  have hpos : 0 < 2 * (lorentz p q + 1) := by linarith [one_le_lorentz p q]
  have hsq : p.z * (p.z + q.z) - p.x * (p.x + q.x) - p.y * (p.y + q.y) = lorentz p q + 1 := by
    unfold lorentz; nlinarith [p.on_sheet]
  have hnum : lorentz p (mid p q) = (lorentz p q + 1) / Real.sqrt (2 * (lorentz p q + 1)) := by
    unfold lorentz mid
    dsimp only
    rw [← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc, ← sub_div, ← sub_div]
    congr 1
  rw [hnum]
  have hnonneg : 0 ≤ (lorentz p q + 1) / Real.sqrt (2 * (lorentz p q + 1)) :=
    div_nonneg (by linarith [one_le_lorentz p q]) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hnonneg, div_pow, Real.sq_sqrt hpos.le]
  congr 1; field_simp

lemma cosh_half_dist (p q : H2) :
    Real.cosh (dist p q / 2) = Real.sqrt ((lorentz p q + 1) / 2) := by
  have h1 := Real.cosh_two_mul (dist p q / 2)
  have h2 : 2 * (dist p q / 2) = dist p q := by ring
  rw [h2, cosh_dist] at h1
  have hc := Real.cosh_sq_sub_sinh_sq (dist p q / 2)
  have hsq : Real.cosh (dist p q / 2) ^ 2 = (lorentz p q + 1) / 2 := by linarith
  rw [← Real.sqrt_sq (Real.cosh_pos _).le, hsq]

lemma dist_mid_left (p q : H2) : dist p (mid p q) = dist p q / 2 := by
  rw [dist_eq_arcosh, lorentz_mid_left, ← cosh_half_dist, Real.arcosh_cosh (by positivity)]

lemma mid_comm (p q : H2) : mid p q = mid q p := by
  ext <;> simp [mid, add_comm, lorentz_symm]

lemma dist_mid_right (p q : H2) : dist (mid p q) q = dist p q / 2 := by
  rw [mid_comm, dist_comm, dist_mid_left, dist_comm]

/-- Uniqueness of hyperbolic midpoint: any `m` at distance `dist a b / 2` from both `a` and `b`
    equals `mid a b`. -/
lemma eq_mid_of_dist (a b m : H2) (hma : dist a m = dist a b / 2) (hmb : dist m b = dist a b / 2) :
    m = mid a b := by
  have hl_a : lorentz m a = Real.cosh (dist a b / 2) := by
    rw [lorentz_symm, ← cosh_dist, hma]
  have hl_b : lorentz m b = Real.cosh (dist a b / 2) := by
    rw [← cosh_dist, hmb]
  have hch_sq : 2 * Real.cosh (dist a b / 2) ^ 2 = lorentz a b + 1 := by
    have h1 := Real.cosh_two_mul (dist a b / 2)
    have h2 : 2 * (dist a b / 2) = dist a b := by ring
    rw [h2, cosh_dist] at h1
    have hc := Real.cosh_sq_sub_sinh_sq (dist a b / 2)
    linarith
  have hpos : 0 < 2 * (lorentz a b + 1) := by linarith [one_le_lorentz a b]
  have hl_m : lorentz m (mid a b) = 1 := by
    have hnum : lorentz m (mid a b) =
        (lorentz m a + lorentz m b) / Real.sqrt (2 * (lorentz a b + 1)) := by
      set s := Real.sqrt (2 * (lorentz a b + 1))
      change m.z * ((a.z + b.z) / s) - m.x * ((a.x + b.x) / s) - m.y * ((a.y + b.y) / s) =
        ((m.z * a.z - m.x * a.x - m.y * a.y) + (m.z * b.z - m.x * b.x - m.y * b.y)) / s
      ring
    rw [hnum, hl_a, hl_b, div_eq_one_iff_eq (Real.sqrt_pos.mpr hpos).ne']
    have h2c : 0 ≤ 2 * Real.cosh (dist a b / 2) := by positivity
    rw [show Real.cosh (dist a b / 2) + Real.cosh (dist a b / 2) = 2 * Real.cosh (dist a b / 2) by ring]
    rw [← Real.sqrt_sq h2c]
    congr 1; nlinarith
  exact (lorentz_eq_one_iff m (mid a b)).mp hl_m

/-- Any hyperbolic isometry maps `mid p q` to `mid (φ p) (φ q)`. -/
lemma isometry_mid (φ : H2 ≃ᵢ H2) (p q : H2) :
    φ (mid p q) = mid (φ p) (φ q) := by
  apply eq_mid_of_dist (φ p) (φ q) (φ (mid p q))
  · rw [φ.dist_eq, φ.dist_eq, dist_mid_left]
  · rw [φ.dist_eq, φ.dist_eq, dist_mid_right]

/-! ### Geodesic interpolation and strict quasiconvexity -/

/-- Geodesic interpolation `γ(t)` from `p` to `q` at arclength `t ∈ ℝ` (for `p ≠ q`). -/
def geodInterp (p q : H2) (hpq : p ≠ q) (t : ℝ) : H2 :=
  let L := dist p q
  have hL : 0 < L := dist_pos.mpr hpq
  have hshL : 0 < Real.sinh L := Real.sinh_pos_iff.mpr hL
  let a := Real.sinh (L - t) / Real.sinh L
  let b := Real.sinh t / Real.sinh L
  have h_id : a ^ 2 + b ^ 2 + 2 * a * b * Real.cosh L = 1 := by
    have h1 : Real.sinh (L - t) ^ 2 + Real.sinh t ^ 2 +
        2 * Real.sinh (L - t) * Real.sinh t * Real.cosh L = Real.sinh L ^ 2 := by
      set u := L - t
      have hL_eq : L = u + t := by ring
      rw [hL_eq, Real.sinh_add, Real.cosh_add]
      have hc1 := Real.cosh_sq_sub_sinh_sq u
      have hc2 := Real.cosh_sq_sub_sinh_sq t
      linear_combination -(Real.sinh u ^ 2) * hc2 - (Real.sinh t ^ 2) * hc1
    simp only [a, b]
    rw [div_pow, div_pow]
    field_simp [hshL.ne']
    linarith
  have hl_pq : p.z * q.z - p.x * q.x - p.y * q.y = Real.cosh L := (cosh_dist p q).symm
  have hsheet : (a * p.z + b * q.z) ^ 2 - (a * p.x + b * q.x) ^ 2 - (a * p.y + b * q.y) ^ 2 = 1 := by
    linear_combination a ^ 2 * p.on_sheet + b ^ 2 * q.on_sheet + 2 * a * b * hl_pq + h_id
  have hz_pos : 0 < a * p.z + b * q.z := by
    have hsq : 1 ≤ (a * p.z + b * q.z) ^ 2 := by nlinarith
    have hne : a * p.z + b * q.z ≠ 0 := by intro h0; rw [h0] at hsq; norm_num at hsq
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exfalso
      have hcosht : a + b * Real.cosh L = Real.cosh t := by
        simp only [a, b]
        rw [mul_comm, ← mul_div_assoc, ← add_div, div_eq_iff hshL.ne']
        set u := L - t
        have hL_eq : L = u + t := by ring
        rw [hL_eq, Real.cosh_add, Real.sinh_add]
        have hc := Real.cosh_sq_sub_sinh_sq t
        linear_combination -Real.sinh u * hc
      have hl_p : (a * p.z + b * q.z) * p.z - (a * p.x + b * q.x) * p.x - (a * p.y + b * q.y) * p.y =
          Real.cosh t := by
        linear_combination a * p.on_sheet + b * hl_pq + hcosht
      have hcs : ((a * p.x + b * q.x) * p.x + (a * p.y + b * q.y) * p.y) ^ 2 ≤
          ((a * p.x + b * q.x) ^ 2 + (a * p.y + b * q.y) ^ 2) * (p.x ^ 2 + p.y ^ 2) := by
        nlinarith [sq_nonneg ((a * p.x + b * q.x) * p.y - (a * p.y + b * q.y) * p.x)]
      have h1 : (a * p.z + b * q.z) * p.z < 0 := mul_neg_of_neg_of_pos hneg p.hz
      have h2 : Real.cosh t > 0 := Real.cosh_pos t
      have hsq_gt : ((a * p.z + b * q.z) * p.z) ^ 2 <
          ((a * p.x + b * q.x) * p.x + (a * p.y + b * q.y) * p.y) ^ 2 := by
        nlinarith
      have hsq_le : ((a * p.x + b * q.x) ^ 2 + (a * p.y + b * q.y) ^ 2) * (p.x ^ 2 + p.y ^ 2) ≤
          ((a * p.z + b * q.z) * p.z) ^ 2 := by
        have ha1 : (a * p.x + b * q.x) ^ 2 + (a * p.y + b * q.y) ^ 2 = (a * p.z + b * q.z) ^ 2 - 1 := by linarith
        have hp1 : p.x ^ 2 + p.y ^ 2 = p.z ^ 2 - 1 := by linarith [p.on_sheet]
        rw [ha1, hp1]
        nlinarith [p.on_sheet]
      linarith
    · exact hpos
  { x := a * p.x + b * q.x
    y := a * p.y + b * q.y
    z := a * p.z + b * q.z
    hz := hz_pos
    on_sheet := hsheet }

lemma lorentz_geodInterp (r p q : H2) (hpq : p ≠ q) (t : ℝ) :
    lorentz r (geodInterp p q hpq t) =
      (Real.sinh (dist p q - t) / Real.sinh (dist p q)) * lorentz r p +
      (Real.sinh t / Real.sinh (dist p q)) * lorentz r q := by
  unfold lorentz geodInterp
  dsimp only
  ring

/-- **Strict quasiconvexity of hyperbolic distance along geodesic segments** (2-line algebraic proof!):
    For `0 < t < dist p q`, `lorentz r (geodInterp p q t) < max (lorentz r p) (lorentz r q)`. -/
theorem lorentz_geodInterp_lt_max (r p q : H2) (hpq : p ≠ q) (t : ℝ)
    (ht0 : 0 < t) (htL : t < dist p q) :
    lorentz r (geodInterp p q hpq t) < max (lorentz r p) (lorentz r q) := by
  rw [lorentz_geodInterp]
  set L := dist p q
  have hL : 0 < L := dist_pos.mpr hpq
  have hshL : 0 < Real.sinh L := Real.sinh_pos_iff.mpr hL
  have ha_pos : 0 < Real.sinh (L - t) / Real.sinh L :=
    div_pos (Real.sinh_pos_iff.mpr (by linarith)) hshL
  have hb_pos : 0 < Real.sinh t / Real.sinh L :=
    div_pos (Real.sinh_pos_iff.mpr ht0) hshL
  have hsum_lt : Real.sinh (L - t) + Real.sinh t < Real.sinh L := by
    set u := L - t
    have hL_eq : L = u + t := by ring
    rw [hL_eq, Real.sinh_add]
    have hc1 : 1 < Real.cosh t := by
      have := Real.cosh_sq_sub_sinh_sq t
      have hsh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht0
      have hch : 0 < Real.cosh t := Real.cosh_pos t
      nlinarith
    have hc2 : 1 < Real.cosh u := by
      have := Real.cosh_sq_sub_sinh_sq u
      have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
      have hch : 0 < Real.cosh u := Real.cosh_pos u
      nlinarith
    have hs1 : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
    have hs2 : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht0
    nlinarith
  have hab_lt : Real.sinh (L - t) / Real.sinh L + Real.sinh t / Real.sinh L < 1 := by
    rw [← add_div, div_lt_one hshL]
    exact hsum_lt
  set M := max (lorentz r p) (lorentz r q)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_trans (one_le_lorentz r p) (le_max_left _ _))
  have h1 : (Real.sinh (L - t) / Real.sinh L) * lorentz r p ≤ (Real.sinh (L - t) / Real.sinh L) * M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) ha_pos.le
  have h2 : (Real.sinh t / Real.sinh L) * lorentz r q ≤ (Real.sinh t / Real.sinh L) * M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hb_pos.le
  nlinarith

/-- Strict quasiconvexity in terms of `dist`: if `dist r p ≤ R` and `dist r q ≤ R` (with `p ≠ q`),
    then `dist r (geodInterp p q t) < R` for every `0 < t < dist p q`. -/
theorem dist_geodInterp_lt_of_le (r p q : H2) (hpq : p ≠ q) (t R : ℝ)
    (ht0 : 0 < t) (htL : t < dist p q) (hrp : dist r p ≤ R) (hrq : dist r q ≤ R) :
    dist r (geodInterp p q hpq t) < R := by
  have hR_nonneg : 0 ≤ R := le_trans dist_nonneg hrp
  rw [← Real.arcosh_cosh hR_nonneg, dist_eq_arcosh]
  rw [Real.arcosh_lt_arcosh (lt_of_lt_of_le zero_lt_one (one_le_lorentz _ _)) (Real.cosh_pos R)]
  have hlt := lorentz_geodInterp_lt_max r p q hpq t ht0 htL
  have hlp : lorentz r p ≤ Real.cosh R := by
    rw [← cosh_dist]
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hR_nonneg]; exact hrp)
  have hlq : lorentz r q ≤ Real.cosh R := by
    rw [← cosh_dist]
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hR_nonneg]; exact hrq)
  exact lt_of_lt_of_le hlt (max_le hlp hlq)

end FejesTothP7.H2
