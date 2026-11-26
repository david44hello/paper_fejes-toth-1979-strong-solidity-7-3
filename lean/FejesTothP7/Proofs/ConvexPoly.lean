/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.H2Basic

/-!
# Hyperbolic Convex Polygons, Nearest-Point Feet, and Star-Shaped Convexity

Provides:
1. The tangent-normal functional `normalFunc p x y = lorentz x y - lorentz x p * lorentz p y`,
   exact 3D Cramer identity in a wedge, and unique-foot disjointness (`IsFoot`).
2. Klein disk projection `klein : H2 → ℝ × ℝ`, relating `detH` to 2D orientation `orient2D`.
3. Elementary proof that any star-shaped locally convex polygon in `ℝ²` (and hence in `H2`)
   is globally convex (`starShaped_locallyConvex_globallyConvex`).
-/

noncomputable section

namespace FejesTothP7.H2

/-! ### Tangent-normal functional and unique closest-point feet -/

/-- Tangent-normal functional at `p` in direction `x`:
    `normalFunc p x y ≥ 0` iff the hyperbolic angle `∠(x, p, y) ≥ π / 2` (for `x, y ≠ p`). -/
def normalFunc (p x y : H2) : ℝ :=
  lorentz x y - lorentz x p * lorentz p y

lemma normalFunc_self (p x : H2) : normalFunc p x p = 0 := by
  unfold normalFunc
  rw [lorentz_self, mul_one, sub_self]

lemma normalFunc_isometry (φ : H2 ≃ᵢ H2) (p x y : H2) :
    normalFunc (φ p) (φ x) (φ y) = normalFunc p x y := by
  unfold normalFunc
  rw [isometry_lorentz, isometry_lorentz, isometry_lorentz]

/-- `p ∈ P` is the strict unique closest point (foot) of `x` on `P`. -/
def IsFoot (P : Set H2) (x p : H2) : Prop :=
  p ∈ P ∧ ∀ y ∈ P, y ≠ p → lorentz x p < lorentz x y

lemma eq_of_isFoot {P : Set H2} {x p₁ p₂ : H2}
    (h₁ : IsFoot P x p₁) (h₂ : IsFoot P x p₂) : p₁ = p₂ := by
  by_contra hne
  have hlt1 := h₁.2 p₂ h₂.1 (Ne.symm hne)
  have hlt2 := h₂.2 p₁ h₁.1 hne
  linarith

/-- If `p ∈ P`, `x ≠ p`, and `normalFunc p x y ≥ 0` for all `y ∈ P`, then `p` is the unique foot of `x` on `P`. -/
lemma isFoot_of_normalFunc_nonneg {P : Set H2} {x p : H2}
    (hp : p ∈ P) (hxp : x ≠ p) (hnorm : ∀ y ∈ P, 0 ≤ normalFunc p x y) :
    IsFoot P x p := by
  refine ⟨hp, fun y hy hyp => ?_⟩
  have hn := hnorm y hy
  unfold normalFunc at hn
  have hxp_gt : 1 < lorentz x p :=
    lt_of_le_of_ne (one_le_lorentz x p) (fun h => hxp ((lorentz_eq_one_iff x p).mp h.symm))
  have hpy_gt : 1 < lorentz p y :=
    lt_of_le_of_ne (one_le_lorentz p y) (fun h => hyp ((lorentz_eq_one_iff p y).mp h.symm).symm)
  nlinarith

/-- **3D Cramer identity for `normalFunc`**:
    `det(p, a, b) * normalFunc p x y = det(p, y, b) * normalFunc p x a + det(p, a, y) * normalFunc p x b`. -/
lemma cramer_normalFunc (p a b x y : H2) :
    detH p a b * normalFunc p x y =
      detH p y b * normalFunc p x a + detH p a y * normalFunc p x b := by
  unfold detH normalFunc lorentz
  have hp := p.on_sheet
  linear_combination
    -(x.z * p.z - x.x * p.x - x.y * p.y) *
      (y.x * (a.y * b.z - a.z * b.y) - y.y * (a.x * b.z - a.z * b.x) + y.z * (a.x * b.y - a.y * b.x)) * hp

/-- **Vertex normal-cone criterion**: if `y` lies in the convex wedge `det(p,a,y) ≥ 0, det(p,y,b) ≥ 0`
    at `p` (with `det(p,a,b) > 0`) and `x` lies in the normal cone (`normalFunc p x a ≥ 0, normalFunc p x b ≥ 0`),
    then `normalFunc p x y ≥ 0`. -/
lemma normalFunc_wedge_nonneg {p a b x y : H2}
    (hab : 0 < detH p a b)
    (hya : 0 ≤ detH p a y) (hyb : 0 ≤ detH p y b)
    (hxa : 0 ≤ normalFunc p x a) (hxb : 0 ≤ normalFunc p x b) :
    0 ≤ normalFunc p x y := by
  have hc := cramer_normalFunc p a b x y
  nlinarith

/-- **Edge perpendicular criterion (at origin along `x`-axis)**:
    if `u = polarOrigin (-s) 0` and `v = polarOrigin s 0` (`s > 0`), and `x = polarOrigin d (-π/2)` (`d > 0`),
    then `0 ≤ detH u v y → 0 ≤ normalFunc origin x y`. -/
lemma normalFunc_edge_origin_nonneg {s d : ℝ} (hs : 0 < s) (hd : 0 < d) (y : H2)
    (hy : 0 ≤ detH (polarOrigin (-s) 0) (polarOrigin s 0) y) :
    0 ≤ normalFunc origin (polarOrigin d (-(Real.pi / 2))) y := by
  have hdet : detH (polarOrigin (-s) 0) (polarOrigin s 0) y =
      2 * Real.sinh s * Real.cosh s * y.y := by
    unfold detH polarOrigin
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, Real.sinh_neg, Real.cosh_neg]
    ring
  rw [hdet] at hy
  have hsc : 0 < 2 * Real.sinh s * Real.cosh s := by
    have h1 := Real.sinh_pos_iff.mpr hs
    have h2 := Real.cosh_pos s
    positivity
  have hyy : 0 ≤ y.y := by nlinarith
  have hn : normalFunc origin (polarOrigin d (-(Real.pi / 2))) y = Real.sinh d * y.y := by
    unfold normalFunc lorentz origin polarOrigin
    simp only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
    ring
  rw [hn]
  exact mul_nonneg (Real.sinh_pos_iff.mpr hd).le hyy

/-! ### Klein disk projection and 2D orientation -/

/-- Klein disk projection `(x, y, z) ↦ (x / z, y / z)`. -/
def klein (p : H2) : ℝ × ℝ := (p.x / p.z, p.y / p.z)

/-- Signed doubled area / 2D orientation of `(a, b, c)` in `ℝ²`. -/
def orient2D (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- `detH p q r = p.z * q.z * r.z * orient2D (klein p) (klein q) (klein r)`. -/
lemma detH_eq_orient2D (p q r : H2) :
    detH p q r = p.z * q.z * r.z * orient2D (klein p) (klein q) (klein r) := by
  unfold detH orient2D klein
  have hp : p.z ≠ 0 := p.hz.ne'
  have hq : q.z ≠ 0 := q.hz.ne'
  have hr : r.z ≠ 0 := r.hz.ne'
  field_simp
  ring

lemma detH_pos_iff_orient2D_pos (p q r : H2) :
    0 < detH p q r ↔ 0 < orient2D (klein p) (klein q) (klein r) := by
  rw [detH_eq_orient2D]
  have hpos : 0 < p.z * q.z * r.z := mul_pos (mul_pos p.hz q.hz) r.hz
  exact mul_pos_iff_of_pos_left hpos

lemma detH_nonneg_iff_orient2D_nonneg (p q r : H2) :
    0 ≤ detH p q r ↔ 0 ≤ orient2D (klein p) (klein q) (klein r) := by
  rw [detH_eq_orient2D]
  have hpos : 0 < p.z * q.z * r.z := mul_pos (mul_pos p.hz q.hz) r.hz
  exact mul_nonneg_iff_of_pos_left hpos

/-! ### Elementary 2D Star-Shaped Locally Convex Polygon Theorem -/

/-- Existence of a unique angle jump in `(0, π)` between two unit-or-nonzero vectors with positive cross product. -/
lemma exists_angle_step_in_Ioo {x₁ y₁ x₂ y₂ ψ₁ : ℝ}
    (hr₁ : 0 < x₁ ^ 2 + y₁ ^ 2) (hr₂ : 0 < x₂ ^ 2 + y₂ ^ 2)
    (h1x : x₁ = Real.sqrt (x₁ ^ 2 + y₁ ^ 2) * Real.cos ψ₁)
    (h1y : y₁ = Real.sqrt (x₁ ^ 2 + y₁ ^ 2) * Real.sin ψ₁)
    (hdet : 0 < x₁ * y₂ - y₁ * x₂) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi ∧
      x₂ = Real.sqrt (x₂ ^ 2 + y₂ ^ 2) * Real.cos (ψ₁ + δ) ∧
      y₂ = Real.sqrt (x₂ ^ 2 + y₂ ^ 2) * Real.sin (ψ₁ + δ) := by
  set r₁ := Real.sqrt (x₁ ^ 2 + y₁ ^ 2)
  set r₂ := Real.sqrt (x₂ ^ 2 + y₂ ^ 2)
  have hr1_pos : 0 < r₁ := Real.sqrt_pos.mpr hr₁
  have hr2_pos : 0 < r₂ := Real.sqrt_pos.mpr hr₂
  set c := (x₁ * x₂ + y₁ * y₂) / (r₁ * r₂)
  set s := (x₁ * y₂ - y₁ * x₂) / (r₁ * r₂)
  have hs_pos : 0 < s := div_pos hdet (mul_pos hr1_pos hr2_pos)
  have hcs_id : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, div_pow, ← add_div]
    rw [div_eq_one_iff_eq (pow_ne_zero 2 (mul_pos hr1_pos hr2_pos).ne')]
    have hr1_sq : r₁ ^ 2 = x₁ ^ 2 + y₁ ^ 2 := Real.sq_sqrt hr₁.le
    have hr2_sq : r₂ ^ 2 = x₂ ^ 2 + y₂ ^ 2 := Real.sq_sqrt hr₂.le
    rw [mul_pow, hr1_sq, hr2_sq]
    ring
  have hc_lt1 : c < 1 := by nlinarith [sq_pos_of_pos hs_pos]
  have hc_gt_neg1 : -1 < c := by nlinarith [sq_pos_of_pos hs_pos]
  refine ⟨Real.arccos c, ?_, ?_, ?_, ?_⟩
  · exact Real.arccos_pos.mpr hc_lt1
  · exact Real.arccos_lt_pi.mpr hc_gt_neg1
  · rw [Real.cos_add, Real.cos_arccos hc_gt_neg1.le hc_lt1.le, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - c ^ 2) = s := by
      rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs_pos.le]
    rw [hsqrt]
    have hcos : Real.cos ψ₁ = x₁ / r₁ := by field_simp [hr1_pos.ne']; linarith
    have hsin : Real.sin ψ₁ = y₁ / r₁ := by field_simp [hr1_pos.ne']; linarith
    rw [hcos, hsin]
    simp only [c, s]
    have hr1_sq : r₁ ^ 2 = x₁ ^ 2 + y₁ ^ 2 := Real.sq_sqrt hr₁.le
    field_simp [hr1_pos.ne', hr2_pos.ne']
    linear_combination x₂ * hr1_sq
  · rw [Real.sin_add, Real.cos_arccos hc_gt_neg1.le hc_lt1.le, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - c ^ 2) = s := by
      rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs_pos.le]
    rw [hsqrt]
    have hcos : Real.cos ψ₁ = x₁ / r₁ := by field_simp [hr1_pos.ne']; linarith
    have hsin : Real.sin ψ₁ = y₁ / r₁ := by field_simp [hr1_pos.ne']; linarith
    rw [hcos, hsin]
    simp only [c, s]
    have hr1_sq : r₁ ^ 2 = x₁ ^ 2 + y₁ ^ 2 := Real.sq_sqrt hr₁.le
    field_simp [hr1_pos.ne', hr2_pos.ne']
    linear_combination y₂ * hr1_sq

/-- If `cos α > 0` and `α ∈ (-3π/2, 3π/2)`, then `α ∈ (-π/2, π/2)`. -/
lemma abs_lt_pi_div_two_of_cos_pos {α : ℝ} (hcos : 0 < Real.cos α)
    (hlo : -(3 * Real.pi / 2) < α) (hhi : α < 3 * Real.pi / 2) :
    -(Real.pi / 2) < α ∧ α < Real.pi / 2 := by
  constructor
  · by_contra hle
    push Not at hle
    have hneg : Real.cos α ≤ 0 := by
      have h1 : Real.cos α = Real.cos (-α) := (Real.cos_neg α).symm
      rw [h1]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith
  · by_contra hle
    push Not at hle
    have hneg : Real.cos α ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith)
    linarith

/-- **Star-Shaped Locally Convex Polygon Theorem in `ℝ²`**:
    If `u : ℕ → ℝ × ℝ` is `N`-periodic (`N ≥ 3`), star-shaped strictly CCW around `(0, 0)` with
    winding number `1` (`θ (k + N) = θ k + 2π`, `0 < θ (k+1) - θ k < π`), and locally convex
    (`orient2D (u k) (u (k+1)) (u (k+2)) > 0` for all `k`), then `u` is **globally convex**:
    for every `k` and every `j` with `k + 1 < j < k + N`, `orient2D (u k) (u (k+1)) (u j) > 0`! -/
theorem starShaped_locallyConvex_globallyConvex {N : ℕ} (_hN : 3 ≤ N)
    (u : ℕ → ℝ × ℝ) (hper : ∀ k, u (k + N) = u k)
    (R θ : ℕ → ℝ)
    (hR : ∀ k, 0 < R k)
    (hu_pol : ∀ k, u k = (R k * Real.cos (θ k), R k * Real.sin (θ k)))
    (hθ_step : ∀ k, 0 < θ (k + 1) - θ k ∧ θ (k + 1) - θ k < Real.pi)
    (hθ_wind : ∀ k, θ (k + N) = θ k + 2 * Real.pi)
    (hloc : ∀ k, 0 < orient2D (u k) (u (k + 1)) (u (k + 2))) :
    ∀ k j : ℕ, k + 1 < j → j < k + N → 0 < orient2D (u k) (u (k + 1)) (u j) := by
  -- Outward normal n_m = ((u (m+1)).2 - (u m).2, -((u (m+1)).1 - (u m).1))
  let nx (m : ℕ) : ℝ := (u (m + 1)).2 - (u m).2
  let ny (m : ℕ) : ℝ := -((u (m + 1)).1 - (u m).1)
  let L (m : ℕ) : ℝ := Real.sqrt (nx m ^ 2 + ny m ^ 2)
  -- For every m, u m · n m = orient2D (0, u m, u (m+1)) = R m * R (m+1) * sin(θ (m+1) - θ m) > 0!
  have hdot_pos : ∀ m, 0 < (u m).1 * nx m + (u m).2 * ny m := by
    intro m
    have h1 : (u m).1 * nx m + (u m).2 * ny m =
        R m * R (m + 1) * Real.sin (θ (m + 1) - θ m) := by
      simp only [nx, ny, hu_pol]
      rw [Real.sin_sub]
      ring
    rw [h1]
    exact mul_pos (mul_pos (hR m) (hR (m + 1)))
      (Real.sin_pos_of_pos_of_lt_pi (hθ_step m).1 (hθ_step m).2)
  have hL_sq_pos : ∀ m, 0 < nx m ^ 2 + ny m ^ 2 := by
    intro m
    by_contra hle
    push Not at hle
    have hnx0 : nx m = 0 := by nlinarith [sq_nonneg (nx m), sq_nonneg (ny m)]
    have hny0 : ny m = 0 := by nlinarith [sq_nonneg (nx m), sq_nonneg (ny m)]
    have hd := hdot_pos m
    rw [hnx0, hny0] at hd
    linarith
  have hL_pos : ∀ m, 0 < L m := fun m => Real.sqrt_pos.mpr (hL_sq_pos m)
  -- Cross product of consecutive outward normals = orient2D (u m, u (m+1), u (m+2)) > 0!
  have hcross_pos : ∀ m, 0 < nx m * ny (m + 1) - ny m * nx (m + 1) := by
    intro m
    have h := hloc m
    unfold orient2D at h
    have heq : nx m * ny (m + 1) - ny m * nx (m + 1) =
        ((u (m + 1)).1 - (u m).1) * ((u (m + 2)).2 - (u m).2) -
        ((u (m + 1)).2 - (u m).2) * ((u (m + 2)).1 - (u m).1) := by
      simp only [nx, ny]; ring
    linarith
  -- Fix k: build lifted outward-normal angle ψ : ℕ → ℝ starting at ψ 0 = angle of n_k near θ k!
  intro k j hjk hjN
  -- First find ψ₀ ∈ (θ k - π/2, θ k + π/2) representing n_k
  have hex0 : ∃ ψ₀ : ℝ,
      -(Real.pi / 2) < ψ₀ - θ k ∧ ψ₀ - θ k < Real.pi / 2 ∧
      nx k = L k * Real.cos ψ₀ ∧ ny k = L k * Real.sin ψ₀ := by
    set c := (Real.cos (θ k) * nx k + Real.sin (θ k) * ny k) / L k
    set s := (-Real.sin (θ k) * nx k + Real.cos (θ k) * ny k) / L k
    have hc_pos : 0 < c := by
      have hd := hdot_pos k
      simp only [hu_pol] at hd
      have hnum : 0 < Real.cos (θ k) * nx k + Real.sin (θ k) * ny k := by
        have hRk := hR k
        nlinarith
      exact div_pos hnum (hL_pos k)
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      simp only [c, s, div_pow, ← add_div]
      rw [div_eq_one_iff_eq (pow_ne_zero 2 (hL_pos k).ne')]
      have hL2 : L k ^ 2 = nx k ^ 2 + ny k ^ 2 := Real.sq_sqrt (hL_sq_pos k).le
      have htrig := Real.cos_sq_add_sin_sq (θ k)
      rw [hL2]
      linear_combination (nx k ^ 2 + ny k ^ 2) * htrig
    have hc_le : c ≤ 1 := by nlinarith [sq_nonneg s]
    have hc_ge : -1 ≤ c := by nlinarith [sq_nonneg s]
    by_cases hs : 0 ≤ s
    · refine ⟨θ k + Real.arccos c, ?_, ?_, ?_, ?_⟩
      · have := Real.arccos_nonneg c; linarith [Real.pi_pos]
      · have := Real.arccos_lt_pi_div_two.mpr hc_pos; linarith
      · rw [Real.cos_add, Real.cos_arccos hc_ge hc_le, Real.sin_arccos]
        have hsq : Real.sqrt (1 - c ^ 2) = s := by
          rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs]
        rw [hsq]
        have htrig := Real.cos_sq_add_sin_sq (θ k)
        simp only [c, s]
        field_simp [(hL_pos k).ne']
        linear_combination -nx k * htrig
      · rw [Real.sin_add, Real.cos_arccos hc_ge hc_le, Real.sin_arccos]
        have hsq : Real.sqrt (1 - c ^ 2) = s := by
          rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs]
        rw [hsq]
        have htrig := Real.cos_sq_add_sin_sq (θ k)
        simp only [c, s]
        field_simp [(hL_pos k).ne']
        linear_combination -ny k * htrig
    · refine ⟨θ k - Real.arccos c, ?_, ?_, ?_, ?_⟩
      · have := Real.arccos_lt_pi_div_two.mpr hc_pos; linarith
      · have := Real.arccos_nonneg c; linarith [Real.pi_pos]
      · rw [Real.cos_sub, Real.cos_arccos hc_ge hc_le, Real.sin_arccos]
        have hsq : Real.sqrt (1 - c ^ 2) = -s := by
          rw [show 1 - c ^ 2 = (-s) ^ 2 by linarith, Real.sqrt_sq (by linarith)]
        rw [hsq]
        have htrig := Real.cos_sq_add_sin_sq (θ k)
        simp only [c, s]
        field_simp [(hL_pos k).ne']
        linear_combination -nx k * htrig
      · rw [Real.sin_sub, Real.cos_arccos hc_ge hc_le, Real.sin_arccos]
        have hsq : Real.sqrt (1 - c ^ 2) = -s := by
          rw [show 1 - c ^ 2 = (-s) ^ 2 by linarith, Real.sqrt_sq (by linarith)]
        rw [hsq]
        have htrig := Real.cos_sq_add_sin_sq (θ k)
        simp only [c, s]
        field_simp [(hL_pos k).ne']
        linear_combination -ny k * htrig
  rcases hex0 with ⟨ψ₀, hψ0_lo, hψ0_hi, hnx0, hny0⟩
  -- Build lifted sequence ψ : ℕ → ℝ by recursion using `exists_angle_step_in_Ioo`!
  have hlift : ∃ ψ : ℕ → ℝ,
      ψ 0 = ψ₀ ∧
      (∀ t, 0 < ψ (t + 1) - ψ t ∧ ψ (t + 1) - ψ t < Real.pi) ∧
      (∀ t, nx (k + t) = L (k + t) * Real.cos (ψ t) ∧ ny (k + t) = L (k + t) * Real.sin (ψ t)) := by
    let P : ℕ → ℝ → Prop := fun t a =>
      nx (k + t) = L (k + t) * Real.cos a ∧ ny (k + t) = L (k + t) * Real.sin a
    let step : ∀ t, { a : ℝ // P t a } → { a : ℝ // P (t + 1) a } := fun t ⟨a, ha⟩ =>
      let hex := exists_angle_step_in_Ioo (hL_sq_pos (k + t)) (hL_sq_pos (k + t + 1))
        ha.1 ha.2 (hcross_pos (k + t))
      ⟨a + Classical.choose hex,
        by
          have hspec := Classical.choose_spec hex
          exact ⟨hspec.2.2.1, hspec.2.2.2⟩⟩
    let seq : (t : ℕ) → { a : ℝ // P t a } :=
      Nat.rec ⟨ψ₀, by simpa [P] using And.intro hnx0 hny0⟩ step
    refine ⟨fun t => (seq t).1, rfl, ?_, fun t => (seq t).2⟩
    intro t
    have hspec := Classical.choose_spec
      (exists_angle_step_in_Ioo (hL_sq_pos (k + t)) (hL_sq_pos (k + t + 1))
        (seq t).2.1 (seq t).2.2 (hcross_pos (k + t)))
    change 0 < ((seq t).1 + Classical.choose _) - (seq t).1 ∧
      ((seq t).1 + Classical.choose _) - (seq t).1 < Real.pi
    constructor <;> linarith [hspec.1, hspec.2.1]
  rcases hlift with ⟨ψ, hψ0, hψ_step, hψ_rep⟩
  -- By induction on t, |ψ t - θ (k + t)| < π / 2 for ALL t!
  have htrack : ∀ t, -(Real.pi / 2) < ψ t - θ (k + t) ∧ ψ t - θ (k + t) < Real.pi / 2 := by
    intro t
    induction t with
    | zero => simpa [hψ0] using And.intro hψ0_lo hψ0_hi
    | succ t ih =>
      have hcos_pos : 0 < Real.cos (ψ (t + 1) - θ (k + (t + 1))) := by
        have hd := hdot_pos (k + (t + 1))
        have hr := hψ_rep (t + 1)
        have hdot_eq : (u (k + (t + 1))).1 * nx (k + (t + 1)) +
            (u (k + (t + 1))).2 * ny (k + (t + 1)) =
            R (k + (t + 1)) * L (k + (t + 1)) * Real.cos (ψ (t + 1) - θ (k + (t + 1))) := by
          rw [hu_pol, hr.1, hr.2, Real.cos_sub]; ring
        rw [hdot_eq] at hd
        have hRL : 0 < R (k + (t + 1)) * L (k + (t + 1)) := mul_pos (hR _) (hL_pos _)
        nlinarith
      have h1 := hψ_step t
      have h2 := hθ_step (k + t)
      have hdiff_eq : ψ (t + 1) - θ (k + (t + 1)) =
          (ψ t - θ (k + t)) + (ψ (t + 1) - ψ t) - (θ (k + t + 1) - θ (k + t)) := by
        have : k + (t + 1) = k + t + 1 := by omega
        rw [this]; ring
      exact abs_lt_pi_div_two_of_cos_pos hcos_pos (by linarith [ih.1, h1.1, h2.2])
        (by linarith [ih.2, h1.2, h2.1])
  -- Therefore ψ N = ψ 0 + 2π!
  have hψN : ψ N = ψ 0 + 2 * Real.pi := by
    have htrN := htrack N
    rw [hθ_wind k] at htrN
    have hnxN : nx (k + N) = nx k := by
      simp only [nx]
      have h1 : k + N + 1 = k + 1 + N := by omega
      rw [h1, hper, hper]
    have hnyN : ny (k + N) = ny k := by
      simp only [ny]
      have h1 : k + N + 1 = k + 1 + N := by omega
      rw [h1, hper, hper]
    have hLN : L (k + N) = L k := by simp [L, hnxN, hnyN]
    have hrepN := hψ_rep N
    have hrep0 := hψ_rep 0
    have hcos_eq : Real.cos (ψ N - ψ 0) = 1 := by
      have hcN : Real.cos (ψ N) = Real.cos (ψ 0) := by
        have h1 : L k * Real.cos (ψ N) = L k * Real.cos (ψ 0) := by
          rw [← hLN, ← hrepN.1, hnxN, hLN]; simpa using hrep0.1
        exact mul_left_cancel₀ (hL_pos k).ne' h1
      have hsN : Real.sin (ψ N) = Real.sin (ψ 0) := by
        have h1 : L k * Real.sin (ψ N) = L k * Real.sin (ψ 0) := by
          rw [← hLN, ← hrepN.2, hnyN, hLN]; simpa using hrep0.2
        exact mul_left_cancel₀ (hL_pos k).ne' h1
      rw [Real.cos_sub, hcN, hsN]
      have := Real.cos_sq_add_sin_sq (ψ 0); nlinarith
    -- ψ N - ψ 0 ∈ (π, 3π) and cos(ψ N - ψ 0) = 1 ⇒ ψ N - ψ 0 = 2π!
    have hlo : Real.pi < ψ N - ψ 0 := by linarith [htrN.1, hψ0, hψ0_hi]
    have hhi : ψ N - ψ 0 < 3 * Real.pi := by linarith [htrN.2, hψ0, hψ0_lo]
    have hcos_shift : Real.cos (ψ N - ψ 0 - 2 * Real.pi) = 1 := by
      rw [Real.cos_sub_two_pi]; exact hcos_eq
    by_contra hne
    have hne0 : ψ N - ψ 0 - 2 * Real.pi ≠ 0 := fun h => hne (by linarith)
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · have hlt : Real.cos (ψ N - ψ 0 - 2 * Real.pi) < Real.cos 0 := by
        rw [← Real.cos_neg (ψ N - ψ 0 - 2 * Real.pi)]
        exact Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
          ⟨by linarith, by linarith⟩ (by linarith)
      simp at hlt; linarith
    · have hlt : Real.cos (ψ N - ψ 0 - 2 * Real.pi) < Real.cos 0 :=
        Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
          ⟨by linarith, by linarith⟩ hpos
      simp at hlt; linarith
  -- Now evaluate orient2D (u k) (u (k+1)) (u j) = -(u j - u k) · n_k = -(u j - u (k+1)) · n_k!
  -- Define f(t) := (u (k + t) - u k) · n_k = (u (k + t)).1 * nx k + (u (k + t)).2 * ny k - ((u k).1 * nx k + (u k).2 * ny k).
  -- Note orient2D (u k) (u (k+1)) (u (k + t)) = - f t!
  let f (t : ℕ) : ℝ :=
    ((u (k + t)).1 - (u k).1) * nx k + ((u (k + t)).2 - (u k).2) * ny k
  have hf_orient : ∀ t, orient2D (u k) (u (k + 1)) (u (k + t)) = -f t := by
    intro t
    unfold orient2D
    simp only [f, nx, ny]
    ring
  have hf_diff : ∀ t, f (t + 1) - f t = -L k * L (k + t) * Real.sin (ψ t - ψ 0) := by
    intro t
    have hrep0 := hψ_rep 0
    have hrept := hψ_rep t
    have h1 : f (t + 1) - f t =
        ((u (k + t + 1)).1 - (u (k + t)).1) * nx k +
        ((u (k + t + 1)).2 - (u (k + t)).2) * ny k := by
      have hk1 : k + (t + 1) = k + t + 1 := by omega
      simp only [f, hk1]; ring
    have h2 : ((u (k + t + 1)).1 - (u (k + t)).1) = -ny (k + t) := by simp [ny]
    have h3 : ((u (k + t + 1)).2 - (u (k + t)).2) = nx (k + t) := by simp [nx]
    rw [h1, h2, h3, hrept.1, hrept.2]
    have h0x : nx k = L k * Real.cos (ψ 0) := by simpa using hrep0.1
    have h0y : ny k = L k * Real.sin (ψ 0) := by simpa using hrep0.2
    rw [h0x, h0y, Real.sin_sub]
    ring
  have hf1 : f 1 = 0 := by simp [f, nx, ny]; ring
  have hfN : f N = 0 := by simp [f, hper]
  -- ψ is strictly increasing from ψ 0 to ψ 0 + 2π:
  have hψ_mono : ∀ a b, a < b → ψ a < ψ b := by
    intro a b hab
    induction hab with
    | refl => linarith [(hψ_step a).1]
    | @step m hlt ih => linarith [ih, (hψ_step m).1]
  -- Let t = j - k (so 1 < t < N). Either ψ t - ψ 0 ≤ π (then f decreases strictly from f 1 = 0 down to f t),
  -- or ψ t - ψ 0 > π (then f increases strictly from f t up to f N = 0)!
  set t := j - k
  have ht1 : 1 < t := by omega
  have htN : t < N := by omega
  have hj_eq : j = k + t := by omega
  rw [hj_eq, hf_orient t]
  suffices hft : f t < 0 by linarith
  by_cases hpi : ψ t - ψ 0 ≤ Real.pi
  · -- For all 1 ≤ s < t: 0 < ψ s - ψ 0 < π, so f (s + 1) < f s!
    have hdec : ∀ s, 1 ≤ s → s ≤ t → (1 < s → f s < 0) ∧ f s ≤ 0 := by
      intro s hs1 hst
      induction s, hs1 using Nat.le_induction with
      | base => exact ⟨fun h => absurd h (by omega), le_of_eq hf1⟩
      | succ r hr ih =>
        have hr_lt : r < t := by omega
        have hψ_lo : 0 < ψ r - ψ 0 := by linarith [hψ_mono 0 r (by omega)]
        have hψ_hi : ψ r - ψ 0 < Real.pi := by linarith [hψ_mono r t hr_lt, hpi]
        have hsin : 0 < Real.sin (ψ r - ψ 0) := Real.sin_pos_of_pos_of_lt_pi hψ_lo hψ_hi
        have hstep_neg : f (r + 1) - f r < 0 := by
          rw [hf_diff r]
          have hLL : 0 < L k * L (k + r) := mul_pos (hL_pos k) (hL_pos (k + r))
          nlinarith
        have ihr := ih (by omega)
        exact ⟨fun _ => by linarith [ihr.2], by linarith [ihr.2]⟩
    exact (hdec t (by omega) le_rfl).1 ht1
  · -- ψ t - ψ 0 > π: for all t ≤ s < N, π < ψ s - ψ 0 < 2π, so sin < 0, hence f (s + 1) > f s!
    push Not at hpi
    have hinc : ∀ m, t ≤ m → m ≤ N → f t ≤ f m ∧ (t < m → f t < f m) := by
      intro m htm hmN
      induction m, htm using Nat.le_induction with
      | base => exact ⟨le_rfl, fun h => absurd h (by omega)⟩
      | succ r hr ih =>
        have hr_lt : r < N := by omega
        have hψ_lo : Real.pi < ψ r - ψ 0 := by
          rcases eq_or_lt_of_le hr with rfl | hlt
          · exact hpi
          · linarith [hψ_mono t r hlt, hpi]
        have hψ_hi : ψ r - ψ 0 < 2 * Real.pi := by linarith [hψ_mono r N hr_lt, hψN]
        have hsin : Real.sin (ψ r - ψ 0) < 0 := by
          have h1 : Real.sin (ψ r - ψ 0 - Real.pi) = -Real.sin (ψ r - ψ 0) := Real.sin_sub_pi _
          have h2 : 0 < Real.sin (ψ r - ψ 0 - Real.pi) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          linarith
        have hstep_pos : 0 < f (r + 1) - f r := by
          rw [hf_diff r]
          have hLL : 0 < L k * L (k + r) := mul_pos (hL_pos k) (hL_pos (k + r))
          nlinarith
        have ihr := ih (by omega)
        exact ⟨by linarith [ihr.1], fun _ => by linarith [ihr.1]⟩
    have hltN := (hinc N (by omega) le_rfl).2 htN
    linarith [hfN]

end FejesTothP7.H2
