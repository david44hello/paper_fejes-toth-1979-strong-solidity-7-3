/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# The Hyperbolic Plane `H2` (Hyperboloid Model)

We represent the hyperbolic plane `H2` of constant curvature `-1` as the upper sheet
`{ (x, y, z) ∈ ℝ³ | z > 0 ∧ z^2 - x^2 - y^2 = 1 }` of the two-sheeted hyperboloid,
equipped with the Minkowski bilinear form `lorentz p q = p.z * q.z - p.x * q.x - p.y * q.y`
and hyperbolic distance `dist p q = Real.arcosh (lorentz p q)`.

This module provides the `MetricSpace H2` instance, polar coordinates about the origin,
exact hyperbolic midpoints, orientation determinant `detH`, and reflection/rotation isometries.
-/

noncomputable section

namespace FejesTothP7

/-- A point of the hyperbolic plane `H2` in the hyperboloid (Lorentz) model. -/
@[ext]
structure H2 where
  x : ℝ
  y : ℝ
  z : ℝ
  hz : 0 < z
  on_sheet : z ^ 2 - x ^ 2 - y ^ 2 = 1

namespace H2

/-- The Minkowski (Lorentz) pairing `p.z * q.z - p.x * q.x - p.y * q.y`, equal to `cosh d(p, q)`. -/
def lorentz (p q : H2) : ℝ :=
  p.z * q.z - p.x * q.x - p.y * q.y

/-- The 3×3 orientation determinant of three points in `H2 ⊂ ℝ³`. -/
def detH (p q r : H2) : ℝ :=
  p.x * (q.y * r.z - q.z * r.y)
  - p.y * (q.x * r.z - q.z * r.x)
  + p.z * (q.x * r.y - q.y * r.x)

lemma lorentz_symm (p q : H2) : lorentz p q = lorentz q p := by
  unfold lorentz; ring

lemma lorentz_self (p : H2) : lorentz p p = 1 := by
  unfold lorentz
  have h := p.on_sheet
  nlinarith

lemma z_ge_one (p : H2) : 1 ≤ p.z := by
  have h1 : 1 ≤ p.z ^ 2 := by nlinarith [p.on_sheet]
  nlinarith [p.hz]

/-- Fundamental hyperboloid inequality: `lorentz p q ≥ 1` for all `p, q ∈ H2`. -/
lemma one_le_lorentz (p q : H2) : 1 ≤ lorentz p q := by
  unfold lorentz
  have hp := p.on_sheet
  have hq := q.on_sheet
  have hpz := z_ge_one p
  have hqz := z_ge_one q
  have hcs : (p.x * q.x + p.y * q.y) ^ 2 ≤ (p.x ^ 2 + p.y ^ 2) * (q.x ^ 2 + q.y ^ 2) := by
    nlinarith [sq_nonneg (p.x * q.y - p.y * q.x)]
  have h1 : (p.x ^ 2 + p.y ^ 2) * (q.x ^ 2 + q.y ^ 2) ≤ (p.z * q.z - 1) ^ 2 := by
    have hpx : p.x ^ 2 + p.y ^ 2 = p.z ^ 2 - 1 := by linarith
    have hqx : q.x ^ 2 + q.y ^ 2 = q.z ^ 2 - 1 := by linarith
    rw [hpx, hqx]
    nlinarith [sq_nonneg (p.z - q.z)]
  have h2 : (p.x * q.x + p.y * q.y) ^ 2 ≤ (p.z * q.z - 1) ^ 2 := le_trans hcs h1
  have h3 : 0 ≤ p.z * q.z - 1 := by nlinarith
  have h4 : p.x * q.x + p.y * q.y ≤ p.z * q.z - 1 := by nlinarith
  linarith

lemma lorentz_eq_one_iff (p q : H2) : lorentz p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hp := p.on_sheet
    have hq := q.on_sheet
    have hsum : (p.x * q.y - p.y * q.x) ^ 2 + (p.z - q.z) ^ 2 = 0 := by
      unfold lorentz at h
      have hpx : p.x ^ 2 + p.y ^ 2 = p.z ^ 2 - 1 := by linarith
      have hqx : q.x ^ 2 + q.y ^ 2 = q.z ^ 2 - 1 := by linarith
      have hxy : p.x * q.x + p.y * q.y = p.z * q.z - 1 := by linarith
      nlinarith [sq_nonneg (p.x * q.y - p.y * q.x), sq_nonneg (p.z - q.z)]
    have hzq : p.z = q.z := by nlinarith [sq_nonneg (p.x * q.y - p.y * q.x), sq_nonneg (p.z - q.z)]
    have hdist : (p.x - q.x) ^ 2 + (p.y - q.y) ^ 2 = 0 := by
      unfold lorentz at h
      nlinarith
    ext
    · nlinarith [sq_nonneg (p.x - q.x), sq_nonneg (p.y - q.y)]
    · nlinarith [sq_nonneg (p.x - q.x), sq_nonneg (p.y - q.y)]
    · exact hzq
  · rintro rfl
    exact lorentz_self p

/-- Gram-determinant identity: `(B(p,q)² - 1)(B(q,r)² - 1) - (B(p,r) - B(p,q)B(q,r))² = det(p,q,r)²`. -/
lemma gram_det_identity (p q r : H2) :
    (lorentz p q ^ 2 - 1) * (lorentz q r ^ 2 - 1)
      - (lorentz p r - lorentz p q * lorentz q r) ^ 2
      = (detH p q r) ^ 2 := by
  unfold lorentz detH
  have hp : p.z ^ 2 - p.x ^ 2 - p.y ^ 2 - 1 = 0 := by linarith [p.on_sheet]
  have hq : q.z ^ 2 - q.x ^ 2 - q.y ^ 2 - 1 = 0 := by linarith [q.on_sheet]
  have hr : r.z ^ 2 - r.x ^ 2 - r.y ^ 2 - 1 = 0 := by linarith [r.on_sheet]
  have hpoly :
      ((p.z * q.z - p.x * q.x - p.y * q.y) ^ 2 - (p.z ^ 2 - p.x ^ 2 - p.y ^ 2) * (q.z ^ 2 - q.x ^ 2 - q.y ^ 2)) *
      ((q.z * r.z - q.x * r.x - q.y * r.y) ^ 2 - (q.z ^ 2 - q.x ^ 2 - q.y ^ 2) * (r.z ^ 2 - r.x ^ 2 - r.y ^ 2)) -
      ((q.z ^ 2 - q.x ^ 2 - q.y ^ 2) * (p.z * r.z - p.x * r.x - p.y * r.y) -
       (p.z * q.z - p.x * q.x - p.y * q.y) * (q.z * r.z - q.x * r.x - q.y * r.y)) ^ 2 =
      (q.z ^ 2 - q.x ^ 2 - q.y ^ 2) *
      (p.x * (q.y * r.z - q.z * r.y) - p.y * (q.x * r.z - q.z * r.x) + p.z * (q.x * r.y - q.y * r.x)) ^ 2 := by
    ring
  rw [p.on_sheet, q.on_sheet, r.on_sheet] at hpoly
  linarith

/-- Hyperbolic distance on `H2`. -/
def distH (p q : H2) : ℝ :=
  Real.arcosh (lorentz p q)

lemma distH_nonneg (p q : H2) : 0 ≤ distH p q :=
  Real.arcosh_nonneg (one_le_lorentz p q)

lemma cosh_distH (p q : H2) : Real.cosh (distH p q) = lorentz p q :=
  Real.cosh_arcosh (one_le_lorentz p q)

lemma sinh_distH (p q : H2) : Real.sinh (distH p q) = Real.sqrt (lorentz p q ^ 2 - 1) :=
  Real.sinh_arcosh (one_le_lorentz p q)

lemma distH_self (p : H2) : distH p p = 0 := by
  simp [distH, lorentz_self]

lemma distH_comm (p q : H2) : distH p q = distH q p := by
  simp [distH, lorentz_symm]

lemma eq_of_distH_eq_zero {p q : H2} (h : distH p q = 0) : p = q := by
  rw [← lorentz_eq_one_iff]
  exact (Real.arcosh_eq_zero_iff (one_le_lorentz p q)).mp h

lemma distH_triangle (p q r : H2) : distH p r ≤ distH p q + distH q r := by
  have h0 : 0 ≤ distH p r := distH_nonneg p r
  have h1 : 0 ≤ distH p q + distH q r := add_nonneg (distH_nonneg p q) (distH_nonneg q r)
  rw [← Real.arcosh_cosh h0, ← Real.arcosh_cosh h1]
  rw [Real.arcosh_le_arcosh (Real.cosh_pos _) (Real.cosh_pos _)]
  rw [Real.cosh_add, cosh_distH, cosh_distH, cosh_distH, sinh_distH, sinh_distH]
  have hgram := gram_det_identity p q r
  have hpq : 0 ≤ lorentz p q ^ 2 - 1 := by nlinarith [one_le_lorentz p q]
  have hqr : 0 ≤ lorentz q r ^ 2 - 1 := by nlinarith [one_le_lorentz q r]
  have hsq : (lorentz p r - lorentz p q * lorentz q r) ^ 2 ≤
      (Real.sqrt (lorentz p q ^ 2 - 1) * Real.sqrt (lorentz q r ^ 2 - 1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpq, Real.sq_sqrt hqr]
    nlinarith [sq_nonneg (detH p q r)]
  have hrhs : 0 ≤ Real.sqrt (lorentz p q ^ 2 - 1) * Real.sqrt (lorentz q r ^ 2 - 1) := by
    positivity
  nlinarith

instance : MetricSpace H2 where
  dist := distH
  dist_self := distH_self
  dist_comm := distH_comm
  dist_triangle := distH_triangle
  eq_of_dist_eq_zero := eq_of_distH_eq_zero

lemma dist_eq_arcosh (p q : H2) : dist p q = Real.arcosh (lorentz p q) := rfl

lemma cosh_dist (p q : H2) : Real.cosh (dist p q) = lorentz p q := cosh_distH p q

/-- The origin `(0, 0, 1) ∈ H2`. -/
def origin : H2 where
  x := 0
  y := 0
  z := 1
  hz := by norm_num
  on_sheet := by norm_num

/-- Polar coordinates `(ρ, θ)` about the origin: `(sinh ρ cos θ, sinh ρ sin θ, cosh ρ)`. -/
def polarOrigin (ρ θ : ℝ) : H2 where
  x := Real.sinh ρ * Real.cos θ
  y := Real.sinh ρ * Real.sin θ
  z := Real.cosh ρ
  hz := Real.cosh_pos ρ
  on_sheet := by
    have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have hch : Real.cosh ρ ^ 2 - Real.sinh ρ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq ρ
    nlinarith

/-- Hyperbolic midpoint of two points `p, q ∈ H2`. -/
def mid (p q : H2) : H2 where
  x := (p.x + q.x) / Real.sqrt (2 * (lorentz p q + 1))
  y := (p.y + q.y) / Real.sqrt (2 * (lorentz p q + 1))
  z := (p.z + q.z) / Real.sqrt (2 * (lorentz p q + 1))
  hz := div_pos (add_pos p.hz q.hz) (Real.sqrt_pos.mpr (by linarith [one_le_lorentz p q]))
  on_sheet := by
    have hpos : 0 < 2 * (lorentz p q + 1) := by linarith [one_le_lorentz p q]
    have hsq : Real.sqrt (2 * (lorentz p q + 1)) ^ 2 = 2 * (lorentz p q + 1) :=
      Real.sq_sqrt hpos.le
    rw [div_pow, div_pow, div_pow, ← sub_div, ← sub_div, hsq]
    rw [div_eq_one_iff_eq hpos.ne']
    unfold lorentz
    nlinarith [p.on_sheet, q.on_sheet]

/-- Reflection across the `x`-axis (`θ = 0`) in `H2`. -/
def reflXAxis : H2 ≃ᵢ H2 where
  toFun p := ⟨p.x, -p.y, p.z, p.hz, by nlinarith [p.on_sheet]⟩
  invFun p := ⟨p.x, -p.y, p.z, p.hz, by nlinarith [p.on_sheet]⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  isometry_toFun := by
    intro p q
    simp only [edist_dist, dist_eq_arcosh, lorentz]
    congr 2; ring

/-- Rotation about `origin` by angle `φ`. -/
def rotOrigin (φ : ℝ) : H2 ≃ᵢ H2 where
  toFun p :=
    ⟨p.x * Real.cos φ - p.y * Real.sin φ,
     p.x * Real.sin φ + p.y * Real.cos φ,
     p.z, p.hz, by
       have hcs := Real.cos_sq_add_sin_sq φ
       nlinarith [p.on_sheet, sq_nonneg (p.x * Real.cos φ - p.y * Real.sin φ),
         sq_nonneg (p.x * Real.sin φ + p.y * Real.cos φ)]⟩
  invFun p :=
    ⟨p.x * Real.cos φ + p.y * Real.sin φ,
     -p.x * Real.sin φ + p.y * Real.cos φ,
     p.z, p.hz, by
       have hcs := Real.cos_sq_add_sin_sq φ
       nlinarith [p.on_sheet]⟩
  left_inv p := by
    have hcs := Real.cos_sq_add_sin_sq φ
    ext <;> dsimp
    · linear_combination p.x * hcs
    · linear_combination p.y * hcs
  right_inv p := by
    have hcs := Real.cos_sq_add_sin_sq φ
    ext <;> dsimp
    · linear_combination p.x * hcs
    · linear_combination p.y * hcs
  isometry_toFun := by
    intro p q
    simp only [edist_dist, dist_eq_arcosh, lorentz]
    have hcs := Real.cos_sq_add_sin_sq φ
    congr 2
    linear_combination -(p.x * q.x + p.y * q.y) * hcs

/-- Reflection across the ray through `origin` at angle `φ` (maps `θ ↦ 2φ - θ`). -/
def reflRay (φ : ℝ) : H2 ≃ᵢ H2 :=
  (rotOrigin (-φ)).trans (reflXAxis.trans (rotOrigin φ))

/-- Hyperbolic translation along the `x`-axis by signed distance `t`. -/
def boostX (t : ℝ) : H2 ≃ᵢ H2 where
  toFun p :=
    ⟨p.x * Real.cosh t + p.z * Real.sinh t,
     p.y,
     p.x * Real.sinh t + p.z * Real.cosh t,
     by
       have hch := Real.cosh_pos t
       have hsh : |Real.sinh t| < Real.cosh t := by
         have h := Real.cosh_sq_sub_sinh_sq t
         rw [abs_lt]
         constructor <;> nlinarith
       have hpx : |p.x| < p.z := by
         rw [abs_lt]
         constructor <;> nlinarith [p.on_sheet, p.hz]
       have hmul : |p.x * Real.sinh t| < p.z * Real.cosh t := by
         rw [abs_mul]
         exact mul_lt_mul'' hpx hsh (abs_nonneg _) (abs_nonneg _)
       linarith [(abs_lt.mp hmul).1],
     by
       have hch := Real.cosh_sq_sub_sinh_sq t
       nlinarith [p.on_sheet]⟩
  invFun p :=
    ⟨p.x * Real.cosh t - p.z * Real.sinh t,
     p.y,
     -p.x * Real.sinh t + p.z * Real.cosh t,
     by
       have hch := Real.cosh_pos t
       have hsh : |Real.sinh t| < Real.cosh t := by
         have h := Real.cosh_sq_sub_sinh_sq t
         rw [abs_lt]
         constructor <;> nlinarith
       have hpx : |p.x| < p.z := by
         rw [abs_lt]
         constructor <;> nlinarith [p.on_sheet, p.hz]
       have hmul : |p.x * Real.sinh t| < p.z * Real.cosh t := by
         rw [abs_mul]
         exact mul_lt_mul'' hpx hsh (abs_nonneg _) (abs_nonneg _)
       linarith [(abs_lt.mp hmul).2],
     by
       have hch := Real.cosh_sq_sub_sinh_sq t
       nlinarith [p.on_sheet]⟩
  left_inv p := by
    have hch := Real.cosh_sq_sub_sinh_sq t
    ext <;> dsimp
    · linear_combination p.x * hch
    · linear_combination p.z * hch
  right_inv p := by
    have hch := Real.cosh_sq_sub_sinh_sq t
    ext <;> dsimp
    · linear_combination p.x * hch
    · linear_combination p.z * hch
  isometry_toFun := by
    intro p q
    simp only [edist_dist, dist_eq_arcosh, lorentz]
    have hch := Real.cosh_sq_sub_sinh_sq t
    congr 2
    linear_combination (p.z * q.z - p.x * q.x) * hch

/-- Reflection across the geodesic perpendicular to the `x`-axis at `(sinh d, 0, cosh d)`.
    This maps `origin` to `polarOrigin (2 * d) 0` and fixes `polarOrigin d 0`. -/
def reflPerpX (d : ℝ) : H2 ≃ᵢ H2 :=
  (boostX (-d)).trans (((rotOrigin Real.pi).trans reflXAxis).trans (boostX d))

/-- Geodesic segment between `p` and `q`: points `x` satisfying `dist p x + dist x q = dist p q`. -/
def GeodesicSegment (p q : H2) : Set H2 :=
  {x : H2 | dist p x + dist x q = dist p q}

/-- Open half-plane strictly on the positive (`detH p q · > 0`) side of oriented geodesic `p → q`. -/
def OpenHalfPlanePos (p q : H2) : Set H2 :=
  {x : H2 | 0 < detH p q x}

/-- Open half-plane strictly on the negative (`detH p q · < 0`) side of oriented geodesic `p → q`. -/
def OpenHalfPlaneNeg (p q : H2) : Set H2 :=
  {x : H2 | detH p q x < 0}

/-- Closed half-plane on the non-negative (`0 ≤ detH p q ·`) side of oriented geodesic `p → q`. -/
def ClosedHalfPlanePos (p q : H2) : Set H2 :=
  {x : H2 | 0 ≤ detH p q x}

end H2
end FejesTothP7
