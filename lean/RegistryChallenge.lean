-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Strong solidity of the regular `{7, 3}` hyperbolic circle packing

The face-incircles of the regular hyperbolic tiling `{7, 3}` form a strongly solid circle packing
of the hyperbolic plane `H2`, with grade of saturatedness `3` and order of solidity `1`.
This module states Theorem 1.1, Corollary 1.2, the `{7, 3}`/`{3, 7}` tiling certification,
and the open-disc packing and overlap bridges over Mathlib alone.
-/

noncomputable section

namespace FejesTothP7

/-- A point of the hyperbolic plane `H2` in the hyperboloid (Lorentz) model. -/
structure H2 where
  x : ℝ
  y : ℝ
  z : ℝ
  hz : 0 < z
  on_sheet : z ^ 2 - x ^ 2 - y ^ 2 = 1

namespace H2

@[ext]
lemma ext {p q : H2} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p; cases q; simp only at hx hy hz; subst hx; subst hy; subst hz; rfl

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

end H2

instance instAtLeastTwo2 : Nat.AtLeastTwo 2 := inferInstance
instance instAtLeastTwo3 : Nat.AtLeastTwo 3 := inferInstance

/-- Vertex angle `2π / p` of an equilateral triangle in the dual triangulation `{3, p}`. -/
def alphaP (p : ℕ) : ℝ := 2 * Real.pi / (p : ℝ)

/-- Face-inradius `r_p` of the regular hyperbolic tiling `{p, 3}` (`p ≥ 7`). -/
def rP (p : ℕ) : ℝ := Real.arcosh (1 / (2 * Real.sin (Real.pi / (p : ℝ))))

/-- Specialized constants for `p = 7`. -/
def α7 : ℝ := alphaP 7
def r7 : ℝ := rP 7
def Rc7 : ℝ := Real.arsinh (Real.sinh r7 / Real.sin (Real.pi / 3))

/-- A set `C ⊆ H2` of centers forms a packing of open discs of radius `r > 0`
    iff distinct centers lie at distance at least `2 r`. -/
def IsPacking (r : ℝ) (C : Set H2) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * r ≤ dist x y

/-- Two sets of centers in `H2` are congruent if one is mapped onto the other by a hyperbolic isometry. -/
def Congruent (A B : Set H2) : Prop :=
  ∃ φ : H2 ≃ᵢ H2, φ '' A = B

/-- `X` is a finite rearrangement of a finite subset `s ⊆ C` in a radius-`r` packing `C`:
    `|X| = |s|`, `X` is disjoint from the fixed circles `C \ s`, and `(C \ s) ∪ X` is a radius-`r` packing. -/
def IsRearrangement (r : ℝ) (C : Set H2) (s X : Finset H2) : Prop :=
  (s : Set H2) ⊆ C ∧
  X.card = s.card ∧
  Disjoint (C \ (s : Set H2)) (X : Set H2) ∧
  IsPacking r ((C \ (s : Set H2)) ∪ (X : Set H2))

/-- A rearrangement `X` of `s ⊆ C` is trivial if `(C \ s) ∪ X` is congruent to `C`. -/
def IsTrivialRearrangement (C : Set H2) (s X : Finset H2) : Prop :=
  Congruent ((C \ (s : Set H2)) ∪ (X : Set H2)) C

/-- A packing `C` of open discs of radius `r` is solid if every finite rearrangement is trivial. -/
def IsSolid (r : ℝ) (C : Set H2) : Prop :=
  IsPacking r C ∧
  ∀ s X : Finset H2, IsRearrangement r C s X → IsTrivialRearrangement C s X

/-- A packing `C` is strongly solid if it is solid and remains solid after removing any single circle. -/
def IsStronglySolid (r : ℝ) (C : Set H2) : Prop :=
  IsSolid r C ∧ ∀ c₀ ∈ C, IsSolid r (C \ {c₀})

/-- A `k`-truncation of `C` is obtained by removing `k` distinct circles from `C`. -/
def IsKTruncation (C : Set H2) (k : ℕ) (C' : Set H2) : Prop :=
  ∃ K : Finset H2, (K : Set H2) ⊆ C ∧ K.card = k ∧ C' = C \ (K : Set H2)

/-- `C` is solid of order `k` if every finite rearrangement of every `k`-truncation `C'` of `C`
    is congruent to some `k`-truncation of `C`. -/
def IsSolidOfOrder (r : ℝ) (C : Set H2) (k : ℕ) : Prop :=
  IsPacking r C ∧
  ∀ C', IsKTruncation C k C' →
    ∀ s X : Finset H2, IsRearrangement r C' s X →
      ∃ C'', IsKTruncation C k C'' ∧ Congruent ((C' \ (s : Set H2)) ∪ (X : Set H2)) C''

/-- The order of solidity of `C` is `k` if `C` is solid of order `k` and not of any larger order. -/
def HasOrderOfSolidity (r : ℝ) (C : Set H2) (k : ℕ) : Prop :=
  IsSolidOfOrder r C k ∧ ∀ m : ℕ, IsSolidOfOrder r C m → m ≤ k

/-- Every radius-`r` circle not in `C` intersects at least `g` circles of `C`. -/
def HasGradeAtLeast (r : ℝ) (C : Set H2) (g : ℕ) : Prop :=
  ∀ P : H2, P ∉ C →
    ∃ F : Finset H2, (F : Set H2) ⊆ C ∧ F.card = g ∧ ∀ q ∈ F, dist P q < 2 * r

/-- The grade of saturatedness of `C` is `g` if every circle not in `C` intersects at least `g`
    circles of `C` and `g` is largest with this property. -/
def HasGradeOfSaturatedness (r : ℝ) (C : Set H2) (g : ℕ) : Prop :=
  HasGradeAtLeast r C g ∧ ∀ m : ℕ, HasGradeAtLeast r C m → m ≤ g

/-- A point `P` overlaps a site `q` if `dist P q < 2 r`. -/
def Overlaps (r : ℝ) (P q : H2) : Prop :=
  dist P q < 2 * r

/-- Reflection `R1` across the ray `θ = 0` from `H2.origin`. -/
def R1_237 : H2 ≃ᵢ H2 := H2.reflXAxis

/-- Reflection `R2` across the ray `θ = π / 7` from `H2.origin`. -/
def R2_237 : H2 ≃ᵢ H2 := H2.reflRay (Real.pi / 7)

/-- Reflection `R3` across the perpendicular bisector of `[origin, polarOrigin (2 * r7) 0]`. -/
def R3_237 : H2 ≃ᵢ H2 := H2.reflPerpX r7

/-- The `(2, 3, 7)` hyperbolic reflection group generated by `R1_237`, `R2_237`, `R3_237`. -/
def Delta237 : Subgroup (H2 ≃ᵢ H2) :=
  Subgroup.closure ({R1_237, R2_237, R3_237} : Set (H2 ≃ᵢ H2))

/-- The canonical set of sites (centers of the face-incircles of `{7, 3}`, i.e. vertices of `{3, 7}`). -/
def sites37 : Set H2 :=
  {p : H2 | ∃ g ∈ Delta237, g H2.origin = p}

/-- Two sites in a site set `V` are adjacent in `{3, 7}` iff their distance equals `2 * r7`. -/
def Adj37 (u v : H2) : Prop :=
  dist u v = 2 * r7

/-- A hyperbolic polar frame at a site `v ∈ V`: an isometry `φ : H2 ≃ᵢ H2` sending `origin` to `v`
    and sending the seven rays `(2 r7, k α7)` (`k : Fin 7`) bijectively onto the neighbors of `v` in `V`. -/
structure SiteFrame (V : Set H2) (v : H2) where
  φ : H2 ≃ᵢ H2
  origin_eq : φ H2.origin = v
  nbr_mem : ∀ k : Fin 7, φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) ∈ V
  nbr_iff : ∀ w ∈ V, Adj37 v w ↔ ∃ k : Fin 7, w = φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))

namespace Paper

/-- **Theorem 1.1**: The face-incircles of the regular hyperbolic tiling `{7, 3}`
    form a strongly solid packing. -/
theorem thm_1_1_strong_solidity :
    IsStronglySolid r7 sites37 := by sorry

/-- **Corollary 1.2**: For the face-incircle packing `Π₇` of `{7, 3}`,
    the grade of saturatedness is `g₇ = 3` and the order of solidity is `k₇ = 1 = g₇ - 2`. -/
theorem cor_1_2_grade_and_order :
    HasGradeOfSaturatedness r7 sites37 3 ∧ HasOrderOfSolidity r7 sites37 1 := by sorry

/-- **Section 2.1 `{7, 3}` / `{3, 7}` certification**: The concrete `Delta237`-orbit `sites37` is a
    radius-`r7` packing in which every site has a 7-neighbor `SiteFrame`, every point of `H2` lies
    within covering radius `Rc7` of a site, and `Delta237` acts transitively on `sites37`. -/
theorem sites37_tiling_certification :
    IsPacking r7 sites37 ∧
    (∀ v ∈ sites37, Nonempty (SiteFrame sites37 v)) ∧
    (∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7) ∧
    (∀ u ∈ sites37, ∀ v ∈ sites37, ∃ g ∈ Delta237, g u = v ∧ g '' sites37 = sites37) := by sorry

/-- **Open-disc packing bridge**: For `r > 0`, `IsPacking r C` is equivalent to pairwise disjointness
    of the open discs `Metric.ball x r`. -/
theorem isPacking_iff_pairwise_disjoint_balls {r : ℝ} (hr : 0 < r) (C : Set H2) :
    IsPacking r C ↔
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (Metric.ball x r) (Metric.ball y r) := by sorry

/-- **Open-disc overlap bridge**: For `r > 0`, `Overlaps r P q` is equivalent to nonempty intersection
    of the open discs `Metric.ball P r` and `Metric.ball q r`. -/
theorem overlaps_iff_balls_inter_nonempty {r : ℝ} (hr : 0 < r) (P q : H2) :
    Overlaps r P q ↔ (Metric.ball P r ∩ Metric.ball q r).Nonempty := by sorry

end Paper
end FejesTothP7
