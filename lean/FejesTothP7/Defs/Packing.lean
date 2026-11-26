/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Defs.H2
import Mathlib.Data.Finset.Card

/-!
# Circle Packings, Finite Rearrangements, Solidity, and Saturatedness

Exact definitions of congruent open-disc packings in `H2`, finite rearrangements,
congruence, solidity, strong solidity, `k`-truncations, solidity of order `k`,
order of solidity, and grade of saturatedness.
-/

noncomputable section

namespace FejesTothP7

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

/-- Relative to a fixed/unfixed decomposition with fixed set `F`, a point `P` is admissible
    if `dist P f ≥ 2 r` for every fixed site `f ∈ F`. -/
def IsAdmissible (r : ℝ) (F : Set H2) (P : H2) : Prop :=
  ∀ f ∈ F, 2 * r ≤ dist P f

/-- A point `P` overlaps a site `q` if `dist P q < 2 r`. -/
def Overlaps (r : ℝ) (P q : H2) : Prop :=
  dist P q < 2 * r

end FejesTothP7
