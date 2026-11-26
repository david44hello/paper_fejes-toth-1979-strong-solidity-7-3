/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Geometric Constants for Regular Hyperbolic `{p, 3}` Tilings (`p ≥ 7`)

Exact definitions of the face-inradius `r_p`, dual equilateral triangle altitude `h_p`,
circumradius `Rc7`, angular half-width `beta_p`, critical polar radius `rhoStar_p`,
and metric gap `delta_p`, with specialized aliases `α7, r7, h7, Rc7, β7, ρ7` for `p = 7`.
-/

noncomputable section

namespace FejesTothP7

/-- Vertex angle `2π / p` of an equilateral triangle in the dual triangulation `{3, p}`. -/
def alphaP (p : ℕ) : ℝ := 2 * Real.pi / (p : ℝ)

/-- Face-inradius `r_p` of the regular hyperbolic tiling `{p, 3}` (`p ≥ 7`). -/
def rP (p : ℕ) : ℝ := Real.arcosh (1 / (2 * Real.sin (Real.pi / (p : ℝ))))

/-- Altitude `h_p` of an equilateral triangle of side `2 r_p` in `{3, p}`. -/
def hP (p : ℕ) : ℝ := Real.arcosh (Real.cosh (2 * rP p) / Real.cosh (rP p))

/-- Angular half-width `β_p(ρ) = arccos(coth(2 r_p) * tanh(ρ / 2))`. -/
def betaP (p : ℕ) (ρ : ℝ) : ℝ :=
  Real.arccos ((Real.cosh (2 * rP p) / Real.sinh (2 * rP p)) * Real.tanh (ρ / 2))

/-- Critical polar radius `ρ_p^* = 2 artanh(tanh(2 r_p) cos(3π / p))`. -/
def rhoStarP (p : ℕ) : ℝ :=
  2 * Real.artanh (Real.tanh (2 * rP p) * Real.cos (3 * Real.pi / (p : ℝ)))

/-- The metric gap `Δ_p = h_p - (r_p + ρ_p^*)`. -/
def deltaP (p : ℕ) : ℝ := hP p - (rP p + rhoStarP p)

/-- Specialized constants for `p = 7`. -/
def α7 : ℝ := alphaP 7
def r7 : ℝ := rP 7
def h7 : ℝ := hP 7
def Rc7 : ℝ := Real.arsinh (Real.sinh r7 / Real.sin (Real.pi / 3))
def β7 (ρ : ℝ) : ℝ := betaP 7 ρ
def ρ7 : ℝ := rhoStarP 7

lemma sin_pi_div_seven_pos : 0 < Real.sin (Real.pi / 7) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [Real.pi_pos]

lemma sin_pi_div_seven_lt_half : Real.sin (Real.pi / 7) < 1 / 2 := by
  rw [← Real.sin_pi_div_six]
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

lemma one_lt_inv_two_sin_pi_div_seven : 1 < 1 / (2 * Real.sin (Real.pi / 7)) := by
  have hpos : 0 < 2 * Real.sin (Real.pi / 7) := by linarith [sin_pi_div_seven_pos]
  rw [one_lt_div hpos]
  linarith [sin_pi_div_seven_lt_half]

lemma r7_pos : 0 < r7 :=
  Real.arcosh_pos one_lt_inv_two_sin_pi_div_seven

end FejesTothP7
