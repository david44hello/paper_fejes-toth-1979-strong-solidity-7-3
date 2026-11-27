module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Proofs.ExactIdentity

@[expose] public section

/-!
# The Metric Gap `Δ_p` for `{p, 3}` (`p ≥ 7`) and Figure 2 Regime Split

We prove:
- `text_1_metric_gap_p_ge_8`: for all `p ≥ 8`, `Δ_p < 0` and `|h_p - ρ_p^*| < r_p`.
- `fig_2_caption_regime_split`: for `7 ≤ p ≤ 14`, `ρ_p^* ≤ h_p` with `h_14 = ρ_14^*`;
  for `p ≥ 15`, `ρ_p^* < 2 r_p < h_p + r_p`.
-/

noncomputable section

namespace FejesTothP7.Proofs

/-- `ρ_p^* < 2 r_p` for every `p ≥ 7`. -/
lemma rhoStarP_lt_two_rP {p : ℕ} (hp : 7 ≤ p) : rhoStarP p < 2 * rP p := by
  have h1 : Real.tanh (rhoStarP p / 2) < Real.tanh (rP p) := by
    rw [tanh_half_rhoStarP_lambda hp, Real.tanh_eq_sinh_div_cosh,
        sinh_rP_lambda hp, cosh_rP_lambda hp]
    have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
    have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
    have hrt4 : 0 < Real.sqrt (4 - lambdaP p ^ 2) := Real.sqrt_pos.mpr hsq
    have hrt3 : 0 < Real.sqrt (lambdaP p ^ 2 - 3) := Real.sqrt_pos.mpr h3
    have h2 : 0 < lambdaP p ^ 2 - 2 := by linarith [(lambdaP_sq_bounds hp).1]
    have hrhs : Real.sqrt (lambdaP p ^ 2 - 3) / Real.sqrt (4 - lambdaP p ^ 2) /
        (1 / Real.sqrt (4 - lambdaP p ^ 2)) = Real.sqrt (lambdaP p ^ 2 - 3) := by
      field_simp [hrt4.ne']
    rw [hrhs, div_lt_iff₀ h2]
    have hlt : lambdaP p ^ 3 - 3 * lambdaP p < lambdaP p ^ 2 - 2 := by
      have hlo := (lambdaP_bounds hp).1
      have hhi := (lambdaP_bounds hp).2
      have hpos : 0 < lambdaP p ^ 2 + lambdaP p - 1 := by
        linarith [(lambdaP_sq_bounds hp).1, Real.sqrt_nonneg 3]
      nlinarith
    have hmul := mul_lt_mul_of_pos_right hlt hrt3
    linarith
  have h2 : rhoStarP p / 2 < rP p := strictMono_tanh.lt_iff_lt.mp h1
  linarith

/-- **Section 1 & Figure 2 caption**: For every `p ≥ 8`, `Δ_p < 0` and `|h_p - ρ_p^*| < r_p`. -/
theorem text_1_metric_gap_p_ge_8 (p : ℕ) (hp : 8 ≤ p) :
    deltaP p < 0 ∧ |hP p - rhoStarP p| < rP p := by
  have hp7 : 7 ≤ p := by omega
  have hlam_gt : lambdaP 7 < lambdaP p := by
    unfold lambdaP
    have hlt : Real.pi / (p : ℝ) < Real.pi / (7 : ℝ) := by
      have hp_gt : (7 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 7 < p)
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hp_gt
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (pi_div_p_pos hp7).le
      (by linarith [Real.pi_pos]) hlt
    have h7 : ((7 : ℕ) : ℝ) = 7 := by norm_num
    rw [h7]
    linarith
  have hcub_pos : 0 < lambdaP p ^ 3 - lambdaP p ^ 2 - 2 * lambdaP p + 1 := by
    have hcub7 := lambda7_cubic
    have h7sq := lambdaP_sq_bounds (by norm_num : 7 ≤ 7)
    have hpsq := lambdaP_sq_bounds hp7
    have h7b := lambdaP_bounds (by norm_num : 7 ≤ 7)
    have hpb := lambdaP_bounds hp7
    have hdiff : (lambdaP p ^ 3 - lambdaP p ^ 2 - 2 * lambdaP p + 1) -
        (lambdaP 7 ^ 3 - lambdaP 7 ^ 2 - 2 * lambdaP 7 + 1) =
        (lambdaP p - lambdaP 7) *
          (lambdaP p ^ 2 + lambdaP p * lambdaP 7 + lambdaP 7 ^ 2 - lambdaP p - lambdaP 7 - 2) := by
      ring
    have hprod : 3 < lambdaP p * lambdaP 7 := by
      have := mul_lt_mul'' hpb.1 h7b.1 (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)
      rwa [Real.mul_self_sqrt (by norm_num)] at this
    have hfac : 0 < lambdaP p ^ 2 + lambdaP p * lambdaP 7 + lambdaP 7 ^ 2 - lambdaP p - lambdaP 7 - 2 := by
      linarith [h7sq.1, hpsq.1, h7b.2, hpb.2, hprod]
    nlinarith
  have ht_lt : Real.tanh ((hP p - rP p) / 2) < Real.tanh (rhoStarP p / 2) := by
    rw [tanh_half_hP_sub_rP_lambda hp7, tanh_half_rhoStarP_lambda hp7]
    have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp7).1]
    have hrt3 : 0 < Real.sqrt (lambdaP p ^ 2 - 3) := Real.sqrt_pos.mpr h3
    have hlam1 : 0 < lambdaP p + 1 := by linarith [(lambdaP_bounds hp7).1, Real.sqrt_nonneg 3]
    have hlam2 : 0 < lambdaP p ^ 2 - 2 := by linarith [(lambdaP_sq_bounds hp7).1]
    rw [div_lt_div_iff₀ hlam1 hlam2]
    have hfac : (lambdaP p ^ 3 - 3 * lambdaP p) * (lambdaP p + 1) - (lambdaP p ^ 2 - 2) =
        (lambdaP p + 2) * (lambdaP p ^ 3 - lambdaP p ^ 2 - 2 * lambdaP p + 1) := by ring
    have hlam_p2 : 0 < lambdaP p + 2 := by linarith
    have hineq : lambdaP p ^ 2 - 2 < (lambdaP p ^ 3 - 3 * lambdaP p) * (lambdaP p + 1) := by
      nlinarith [hfac, hcub_pos, hlam_p2]
    nlinarith [mul_lt_mul_of_pos_right hineq hrt3]
  have hΔ : deltaP p < 0 := by
    have hlt := strictMono_tanh.lt_iff_lt.mp ht_lt
    unfold deltaP
    linarith
  have habs : |hP p - rhoStarP p| < rP p := by
    rw [abs_lt]
    constructor
    · have h1 := rhoStarP_lt_two_rP hp7
      have h2 := rP_lt_hP hp7
      linarith
    · unfold deltaP at hΔ
      linarith
  exact ⟨hΔ, habs⟩

/-- Exact cubic root identity at `p = 14`: `2 sin(π / 14)` satisfies `X³ - X² - 2X + 1 = 0`. -/
lemma two_sin_pi_div_14_cubic :
    let X := 2 * Real.sin (Real.pi / 14)
    X ^ 3 - X ^ 2 - 2 * X + 1 = 0 := by
  dsimp only
  have h14 : Real.sin (Real.pi / 14) = Real.cos (3 * Real.pi / 7) := by
    rw [← Real.cos_pi_div_two_sub]
    congr 1; ring
  rw [h14]
  have hc3 : 2 * Real.cos (3 * Real.pi / 7) = lambdaP 7 ^ 3 - 3 * lambdaP 7 := by
    simpa using two_cos_three_pi_div_p (p := 7)
  have hcub := lambda7_cubic
  have hX : 2 * Real.cos (3 * Real.pi / 7) = lambdaP 7 ^ 2 - lambdaP 7 - 1 := by linarith
  rw [hX]
  set l := lambdaP 7
  have hcub' : l ^ 3 - l ^ 2 - 2 * l + 1 = 0 := hcub
  linear_combination (l ^ 3 - 2 * l ^ 2 - l + 1) * hcub'

/-- Sign characterization of `ρ_p^* ≤ h_p` via `f(2 sin(π/p)) ≤ 0` where `f(X) = X³ - X² - 2X + 1`. -/
lemma tanh_half_rhoStarP_sub_tanh_half_hP_sign {p : ℕ} (hp : 7 ≤ p) :
    let s := Real.sin (Real.pi / (p : ℝ))
    (rhoStarP p ≤ hP p ↔ (2 * s) ^ 3 - (2 * s) ^ 2 - 2 * (2 * s) + 1 ≤ 0) ∧
    (hP p = rhoStarP p ↔ (2 * s) ^ 3 - (2 * s) ^ 2 - 2 * (2 * s) + 1 = 0) := by
  dsimp only
  set s := Real.sin (Real.pi / (p : ℝ))
  set c := Real.cos (Real.pi / (p : ℝ))
  have hs_pos : 0 < s := sin_pi_div_p_pos hp
  have hs_half : s < 1 / 2 := sin_pi_div_p_lt_half hp
  have hc_pos : 0 < c := by
    have : 0 < lambdaP p := lt_trans (Real.sqrt_pos.mpr (by norm_num)) (lambdaP_bounds hp).1
    unfold lambdaP at this; linarith
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hsq : 0 < 4 - lambdaP p ^ 2 := by linarith [(lambdaP_sq_bounds hp).2]
  have h3 : 0 < lambdaP p ^ 2 - 3 := by linarith [(lambdaP_sq_bounds hp).1]
  have hrt3 : 0 < Real.sqrt (lambdaP p ^ 2 - 3) := Real.sqrt_pos.mpr h3
  have h2s_eq : 2 * s = Real.sqrt (4 - lambdaP p ^ 2) := two_sin_eq_sqrt hp
  have h4s2 : 4 * s ^ 2 = 4 - lambdaP p ^ 2 := four_sin_sq_eq
  have h1m2s2 : 0 < 1 - 2 * s ^ 2 := by nlinarith
  have hden2 : 0 < 1 - 2 * s ^ 2 + s := by nlinarith
  have hrho : Real.tanh (rhoStarP p / 2) =
      c * (1 - 4 * s ^ 2) * Real.sqrt (lambdaP p ^ 2 - 3) / (1 - 2 * s ^ 2) := by
    rw [tanh_half_rhoStarP_lambda hp]
    have hlam : lambdaP p = 2 * c := rfl
    have hnum : lambdaP p ^ 3 - 3 * lambdaP p = 2 * c * (1 - 4 * s ^ 2) := by
      rw [hlam]; nlinarith [hcs]
    have hden : lambdaP p ^ 2 - 2 = 2 * (1 - 2 * s ^ 2) := by
      rw [hlam]; nlinarith [hcs]
    rw [hnum, hden]
    field_simp [h1m2s2.ne']
  have hh : Real.tanh (hP p / 2) =
      c * Real.sqrt (lambdaP p ^ 2 - 3) / (1 - 2 * s ^ 2 + s) := by
    have hhalf : Real.tanh (hP p / 2) = Real.sinh (hP p) / (Real.cosh (hP p) + 1) := by
      have hch_pos : 0 < Real.cosh (hP p / 2) := Real.cosh_pos _
      have hx : hP p = 2 * (hP p / 2) := by ring
      rw [Real.tanh_eq_sinh_div_cosh]
      conv_rhs => rw [hx, Real.sinh_two_mul, cosh_two_mul']
      field_simp [hch_pos.ne']
      ring
    rw [hhalf, sinh_hP_lambda hp, cosh_hP_lambda hp, ← h2s_eq]
    have hlam : lambdaP p = 2 * c := rfl
    have hden : lambdaP p ^ 2 - 2 = 2 * (1 - 2 * s ^ 2) := by
      rw [hlam]; nlinarith [hcs]
    rw [hden, hlam]
    field_simp [hs_pos.ne', hden2.ne']
  have hcross :
      c * (1 - 4 * s ^ 2) * (1 - 2 * s ^ 2 + s) - c * (1 - 2 * s ^ 2) =
      c * s * ((2 * s) ^ 3 - (2 * s) ^ 2 - 2 * (2 * s) + 1) := by ring
  constructor
  · rw [show (rhoStarP p ≤ hP p) ↔ (rhoStarP p / 2 ≤ hP p / 2) by constructor <;> intro h <;> linarith]
    rw [← strictMono_tanh.le_iff_le, hrho, hh, div_le_div_iff₀ h1m2s2 hden2]
    constructor
    · intro hle
      have h1 : c * (1 - 4 * s ^ 2) * (1 - 2 * s ^ 2 + s) ≤ c * (1 - 2 * s ^ 2) := by
        nlinarith [hrt3]
      have h2 : c * s * ((2 * s) ^ 3 - (2 * s) ^ 2 - 2 * (2 * s) + 1) ≤ 0 := by linarith [hcross]
      nlinarith [mul_pos hc_pos hs_pos]
    · intro hle
      have h1 : c * (1 - 4 * s ^ 2) * (1 - 2 * s ^ 2 + s) ≤ c * (1 - 2 * s ^ 2) := by
        nlinarith [hcross, mul_pos hc_pos hs_pos]
      nlinarith [hrt3]
  · rw [show (hP p = rhoStarP p) ↔ (rhoStarP p / 2 = hP p / 2) by constructor <;> intro h <;> linarith]
    rw [← Real.tanh_injective.eq_iff, hrho, hh, div_eq_div_iff h1m2s2.ne' hden2.ne']
    constructor
    · intro heq
      have h1 : c * (1 - 4 * s ^ 2) * (1 - 2 * s ^ 2 + s) = c * (1 - 2 * s ^ 2) := by
        nlinarith [hrt3]
      have h2 : c * s * ((2 * s) ^ 3 - (2 * s) ^ 2 - 2 * (2 * s) + 1) = 0 := by linarith [hcross]
      rcases mul_eq_zero.mp h2 with hcs0 | h0
      · linarith [mul_pos hc_pos hs_pos]
      · exact h0
    · intro heq
      have h1 : c * (1 - 4 * s ^ 2) * (1 - 2 * s ^ 2 + s) = c * (1 - 2 * s ^ 2) := by
        rw [heq, mul_zero] at hcross; linarith
      nlinarith [h1]

/-- **Figure 2 caption**: Regime split at `p = 14` (`7 ≤ p ≤ 14` vs `p ≥ 15`). -/
theorem fig_2_caption_regime_split :
    (∀ p : ℕ, 7 ≤ p → p ≤ 14 → rhoStarP p ≤ hP p) ∧
    hP 14 = rhoStarP 14 ∧
    (∀ p : ℕ, 15 ≤ p → rhoStarP p < 2 * rP p ∧ 2 * rP p < hP p + rP p) := by
  have h14_eq : hP 14 = rhoStarP 14 := by
    rw [(tanh_half_rhoStarP_sub_tanh_half_hP_sign (by norm_num : 7 ≤ 14)).2]
    simpa using two_sin_pi_div_14_cubic
  refine ⟨?_, h14_eq, ?_⟩
  · intro p hp7 hp14
    rw [(tanh_half_rhoStarP_sub_tanh_half_hP_sign hp7).1]
    set X := 2 * Real.sin (Real.pi / (p : ℝ))
    set X14 := 2 * Real.sin (Real.pi / 14)
    have hX14_cub : X14 ^ 3 - X14 ^ 2 - 2 * X14 + 1 = 0 := two_sin_pi_div_14_cubic
    have hX_ge : X14 ≤ X := by
      have hle : Real.pi / 14 ≤ Real.pi / (p : ℝ) := by
        have hp_le : (p : ℝ) ≤ 14 := by exact_mod_cast hp14
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
        exact div_le_div_of_nonneg_left Real.pi_pos.le hp_pos hp_le
      have hsin : Real.sin (Real.pi / 14) ≤ Real.sin (Real.pi / (p : ℝ)) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
          (by linarith [pi_div_p_lt_pi_div_six hp7, Real.pi_pos]) hle
      linarith
    have hX_lt1 : X < 1 := by linarith [sin_pi_div_p_lt_half hp7]
    have hX14_pos : 0 < X14 := by linarith [sin_pi_div_p_pos (by norm_num : 7 ≤ 14)]
    have hX14_lt1 : X14 < 1 := by linarith [sin_pi_div_p_lt_half (by norm_num : 7 ≤ 14)]
    have hfac : X ^ 2 + X * X14 + X14 ^ 2 - X - X14 - 2 < 0 := by
      have hprod : X * X14 < 1 := by nlinarith
      nlinarith
    have hdiff : (X ^ 3 - X ^ 2 - 2 * X + 1) - (X14 ^ 3 - X14 ^ 2 - 2 * X14 + 1) =
        (X - X14) * (X ^ 2 + X * X14 + X14 ^ 2 - X - X14 - 2) := by ring
    nlinarith
  · intro p hp15
    have hp7 : 7 ≤ p := by omega
    exact ⟨rhoStarP_lt_two_rP hp7, by linarith [rP_lt_hP hp7]⟩

end FejesTothP7.Proofs
