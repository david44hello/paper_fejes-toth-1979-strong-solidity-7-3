/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.LocalGeom

/-!
# Tip-Disc Lemma (`lem_3_2_tip_disc`) and Strict Half-Lens Bound (`lem_3_3_half_lens`)

We prove:
- `lem_3_2_tip_disc`: Every `P ∈ K₂` satisfies `d(P, mid(n₁, n₂)) ≤ r7`, with equality iff
  `P = tip(v; n₁, n₂)`; plus the mirrored form on `K₂'`.
- `lem_3_3_half_lens`: At a `τ₃` site `v`, every admissible point `Y` overlapping both `a` and `v`
  satisfies `d(Y, tip(v; i, b)) < 2 * r7`.
-/

noncomputable section

namespace FejesTothP7.Proofs

/-! ### Elementary concave-quadratic helper (avoids unfolding definitions in `nlinarith`) -/

lemma sq_le_one_of_mem_Icc {y : ℝ} (h : y ∈ Set.Icc (-1 : ℝ) 1) : y ^ 2 ≤ 1 := by
  nlinarith [h.1, h.2]

lemma concave_quad_pos_between_roots {A B C D u1 u2 u : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hu1 : u1 < u) (hu2 : u < u2)
    (hQ1 : C ^ 2 * u1 * (1 - D * u1) - (A + B * u1) ^ 2 = 0)
    (hQ2 : C ^ 2 * u2 * (1 - D * u2) - (A + B * u2) ^ 2 = 0) :
    0 < C ^ 2 * u * (1 - D * u) - (A + B * u) ^ 2 := by
  have hlead : 0 < C ^ 2 * D + B ^ 2 := by positivity
  have hu21 : 0 < u2 - u1 := by linarith
  have h1 : 0 < u - u1 := by linarith
  have h2 : 0 < u2 - u := by linarith
  have hid : (C ^ 2 * u * (1 - D * u) - (A + B * u) ^ 2) * (u2 - u1) =
      (C ^ 2 * D + B ^ 2) * (u2 - u1) * (u - u1) * (u2 - u) +
      (u2 - u) * (C ^ 2 * u1 * (1 - D * u1) - (A + B * u1) ^ 2) +
      (u - u1) * (C ^ 2 * u2 * (1 - D * u2) - (A + B * u2) ^ 2) := by ring
  rw [hQ1, hQ2, mul_zero, mul_zero, add_zero, add_zero] at hid
  have hrhs : 0 < (C ^ 2 * D + B ^ 2) * (u2 - u1) * (u - u1) * (u2 - u) := by positivity
  nlinarith

/-! ### Helper: Core Tip-Disc bound at the origin -/

/-- For `0 < ρ < 2 r7` and `β7 ρ ≤ θ ≤ 3 α7 - β7 ρ`, the distance from `polarOrigin ρ θ`
    to `M = polarOrigin h7 (3 α7 / 2)` is at most `r7`, with equality iff
    `polarOrigin ρ θ = polarOrigin ρ7 (3 α7 / 2)`. -/
lemma tip_disc_origin (ρ θ : ℝ) (hρ0 : 0 < ρ) (hρ2 : ρ < 2 * r7)
    (hlo : β7 ρ ≤ θ) (hhi : θ ≤ 3 * α7 - β7 ρ) :
    dist (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) ≤ r7 ∧
    (dist (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) = r7 ↔
      H2.polarOrigin ρ θ = H2.polarOrigin ρ7 (3 * α7 / 2)) := by
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hρ2.le
  have hα_lt_β : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρ0, hρ2⟩
  have hβ_le : β7 ρ ≤ 3 * α7 / 2 := by linarith
  have hρ7_pos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
  have hρ7_lt : ρ7 < 2 * r7 := text_2_beta_properties.2.2.2.2.2.2.2.1
  have hβρ7 : β7 ρ7 = 3 * α7 / 2 := text_2_beta_properties.2.2.2.2.2.2.2.2
  have hρ_ge : ρ7 ≤ ρ := by
    by_contra hlt; push Not at hlt
    have hgt : β7 ρ7 < β7 ρ :=
      text_2_beta_properties.2.2.1 ⟨hρ0, hρ2.le⟩ ⟨hρ7_pos, hρ7_lt.le⟩ hlt
    linarith
  have hdist_le_bdry :
      H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) ≤
      H2.lorentz (H2.polarOrigin ρ (β7 ρ)) (H2.polarOrigin h7 (3 * α7 / 2)) := by
    rw [lorentz_polarOrigin, lorentz_polarOrigin]
    have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ0
    have hshh : 0 < Real.sinh h7 := Real.sinh_pos_iff.mpr (by linarith [r7_pos, eq_2_order.1, eq_2_order.2.1])
    have habs : |θ - 3 * α7 / 2| ≤ 3 * α7 / 2 - β7 ρ := by
      rw [abs_le]; constructor <;> linarith
    have hpi : 3 * α7 / 2 - β7 ρ ≤ Real.pi := by
      unfold α7 alphaP; linarith [Real.pi_pos]
    have hcos_ge : Real.cos (β7 ρ - 3 * α7 / 2) ≤ Real.cos (θ - 3 * α7 / 2) := by
      have h1 : Real.cos (β7 ρ - 3 * α7 / 2) = Real.cos (3 * α7 / 2 - β7 ρ) := by
        rw [← Real.cos_neg]; congr 1; ring
      have h2 : Real.cos (θ - 3 * α7 / 2) = Real.cos |θ - 3 * α7 / 2| := by
        by_cases hs : 0 ≤ θ - 3 * α7 / 2
        · rw [abs_of_nonneg hs]
        · rw [abs_of_neg (lt_of_not_ge hs), Real.cos_neg]
      rw [h1, h2]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi habs
    nlinarith [mul_pos hshρ hshh]
  have hbdry_strict : ∀ s : ℝ, ρ7 < s → s < 2 * r7 →
      H2.lorentz (H2.polarOrigin s (β7 s)) (H2.polarOrigin h7 (3 * α7 / 2)) < Real.cosh r7 := by
    intro s hs1 hs2
    have hs0 : 0 < s := lt_trans hρ7_pos hs1
    set coth2r := Real.cosh (2 * r7) / Real.sinh (2 * r7)
    have hsh2r : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hcoth_pos : 0 < coth2r := div_pos (Real.cosh_pos _) hsh2r
    have h3a_pos : 0 < 3 * α7 / 2 := by linarith
    have h3a_lt_pi : 3 * α7 / 2 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
    have hsin3a : 0 < Real.sin (3 * α7 / 2) := Real.sin_pos_of_pos_of_lt_pi h3a_pos h3a_lt_pi
    have hshh : 0 < Real.sinh h7 := Real.sinh_pos_iff.mpr (by linarith [r7_pos, eq_2_order.1, eq_2_order.2.1])
    set A : ℝ := Real.cosh h7 - Real.cosh r7
    set B : ℝ := Real.cosh h7 + Real.cosh r7 - 2 * Real.sinh h7 * Real.cos (3 * α7 / 2) * coth2r
    set C : ℝ := 2 * Real.sinh h7 * Real.sin (3 * α7 / 2)
    set D : ℝ := coth2r ^ 2
    have hC_pos : 0 < C := by positivity
    have hD_pos : 0 < D := sq_pos_of_pos hcoth_pos
    have hl_formula : ∀ x : ℝ, 0 < x → x ≤ 2 * r7 →
        (1 - Real.tanh (x / 2) ^ 2) *
          (H2.lorentz (H2.polarOrigin x (β7 x)) (H2.polarOrigin h7 (3 * α7 / 2)) - Real.cosh r7) =
          (A + B * Real.tanh (x / 2) ^ 2) - C * Real.tanh (x / 2) * Real.sqrt (1 - D * Real.tanh (x / 2) ^ 2) := by
      intro x hx0 hx2
      set t := Real.tanh (x / 2)
      have hch_half : 0 < Real.cosh (x / 2) := Real.cosh_pos _
      have hch_sh := Real.cosh_sq_sub_sinh_sq (x / 2)
      have h1mt2 : 1 - t ^ 2 = 1 / Real.cosh (x / 2) ^ 2 := by
        dsimp only [t]; rw [Real.tanh_eq_sinh_div_cosh, div_pow]
        field_simp [hch_half.ne']; linarith
      have hchx : Real.cosh x = (1 + t ^ 2) / (1 - t ^ 2) := by
        have hx : x = 2 * (x / 2) := by ring
        rw [h1mt2]; conv_lhs => rw [hx, Real.cosh_two_mul]
        dsimp only [t]; rw [Real.tanh_eq_sinh_div_cosh, div_pow]
        field_simp [hch_half.ne']
      have hshx : Real.sinh x = 2 * t / (1 - t ^ 2) := by
        have hx : x = 2 * (x / 2) := by ring
        rw [h1mt2]; conv_lhs => rw [hx, Real.sinh_two_mul]
        dsimp only [t]; rw [Real.tanh_eq_sinh_div_cosh]
        field_simp [hch_half.ne']
      have harg := beta7_arg_mem_Icc hx0 hx2
      have hcosβ : Real.cos (β7 x) = coth2r * t := by
        unfold β7 betaP; exact Real.cos_arccos harg.1 harg.2
      have hsinβ : Real.sin (β7 x) = Real.sqrt (1 - D * t ^ 2) := by
        change Real.sin (Real.arccos (coth2r * t)) = Real.sqrt (1 - D * t ^ 2)
        rw [Real.sin_arccos]; congr 1; dsimp only [D]; ring
      have h1mt2_pos : 0 < 1 - t ^ 2 := by rw [h1mt2]; positivity
      rw [lorentz_polarOrigin, Real.cos_sub, hcosβ, hsinβ, hchx, hshx]
      field_simp [h1mt2_pos.ne']
      dsimp only [A, B, C]; ring
    set u1 := Real.tanh (ρ7 / 2) ^ 2
    set u2 := Real.tanh (2 * r7 / 2) ^ 2
    set u := Real.tanh (s / 2) ^ 2
    have hQ1 : C ^ 2 * u1 * (1 - D * u1) - (A + B * u1) ^ 2 = 0 := by
      have hf := hl_formula ρ7 hρ7_pos hρ7_lt.le
      have hl1 : H2.lorentz (H2.polarOrigin ρ7 (β7 ρ7)) (H2.polarOrigin h7 (3 * α7 / 2)) = Real.cosh r7 := by
        rw [hβρ7, lorentz_polarOrigin]
        have : 3 * α7 / 2 - 3 * α7 / 2 = 0 := by ring
        rw [this, Real.cos_zero, mul_one, ← Real.cosh_sub]
        have : ρ7 - h7 = -r7 := by linarith [prop_3_1_exact_identity]
        rw [this, Real.cosh_neg]
      rw [hl1, sub_self, mul_zero] at hf
      have heq_t : A + B * u1 = C * Real.tanh (ρ7 / 2) * Real.sqrt (1 - D * u1) := by
        dsimp only [u1]; linarith
      have h1mD : 0 ≤ 1 - D * u1 := by
        have h1 : (coth2r * Real.tanh (ρ7 / 2)) ^ 2 ≤ 1 :=
          sq_le_one_of_mem_Icc (beta7_arg_mem_Icc hρ7_pos hρ7_lt.le)
        have h2 : D * u1 = (coth2r * Real.tanh (ρ7 / 2)) ^ 2 := by dsimp only [D, u1]; ring
        linarith
      have hsq : (A + B * u1) ^ 2 = (C * Real.tanh (ρ7 / 2) * Real.sqrt (1 - D * u1)) ^ 2 :=
        congrArg (· ^ 2) heq_t
      rw [mul_pow, mul_pow, Real.sq_sqrt h1mD] at hsq
      have hu1_def : Real.tanh (ρ7 / 2) ^ 2 = u1 := rfl
      rw [hu1_def] at hsq
      linarith
    have hQ2 : C ^ 2 * u2 * (1 - D * u2) - (A + B * u2) ^ 2 = 0 := by
      have hf := hl_formula (2 * r7) (by linarith [r7_pos]) (le_refl _)
      have hl2 : H2.lorentz (H2.polarOrigin (2 * r7) (β7 (2 * r7))) (H2.polarOrigin h7 (3 * α7 / 2)) = Real.cosh r7 := by
        rw [text_2_beta_properties.2.2.2.2.1]
        have hM_eq : H2.polarOrigin h7 (3 * α7 / 2) =
            H2.mid (H2.polarOrigin (2 * r7) α7) (H2.polarOrigin (2 * r7) (α7 + α7)) := by
          have : α7 + α7 / 2 = 3 * α7 / 2 := by ring
          rw [← this, mid_polarOrigin_consec]
        rw [hM_eq, lorentz_mid_right, H2.lorentz_self]
        have hl12 : H2.lorentz (H2.polarOrigin (2 * r7) α7) (H2.polarOrigin (2 * r7) (α7 + α7)) =
            Real.cosh (2 * r7) := by
          rw [lorentz_polarOrigin]
          have : α7 - (α7 + α7) = -α7 := by ring
          rw [this, Real.cos_neg, ← text_2_beta_properties.2.1]
          have hsh2 : Real.sinh (2 * r7) * Real.sinh (2 * r7) = Real.cosh (2 * r7) ^ 2 - 1 := by
            linarith [Real.cosh_sq_sub_sinh_sq (2 * r7), sq (Real.sinh (2 * r7))]
          have hden : 0 < Real.cosh (2 * r7) + 1 := by linarith [Real.cosh_pos (2 * r7)]
          field_simp [hden.ne']; nlinarith [hsh2]
        rw [hl12]
        have hdenom : Real.sqrt (2 * (Real.cosh (2 * r7) + 1)) = 2 * Real.cosh r7 := by
          have hcr : 0 ≤ 2 * Real.cosh r7 := by linarith [Real.cosh_pos r7]
          rw [← Real.sqrt_sq hcr]; congr 1; rw [cosh_two_mul']; ring
        rw [hdenom, cosh_two_mul']
        have hcr : 0 < Real.cosh r7 := Real.cosh_pos r7
        field_simp [hcr.ne']; ring
      rw [hl2, sub_self, mul_zero] at hf
      have heq_t : A + B * u2 = C * Real.tanh (2 * r7 / 2) * Real.sqrt (1 - D * u2) := by
        dsimp only [u2]; linarith
      have h1mD : 0 ≤ 1 - D * u2 := by
        have h1 : (coth2r * Real.tanh (2 * r7 / 2)) ^ 2 ≤ 1 :=
          sq_le_one_of_mem_Icc (beta7_arg_mem_Icc (by linarith [r7_pos]) (le_refl (2 * r7)))
        have h2 : D * u2 = (coth2r * Real.tanh (2 * r7 / 2)) ^ 2 := by dsimp only [D, u2]; ring
        linarith
      have hsq : (A + B * u2) ^ 2 = (C * Real.tanh (2 * r7 / 2) * Real.sqrt (1 - D * u2)) ^ 2 :=
        congrArg (· ^ 2) heq_t
      rw [mul_pow, mul_pow, Real.sq_sqrt h1mD] at hsq
      have hu2_def : Real.tanh (2 * r7 / 2) ^ 2 = u2 := rfl
      rw [hu2_def] at hsq
      linarith
    have ht1_pos : 0 < Real.tanh (ρ7 / 2) := tanh_pos_of_pos (by linarith)
    have ht_gt : Real.tanh (ρ7 / 2) < Real.tanh (s / 2) := strictMono_tanh (by linarith)
    have ht_lt : Real.tanh (s / 2) < Real.tanh (2 * r7 / 2) := strictMono_tanh (by linarith)
    have hu1_lt : u1 < u := by
      simpa [u1, u, sq] using mul_lt_mul'' ht_gt ht_gt ht1_pos.le ht1_pos.le
    have hu_lt : u < u2 := by
      have ht_pos : 0 < Real.tanh (s / 2) := lt_trans ht1_pos ht_gt
      simpa [u, u2, sq] using mul_lt_mul'' ht_lt ht_lt ht_pos.le ht_pos.le
    have hQ_pos : 0 < C ^ 2 * u * (1 - D * u) - (A + B * u) ^ 2 :=
      concave_quad_pos_between_roots hC_pos hD_pos hu1_lt hu_lt hQ1 hQ2
    have h1mD : 0 ≤ 1 - D * u := by
      have h1 : (coth2r * Real.tanh (s / 2)) ^ 2 ≤ 1 :=
        sq_le_one_of_mem_Icc (beta7_arg_mem_Icc hs0 hs2.le)
      have h2 : D * u = (coth2r * Real.tanh (s / 2)) ^ 2 := by dsimp only [D, u]; ring
      linarith
    have hrhs_pos : 0 ≤ C * Real.tanh (s / 2) * Real.sqrt (1 - D * u) := by
      have ht_pos : 0 < Real.tanh (s / 2) := tanh_pos_of_pos (by linarith)
      positivity
    have hsq_lt : (A + B * u) ^ 2 < (C * Real.tanh (s / 2) * Real.sqrt (1 - D * u)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h1mD]
      have hu_def : Real.tanh (s / 2) ^ 2 = u := rfl
      rw [hu_def]
      linarith
    have hAB_lt : A + B * u < C * Real.tanh (s / 2) * Real.sqrt (1 - D * u) := by
      have habs_lt : |A + B * u| < |C * Real.tanh (s / 2) * Real.sqrt (1 - D * u)| :=
        sq_lt_sq.mp hsq_lt
      rw [abs_of_nonneg hrhs_pos] at habs_lt
      exact lt_of_le_of_lt (le_abs_self _) habs_lt
    have hf := hl_formula s hs0 hs2.le
    have h1mt2_pos : 0 < 1 - u := by
      have ht1 : Real.tanh (s / 2) < 1 := Real.tanh_lt_one _
      have ht0 : 0 < Real.tanh (s / 2) := tanh_pos_of_pos (by linarith)
      have hsq1 : u < 1 := by simpa [u, sq] using mul_lt_mul'' ht1 ht1 ht0.le ht0.le
      linarith
    have hneg : (1 - u) * (H2.lorentz (H2.polarOrigin s (β7 s)) (H2.polarOrigin h7 (3 * α7 / 2)) - Real.cosh r7) < 0 := by
      have hu_def : Real.tanh (s / 2) ^ 2 = u := rfl
      rw [hu_def] at hf
      linarith
    have hsub_neg : H2.lorentz (H2.polarOrigin s (β7 s)) (H2.polarOrigin h7 (3 * α7 / 2)) - Real.cosh r7 < 0 :=
      (mul_neg_iff.mp hneg).resolve_right (fun h => not_lt.mpr h1mt2_pos.le h.1) |>.2
    linarith
  have hle_lorentz : H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) ≤ Real.cosh r7 := by
    by_cases hρeq : ρ = ρ7
    · subst hρeq
      have hθeq : θ = 3 * α7 / 2 := by linarith
      rw [hθeq, lorentz_polarOrigin]
      have : 3 * α7 / 2 - 3 * α7 / 2 = 0 := by ring
      rw [this, Real.cos_zero, mul_one, ← Real.cosh_sub]
      have : ρ7 - h7 = -r7 := by linarith [prop_3_1_exact_identity]
      rw [this, Real.cosh_neg]
    · exact le_trans hdist_le_bdry (hbdry_strict ρ (lt_of_le_of_ne hρ_ge (Ne.symm hρeq)) hρ2).le
  have hdist_le : dist (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) ≤ r7 := by
    rw [H2.dist_eq_arcosh, ← Real.arcosh_cosh r7_pos.le]
    exact (Real.arcosh_le_arcosh (by linarith [H2.one_le_lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2))])
      (Real.cosh_pos _)).mpr hle_lorentz
  refine ⟨hdist_le, ?_⟩
  constructor
  · intro heq
    have hρeq : ρ = ρ7 := by
      by_contra hne
      have hlt := lt_of_le_of_lt hdist_le_bdry (hbdry_strict ρ (lt_of_le_of_ne hρ_ge (Ne.symm hne)) hρ2)
      have hce : H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin h7 (3 * α7 / 2)) = Real.cosh r7 := by
        rw [← H2.cosh_dist, heq]
      linarith
    subst hρeq
    have hθeq : θ = 3 * α7 / 2 := by linarith
    rw [hθeq]
  · intro heq
    rw [heq, H2.dist_eq_arcosh, lorentz_polarOrigin]
    have : 3 * α7 / 2 - 3 * α7 / 2 = 0 := by ring
    rw [this, Real.cos_zero, mul_one, ← Real.cosh_sub]
    have : ρ7 - h7 = -r7 := by linarith [prop_3_1_exact_identity]
    rw [this, Real.cosh_neg, Real.arcosh_cosh r7_pos.le]

/-- **Lemma 3.2 (Tip-Disc Lemma, standard & mirror forms)**. -/
theorem lem_3_2_tip_disc (V : Set H2) (v : H2) (F : SiteFrame V v) :
    (∀ P ∈ F.K2, dist P (H2.mid (F.nbr 1) (F.nbr 2)) ≤ r7 ∧
      (dist P (H2.mid (F.nbr 1) (F.nbr 2)) = r7 ↔ P = F.tip12)) ∧
    (∀ P ∈ F.K2Mirror, dist P (H2.mid (F.nbr 0) (F.nbr 1)) ≤ r7 ∧
      (dist P (H2.mid (F.nbr 0) (F.nbr 1)) = r7 ↔ P = F.tip01)) := by
  have hM12 : H2.mid (F.nbr 1) (F.nbr 2) = F.polar h7 (3 * α7 / 2) := by
    unfold SiteFrame.nbr SiteFrame.polar
    rw [← isometry_mid]
    congr 1
    have h1 : ((1 : ℤ) : ℝ) * α7 = α7 := by norm_num
    have h2 : ((2 : ℤ) : ℝ) * α7 = α7 + α7 := by norm_num; ring
    have h3 : α7 + α7 / 2 = 3 * α7 / 2 := by ring
    rw [h1, h2, ← h3]
    exact mid_polarOrigin_consec α7
  have hM01 : H2.mid (F.nbr 0) (F.nbr 1) = F.polar h7 (α7 / 2) := by
    unfold SiteFrame.nbr SiteFrame.polar
    rw [← isometry_mid]
    congr 1
    have h0 : ((0 : ℤ) : ℝ) * α7 = 0 := by norm_num
    have h1 : ((1 : ℤ) : ℝ) * α7 = 0 + α7 := by norm_num
    have h2 : 0 + α7 / 2 = α7 / 2 := by ring
    rw [h0, h1, ← h2]
    exact mid_polarOrigin_consec 0
  constructor
  · rintro P ⟨ρ, θ, hρ0, hρ2, hlo, hhi, rfl⟩
    rw [hM12]
    unfold SiteFrame.tip12 SiteFrame.polar
    rw [F.φ.dist_eq, F.φ.injective.eq_iff]
    exact tip_disc_origin ρ θ hρ0 hρ2 hlo hhi
  · rintro P ⟨ρ, θ, hρ0, hρ2, hlo, hhi, rfl⟩
    rw [hM01]
    unfold SiteFrame.tip01 SiteFrame.polar
    rw [F.φ.dist_eq, F.φ.injective.eq_iff]
    have hrot : ∀ r a : ℝ, H2.rotOrigin α7 (H2.polarOrigin r a) = H2.polarOrigin r (a + α7) := by
      intro r a
      ext <;> simp [H2.polarOrigin, Real.cos_add, Real.sin_add] <;> ring
    rw [← (H2.rotOrigin α7).dist_eq, ← (H2.rotOrigin α7).injective.eq_iff,
        hrot, hrot, hrot]
    have h3a : α7 / 2 + α7 = 3 * α7 / 2 := by ring
    rw [h3a]
    exact tip_disc_origin ρ (θ + α7) hρ0 hρ2 (by linarith) (by linarith)

/-! ### Lemma 3.3: Strict Half-Lens Bound -/

/-- **Lemma 3.3 (Strict Half-Lens Bound)**. -/
theorem lem_3_3_half_lens (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F)
    (Y : H2) (hadm : IsAdmissible r7 (V \ U) Y)
    (hYa : Overlaps r7 Y (F.nbr 0)) (hYv : Overlaps r7 Y v) :
    dist Y F.tip12 < 2 * r7 := by
  by_cases hYv_eq : Y = v
  · subst hYv_eq
    have hd : dist Y F.tip12 = ρ7 := by
      calc dist Y F.tip12
          = dist (F.φ H2.origin) (F.φ (H2.polarOrigin ρ7 (3 * α7 / 2))) := by
            rw [F.origin_eq, SiteFrame.tip12, SiteFrame.polar]
        _ = dist H2.origin (H2.polarOrigin ρ7 (3 * α7 / 2)) := F.φ.dist_eq _ _
        _ = ρ7 := dist_origin_polarOrigin ρ7 (3 * α7 / 2) text_2_beta_properties.2.2.2.2.2.2.1.le
    rw [hd]
    exact text_2_beta_properties.2.2.2.2.2.2.2.1
  · set ρ := dist Y v
    have hρ0 : 0 < ρ := dist_pos.mpr hYv_eq
    have hρ2 : ρ < 2 * r7 := hYv
    have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hρ2.le
    have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
    have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
    obtain ⟨θ, hY_eq, hlo, _, _, hov0, _, _, _⟩ :=
      lem_2_3_freearc_b V U v F hprof Y hYv_eq hρ2 hadm
    have hθ_lt_β : θ < β7 ρ := hov0.mp hYa
    have hα_lt_β : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρ0, hρ2⟩
    have hθ_pos : 0 < θ := by linarith
    have habs_lt : |θ - 3 * α7 / 2| < 3 * α7 / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have hcos_gt : Real.cos (3 * α7 / 2) < Real.cos (θ - 3 * α7 / 2) := by
      have h1 : Real.cos (θ - 3 * α7 / 2) = Real.cos |θ - 3 * α7 / 2| := by
        by_cases hs : 0 ≤ θ - 3 * α7 / 2
        · rw [abs_of_nonneg hs]
        · rw [abs_of_neg (lt_of_not_ge hs), Real.cos_neg]
      rw [h1]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) habs_lt
    rw [hY_eq]
    unfold SiteFrame.tip12 SiteFrame.polar
    rw [F.φ.dist_eq, H2.dist_eq_arcosh, ← Real.arcosh_cosh (by linarith [r7_pos] : 0 ≤ 2 * r7)]
    rw [Real.arcosh_lt_arcosh
      (by linarith [H2.one_le_lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin ρ7 (3 * α7 / 2))])
      (Real.cosh_pos _)]
    have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ0
    have hshρ7 : 0 < Real.sinh ρ7 := Real.sinh_pos_iff.mpr text_2_beta_properties.2.2.2.2.2.2.1
    have hstep1 : H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin ρ7 (3 * α7 / 2)) <
        H2.lorentz (H2.polarOrigin ρ 0) (H2.polarOrigin ρ7 (3 * α7 / 2)) := by
      rw [lorentz_polarOrigin, lorentz_polarOrigin]
      have h0 : Real.cos (0 - 3 * α7 / 2) = Real.cos (3 * α7 / 2) := by rw [zero_sub, Real.cos_neg]
      rw [h0]
      nlinarith [mul_pos hshρ hshρ7]
    have hstep2 : H2.lorentz (H2.polarOrigin ρ 0) (H2.polarOrigin ρ7 (3 * α7 / 2)) < Real.cosh (2 * r7) := by
      set P0 := H2.polarOrigin ρ 0
      set O := H2.origin
      set A := H2.polarOrigin (2 * r7) 0
      set T0 := H2.polarOrigin ρ7 (3 * α7 / 2)
      have hsh2r : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
      set c1 := Real.sinh (2 * r7 - ρ) / Real.sinh (2 * r7)
      set c2 := Real.sinh ρ / Real.sinh (2 * r7)
      have hc1 : 0 < c1 := div_pos (Real.sinh_pos_iff.mpr (by linarith)) hsh2r
      have hc2 : 0 < c2 := div_pos hshρ hsh2r
      have hP0x : P0.x = c1 * O.x + c2 * A.x := by
        simp only [P0, O, A, H2.polarOrigin, H2.origin, Real.cos_zero, mul_one, mul_zero, zero_add, c2]
        field_simp [hsh2r.ne']
      have hP0y : P0.y = c1 * O.y + c2 * A.y := by
        simp [P0, O, A, H2.polarOrigin, H2.origin]
      have hP0z : P0.z = c1 * O.z + c2 * A.z := by
        simp only [P0, O, A, H2.polarOrigin, H2.origin, mul_one, c1, c2]
        rw [Real.sinh_sub]
        field_simp [hsh2r.ne']
        have hch2 := Real.cosh_sq_sub_sinh_sq (2 * r7)
        nlinarith
      have hsum_le : c1 + c2 ≤ 1 := by
        have h1 : H2.lorentz P0 P0 = c1 * H2.lorentz P0 O + c2 * H2.lorentz P0 A := by
          unfold H2.lorentz; rw [hP0x, hP0y, hP0z]; ring
        rw [H2.lorentz_self] at h1
        nlinarith [H2.one_le_lorentz P0 O, H2.one_le_lorentz P0 A]
      have hlOT : H2.lorentz O T0 < Real.cosh (2 * r7) := by
        have h1 : H2.lorentz O T0 = Real.cosh ρ7 := by unfold H2.lorentz O T0 H2.origin H2.polarOrigin; dsimp; ring
        rw [h1]
        have hρ7_pos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
        have hρ7_lt : ρ7 < 2 * r7 := text_2_beta_properties.2.2.2.2.2.2.2.1
        rw [← Real.arcosh_lt_arcosh (Real.cosh_pos _) (Real.cosh_pos _),
            Real.arcosh_cosh hρ7_pos.le, Real.arcosh_cosh (by linarith [r7_pos])]
        exact hρ7_lt
      have hlAT : H2.lorentz A T0 = Real.cosh (2 * r7) := by
        have h5 := (eq_5_tip_distances V v F).2.1
        unfold SiteFrame.tip12 SiteFrame.polar SiteFrame.nbr at h5
        rw [F.φ.dist_eq] at h5
        have h0 : ((0 : ℤ) : ℝ) * α7 = 0 := by norm_num
        rw [h0] at h5
        rw [H2.lorentz_symm, ← H2.cosh_dist, h5]
      have hlP0T : H2.lorentz P0 T0 = c1 * H2.lorentz O T0 + c2 * H2.lorentz A T0 := by
        unfold H2.lorentz; rw [hP0x, hP0y, hP0z]; ring
      nlinarith [Real.cosh_pos (2 * r7)]
    exact lt_trans hstep1 hstep2

end FejesTothP7.Proofs
