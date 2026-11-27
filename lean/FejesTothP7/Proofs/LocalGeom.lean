module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Proofs.ExactIdentity

@[expose] public section

/-!
# Local Hyperbolic Geometric Lemmas (Section 2.3)

We prove:
- `lem_2_2_polar` (Polar Lemma)
- `lem_2_3_freearc_a`, `_b`, `_c`, `_d`, `_d_conseq` (Free-Arc Lemma)
- `lem_2_4_edge` (Edge Lemma, parts i & ii)
- `lem_2_5_reuleaux` (Reuleaux-Triangle Lemma)
-/

noncomputable section

namespace FejesTothP7.Proofs

/-! ### Coordinate simp helpers for `H2` isometries -/

@[simp] lemma reflXAxis_x (p : H2) : (H2.reflXAxis p).x = p.x := rfl
@[simp] lemma reflXAxis_y (p : H2) : (H2.reflXAxis p).y = -p.y := rfl
@[simp] lemma reflXAxis_z (p : H2) : (H2.reflXAxis p).z = p.z := rfl

@[simp] lemma rotOrigin_x (φ : ℝ) (p : H2) :
    (H2.rotOrigin φ p).x = p.x * Real.cos φ - p.y * Real.sin φ := rfl
@[simp] lemma rotOrigin_y (φ : ℝ) (p : H2) :
    (H2.rotOrigin φ p).y = p.x * Real.sin φ + p.y * Real.cos φ := rfl
@[simp] lemma rotOrigin_z (φ : ℝ) (p : H2) : (H2.rotOrigin φ p).z = p.z := rfl

@[simp] lemma boostX_x (t : ℝ) (p : H2) :
    (H2.boostX t p).x = p.x * Real.cosh t + p.z * Real.sinh t := rfl
@[simp] lemma boostX_y (t : ℝ) (p : H2) : (H2.boostX t p).y = p.y := rfl
@[simp] lemma boostX_z (t : ℝ) (p : H2) :
    (H2.boostX t p).z = p.x * Real.sinh t + p.z * Real.cosh t := rfl

lemma sinh_dist (p q : H2) : Real.sinh (dist p q) = Real.sqrt (H2.lorentz p q ^ 2 - 1) :=
  H2.sinh_distH p q

/-! ### Helper lemmas for polar coordinates, `arccos (cos x)`, and `detH` -/

lemma arccos_cos_eq_abs {x : ℝ} (hlo : -Real.pi ≤ x) (hhi : x ≤ Real.pi) :
    Real.arccos (Real.cos x) = |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, Real.arccos_cos hx hhi]
  · push Not at hx
    rw [abs_of_neg hx, ← Real.cos_neg, Real.arccos_cos (by linarith) (by linarith)]

lemma arccos_cos_le_abs (x : ℝ) : Real.arccos (Real.cos x) ≤ |x| := by
  by_cases hx : |x| ≤ Real.pi
  · rw [arccos_cos_eq_abs (abs_le.mp hx).1 (abs_le.mp hx).2]
  · push Not at hx
    exact le_trans (Real.arccos_le_pi _) hx.le

lemma arccos_cos_add_int_mul_two_pi (x : ℝ) (k : ℤ) :
    Real.arccos (Real.cos (x + (k : ℝ) * (2 * Real.pi))) = Real.arccos (Real.cos x) := by
  congr 1
  exact Real.cos_add_int_mul_two_pi x k

lemma polarOrigin_add_int_mul_two_pi (ρ θ : ℝ) (k : ℤ) :
    H2.polarOrigin ρ (θ + (k : ℝ) * (2 * Real.pi)) = H2.polarOrigin ρ θ := by
  ext <;> simp [H2.polarOrigin, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma exists_polarOrigin (Q : H2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ Q = H2.polarOrigin (dist H2.origin Q) θ := by
  set ρ := dist H2.origin Q
  have hρ0 : 0 ≤ ρ := dist_nonneg
  have hqz : Q.z = Real.cosh ρ := by
    have hl : H2.lorentz H2.origin Q = Q.z := by unfold H2.lorentz H2.origin; ring
    rw [← hl, H2.cosh_dist]
  by_cases hρeq : ρ = 0
  · refine ⟨0, le_refl 0, by linarith [Real.pi_pos], ?_⟩
    have hQ : Q = H2.origin := (dist_eq_zero.mp hρeq).symm
    rw [hQ, hρeq]
    ext <;> simp [H2.origin, H2.polarOrigin]
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρeq)
    have hshpos : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρpos
    have hxy : Q.x ^ 2 + Q.y ^ 2 = Real.sinh ρ ^ 2 := by
      have hch := Real.cosh_sq_sub_sinh_sq ρ
      have hsh := Q.on_sheet
      rw [hqz] at hsh
      linarith
    set u := Q.x / Real.sinh ρ
    set v := Q.y / Real.sinh ρ
    have huv : u ^ 2 + v ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, hxy, div_self (pow_ne_zero 2 hshpos.ne')]
    have hu_le : -1 ≤ u ∧ u ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg v]
    have hsin_arccos : Real.sin (Real.arccos u) = |v| := by
      rw [Real.sin_arccos]
      have : 1 - u ^ 2 = v ^ 2 := by linarith
      rw [this, Real.sqrt_sq_eq_abs]
    by_cases hv : 0 ≤ v
    · refine ⟨Real.arccos u, Real.arccos_nonneg u, by linarith [Real.arccos_le_pi u, Real.pi_pos], ?_⟩
      ext
      · simp only [H2.polarOrigin, Real.cos_arccos hu_le.1 hu_le.2]
        dsimp only [u]; field_simp [hshpos.ne']
      · simp only [H2.polarOrigin, hsin_arccos, abs_of_nonneg hv]
        dsimp only [v]; field_simp [hshpos.ne']
      · simp only [H2.polarOrigin, hqz]
    · push Not at hv
      set θ := 2 * Real.pi - Real.arccos u
      have h_arccos_pos : 0 < Real.arccos u := by
        by_contra hle
        push Not at hle
        have h0 : Real.arccos u = 0 := le_antisymm hle (Real.arccos_nonneg u)
        have : Real.sin (Real.arccos u) = 0 := by rw [h0, Real.sin_zero]
        rw [hsin_arccos, abs_of_neg hv] at this
        linarith
      refine ⟨θ, by linarith [Real.arccos_le_pi u], by linarith, ?_⟩
      ext
      · simp only [H2.polarOrigin, θ, Real.cos_two_pi_sub, Real.cos_arccos hu_le.1 hu_le.2]
        dsimp only [u]; field_simp [hshpos.ne']
      · simp only [H2.polarOrigin, θ, Real.sin_two_pi_sub, hsin_arccos, abs_of_neg hv]
        dsimp only [v]; field_simp [hshpos.ne']
      · simp only [H2.polarOrigin, hqz]

lemma exists_polar_SiteFrame {V : Set H2} {v : H2} (F : SiteFrame V v) (P : H2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ P = F.polar (dist P v) θ := by
  obtain ⟨θ, h0, h2pi, hQ⟩ := exists_polarOrigin (F.φ.symm P)
  refine ⟨θ, h0, h2pi, ?_⟩
  have hd : dist H2.origin (F.φ.symm P) = dist P v := by
    rw [dist_comm, ← F.φ.dist_eq, F.φ.apply_symm_apply, F.origin_eq]
  rw [hd] at hQ
  unfold SiteFrame.polar
  rw [← hQ, F.φ.apply_symm_apply]

lemma dist_polar_eq {V : Set H2} {v : H2} (F : SiteFrame V v) (ρ θ : ℝ) (hρ : 0 ≤ ρ) :
    dist (F.polar ρ θ) v = ρ := by
  calc dist (F.polar ρ θ) v
      = dist (F.φ (H2.polarOrigin ρ θ)) (F.φ H2.origin) := by rw [SiteFrame.polar, F.origin_eq]
    _ = dist (H2.polarOrigin ρ θ) H2.origin := F.φ.dist_eq _ _
    _ = dist H2.origin (H2.polarOrigin ρ θ) := dist_comm _ _
    _ = ρ := dist_origin_polarOrigin ρ θ hρ

lemma SiteFrame.nbr_mod_seven {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    F.nbr k = F.nbr ((k % 7 : ℤ)) := by
  unfold SiteFrame.nbr
  congr 1
  have hdiv : (k : ℝ) = ((k % 7 : ℤ) : ℝ) + ((k / 7 : ℤ) : ℝ) * 7 := by
    exact_mod_cast (Int.emod_add_mul_ediv k 7).symm.trans (by ring)
  have hα : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
  have hθ : (k : ℝ) * α7 = ((k % 7 : ℤ) : ℝ) * α7 + ((k / 7 : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hdiv]; linear_combination ((k / 7 : ℤ) : ℝ) * hα
  rw [hθ, polarOrigin_add_int_mul_two_pi]

/-! ### Lemma 2.2: Polar Lemma -/

lemma beta7_arg_mem_Icc {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * r7) :
    (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsh2 : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hcoth : 0 < Real.cosh (2 * r7) / Real.sinh (2 * r7) := div_pos (Real.cosh_pos _) hsh2
  have ht_pos : 0 < Real.tanh (ρ / 2) := tanh_pos_of_pos (by linarith)
  have ht_le : Real.tanh (ρ / 2) ≤ Real.tanh r7 := strictMono_tanh.monotone (by linarith)
  constructor
  · linarith [mul_pos hcoth ht_pos]
  · calc (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2)
        ≤ (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh r7 :=
          mul_le_mul_of_nonneg_left ht_le hcoth.le
      _ = Real.cos α7 := text_2_beta_properties.1.trans text_2_beta_properties.2.1
      _ ≤ 1 := Real.cos_le_one _

lemma beta7_lt_pi_div_two {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * r7) :
    β7 ρ < Real.pi / 2 := by
  unfold β7 betaP
  rw [← Real.arccos_zero]
  have hsh2 : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hpos : 0 < (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) :=
    mul_pos (div_pos (Real.cosh_pos _) hsh2) (tanh_pos_of_pos (by linarith))
  exact Real.strictAntiOn_arccos ⟨by norm_num, by norm_num⟩ (beta7_arg_mem_Icc hρ0 hρ2) hpos

/-- **Lemma 2.2 (Polar Lemma)**. -/
theorem lem_2_2_polar (φ_iso : H2 ≃ᵢ H2) (ρ θ φ : ℝ)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * r7) :
    (dist (φ_iso (H2.polarOrigin ρ θ)) (φ_iso (H2.polarOrigin (2 * r7) φ)) < 2 * r7 ↔
      Real.arccos (Real.cos (θ - φ)) < β7 ρ) ∧
    (dist (φ_iso (H2.polarOrigin ρ θ)) (φ_iso (H2.polarOrigin (2 * r7) φ)) = 2 * r7 ↔
      Real.arccos (Real.cos (θ - φ)) = β7 ρ) := by
  rw [φ_iso.dist_eq]
  have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ0
  have hsh2r : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hch_half : 0 < Real.cosh (ρ / 2) := Real.cosh_pos _
  have hsh_half : 0 < Real.sinh (ρ / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have htanh_id : (Real.cosh ρ - 1) / Real.sinh ρ = Real.tanh (ρ / 2) := by
    have hρ : ρ = 2 * (ρ / 2) := by ring
    rw [Real.tanh_eq_sinh_div_cosh]
    conv_lhs => rw [hρ, cosh_two_mul', Real.sinh_two_mul]
    have hcs := Real.cosh_sq_sub_sinh_sq (ρ / 2)
    field_simp [hsh_half.ne', hch_half.ne']
    nlinarith
  have harg := beta7_arg_mem_Icc hρ0 hρ2
  have hcos_mem : Real.cos (θ - φ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hlt_lorentz :
      H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) < Real.cosh (2 * r7) ↔
      (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) < Real.cos (θ - φ) := by
    rw [lorentz_polarOrigin, ← htanh_id]
    have hmul : 0 < Real.sinh ρ * Real.sinh (2 * r7) := mul_pos hshρ hsh2r
    have h1 : (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * ((Real.cosh ρ - 1) / Real.sinh ρ) =
        (Real.cosh ρ - 1) * Real.cosh (2 * r7) / (Real.sinh ρ * Real.sinh (2 * r7)) := by ring
    rw [h1, div_lt_iff₀ hmul]
    constructor <;> intro h <;> linarith
  have heq_lorentz :
      H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) = Real.cosh (2 * r7) ↔
      (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * Real.tanh (ρ / 2) = Real.cos (θ - φ) := by
    rw [lorentz_polarOrigin, ← htanh_id]
    have hmul : 0 < Real.sinh ρ * Real.sinh (2 * r7) := mul_pos hshρ hsh2r
    have h1 : (Real.cosh (2 * r7) / Real.sinh (2 * r7)) * ((Real.cosh ρ - 1) / Real.sinh ρ) =
        (Real.cosh ρ - 1) * Real.cosh (2 * r7) / (Real.sinh ρ * Real.sinh (2 * r7)) := by ring
    rw [h1, div_eq_iff hmul.ne']
    constructor <;> intro h <;> linarith
  have h2r_eq : 2 * r7 = Real.arcosh (Real.cosh (2 * r7)) :=
    (Real.arcosh_cosh (by linarith [r7_pos])).symm
  constructor
  · have hstep : dist (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) < 2 * r7 ↔
        H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) < Real.cosh (2 * r7) := by
      rw [H2.dist_eq_arcosh]
      conv_lhs => rhs; rw [h2r_eq]
      exact Real.arcosh_lt_arcosh
        (by linarith [H2.one_le_lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ)])
        (Real.cosh_pos _)
    rw [hstep, hlt_lorentz]
    unfold β7 betaP
    exact (Real.strictAntiOn_arccos.lt_iff_gt hcos_mem harg).symm
  · have hstep : dist (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) = 2 * r7 ↔
        H2.lorentz (H2.polarOrigin ρ θ) (H2.polarOrigin (2 * r7) φ) = Real.cosh (2 * r7) := by
      rw [H2.dist_eq_arcosh]
      conv_lhs => rhs; rw [h2r_eq]
      exact Real.arcosh_injOn.eq_iff (H2.one_le_lorentz _ _) (Real.one_le_cosh _)
    rw [hstep, heq_lorentz]
    unfold β7 betaP
    exact (Real.strictAntiOn_arccos.injOn.eq_iff harg hcos_mem).symm.trans eq_comm

/-! ### Lemma 2.3: Free-Arc Lemma -/

/-- **Lemma 2.3(a) (Free-Arc Lemma, part a)**. -/
theorem lem_2_3_freearc_a (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ((∀ j : Fin 7, F.nbr j ∉ U) → False) ∧
    ((∃ j₀ : Fin 7, ∀ j : Fin 7, F.nbr j ∈ U → j = j₀) → False) ∧
    ((∃ j₁ j₂ : Fin 7, (∀ j : Fin 7, F.nbr j ∈ U → j = j₁ ∨ j = j₂) ∧
      (j₁.1 + 1) % 7 ≠ j₂.1 ∧ (j₂.1 + 1) % 7 ≠ j₁.1) → False) ∧
    (∀ k : ℕ, k = 2 ∨ k = 3 ∨ k = 4 → HasProfile V U v k F →
      ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
        β7 (dist P v) - α7 ≤ θ ∧ θ ≤ (k : ℝ) * α7 - β7 (dist P v)) := by
  set ρ := dist P v
  have hρ0 : 0 < ρ := dist_pos.mpr hPv
  have hρ2 : ρ ≤ 2 * r7 := hPr.le
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hα_lt_β : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρ0, hPr⟩
  have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hρ2
  obtain ⟨θ, hθ0, hθ2pi, hP_eq⟩ := exists_polar_SiteFrame F P
  have hnbr_in_U : ∀ j : Fin 7, Real.arccos (Real.cos (θ - (j : ℝ) * α7)) < β7 ρ → F.nbr j ∈ U := by
    intro j hlt
    by_contra hnotU
    have hmemV : F.nbr j ∈ V := F.nbr_mem j
    have hdist_ge : 2 * r7 ≤ dist P (F.nbr j) := hadm (F.nbr j) ⟨hmemV, hnotU⟩
    rw [hP_eq] at hdist_ge
    unfold SiteFrame.polar SiteFrame.nbr at hdist_ge
    have hdist_lt : dist (F.φ (H2.polarOrigin ρ θ)) (F.φ (H2.polarOrigin (2 * r7) ((j : ℝ) * α7))) < 2 * r7 :=
      (lem_2_2_polar F.φ ρ θ ((j : ℝ) * α7) hρ0 hρ2).1.mpr (by simpa using hlt)
    have hcast : ((j : ℤ) : ℝ) = (j : ℝ) := by norm_cast
    rw [hcast] at hdist_ge
    linarith
  set m_int : ℤ := ⌊θ / α7⌋
  have hm_nonneg : 0 ≤ m_int := Int.floor_nonneg.mpr (div_nonneg hθ0 hα_pos.le)
  have hm_lt7 : m_int < 7 := by
    rw [Int.floor_lt]
    have h7a : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
    rw [div_lt_iff₀ hα_pos]
    have hcast : ((7 : ℤ) : ℝ) = 7 := by norm_num
    rw [hcast]
    linarith
  set m : ℕ := m_int.toNat
  have hm_cast : (m : ℤ) = m_int := Int.toNat_of_nonneg hm_nonneg
  have hm_rcast : (m : ℝ) = (m_int : ℝ) := by exact_mod_cast hm_cast
  have hm_lt : m < 7 := by omega
  have hm_le : (m : ℝ) * α7 ≤ θ := by
    have h1 : (m_int : ℝ) ≤ θ / α7 := Int.floor_le (θ / α7)
    rw [le_div_iff₀ hα_pos] at h1
    rw [hm_rcast]; exact h1
  have hθ_lt : θ < ((m + 1 : ℕ) : ℝ) * α7 := by
    have h1 : θ / α7 < (m_int : ℝ) + 1 := Int.lt_floor_add_one (θ / α7)
    rw [div_lt_iff₀ hα_pos] at h1
    push_cast; rw [hm_rcast]; linarith
  let j₁ : Fin 7 := ⟨m, hm_lt⟩
  let j₂ : Fin 7 := ⟨(m + 1) % 7, Nat.mod_lt _ (by norm_num)⟩
  have hj1_in_U : F.nbr j₁ ∈ U := by
    apply hnbr_in_U j₁
    calc Real.arccos (Real.cos (θ - (j₁ : ℝ) * α7))
        ≤ |θ - (j₁ : ℝ) * α7| := arccos_cos_le_abs _
      _ = θ - (m : ℝ) * α7 := abs_of_nonneg (by dsimp [j₁]; linarith)
      _ < α7 := by push_cast at hθ_lt; linarith
      _ < β7 ρ := hα_lt_β
  have hj2_in_U : F.nbr j₂ ∈ U := by
    apply hnbr_in_U j₂
    have hcos_eq : Real.cos (θ - (j₂ : ℝ) * α7) = Real.cos (θ - ((m + 1 : ℕ) : ℝ) * α7) := by
      by_cases hm6 : m + 1 < 7
      · have : j₂.1 = m + 1 := Nat.mod_eq_of_lt hm6
        simp [this]
      · have hm_eq : m = 6 := by omega
        have hj2_eq : j₂.1 = 0 := by dsimp [j₂]; rw [hm_eq]
        have hj2_r : (j₂ : ℝ) = 0 := by exact_mod_cast hj2_eq
        have h7a : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
        have : θ - (j₂ : ℝ) * α7 = (θ - ((m + 1 : ℕ) : ℝ) * α7) + (1 : ℤ) * (2 * Real.pi) := by
          rw [hj2_r, hm_eq]; push_cast; linarith
        rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos_eq]
    calc Real.arccos (Real.cos (θ - ((m + 1 : ℕ) : ℝ) * α7))
        ≤ |θ - ((m + 1 : ℕ) : ℝ) * α7| := arccos_cos_le_abs _
      _ = ((m + 1 : ℕ) : ℝ) * α7 - θ := by rw [abs_of_neg (by linarith)]; ring
      _ ≤ α7 := by push_cast; linarith
      _ < β7 ρ := hα_lt_β
  have hj1_ne_j2 : j₁ ≠ j₂ := by
    intro heq
    have : m = (m + 1) % 7 := congrArg Fin.val heq
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    exact h0 j₁ hj1_in_U
  · rintro ⟨j₀, hj₀⟩
    have h1 := hj₀ j₁ hj1_in_U
    have h2 := hj₀ j₂ hj2_in_U
    exact hj1_ne_j2 (h1.trans h2.symm)
  · rintro ⟨a, b, hab, hna1, hna2⟩
    rcases hab j₁ hj1_in_U with hj1a | hj1b <;> rcases hab j₂ hj2_in_U with hj2a | hj2b
    · exact hj1_ne_j2 (hj1a.trans hj2a.symm)
    · have h1 : a.1 = m := congrArg Fin.val hj1a.symm
      have h2 : b.1 = (m + 1) % 7 := congrArg Fin.val hj2b.symm
      exact hna1 (by rw [h1, h2])
    · have h1 : b.1 = m := congrArg Fin.val hj1b.symm
      have h2 : a.1 = (m + 1) % 7 := congrArg Fin.val hj2a.symm
      exact hna2 (by rw [h1, h2])
    · exact hj1_ne_j2 (hj1b.trans hj2b.symm)
  · intro k hk hprof
    have hm_lt_k : m < k := (hprof j₁).mp hj1_in_U
    have hm1_lt_k : (m + 1) % 7 < k := (hprof j₂).mp hj2_in_U
    have hk_le4 : k ≤ 4 := by rcases hk with rfl | rfl | rfl <;> norm_num
    have hm1_lt_k' : m + 1 < k := by
      have : m + 1 < 7 := by omega
      rwa [Nat.mod_eq_of_lt this] at hm1_lt_k
    have hθ_upper_raw : θ < ((k - 1 : ℕ) : ℝ) * α7 := by
      have : ((m + 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ k - 1)
      nlinarith
    have hlo : β7 ρ - α7 ≤ θ := by
      let j6 : Fin 7 := ⟨6, by norm_num⟩
      have h6_notU : F.nbr j6 ∉ U := by
        rw [hprof j6]; dsimp [j6]; omega
      have hge : β7 ρ ≤ Real.arccos (Real.cos (θ - (j6 : ℝ) * α7)) := by
        by_contra hlt; push Not at hlt; exact h6_notU (hnbr_in_U j6 hlt)
      have hcos6 : Real.cos (θ - (j6 : ℝ) * α7) = Real.cos (θ + α7) := by
        have h7a : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
        have : θ - (j6 : ℝ) * α7 = (θ + α7) + (-1 : ℤ) * (2 * Real.pi) := by
          dsimp [j6]; norm_num; linarith
        rw [this, Real.cos_add_int_mul_two_pi]
      rw [hcos6] at hge
      by_cases hpi : θ + α7 ≤ Real.pi
      · have habs : Real.arccos (Real.cos (θ + α7)) = θ + α7 := by
          rw [arccos_cos_eq_abs (by linarith) hpi, abs_of_nonneg (by linarith)]
        linarith
      · push Not at hpi
        have : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
        linarith
    have hhi : θ ≤ (k : ℝ) * α7 - β7 ρ := by
      have hk_lt7 : k < 7 := by omega
      let jk : Fin 7 := ⟨k, hk_lt7⟩
      have hk_notU : F.nbr jk ∉ U := by
        rw [hprof jk]; dsimp [jk]; omega
      have hge : β7 ρ ≤ Real.arccos (Real.cos (θ - (jk : ℝ) * α7)) := by
        by_contra hlt; push Not at hlt; exact hk_notU (hnbr_in_U jk hlt)
      have hdiff_pos : 0 < (k : ℝ) * α7 - θ := by
        have : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
        nlinarith
      by_cases hpi : (k : ℝ) * α7 - θ ≤ Real.pi
      · have habs : Real.arccos (Real.cos (θ - (jk : ℝ) * α7)) = (k : ℝ) * α7 - θ := by
          have : (jk : ℝ) = (k : ℝ) := rfl
          rw [this, arccos_cos_eq_abs (by linarith) (by linarith), abs_of_neg (by linarith)]
          ring
        linarith
      · push Not at hpi
        linarith [Real.pi_pos]
    exact ⟨θ, hP_eq, hlo, hhi⟩

/-- **Lemma 2.3(b) (Free-Arc Lemma, part b)**. -/
theorem lem_2_3_freearc_b (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
      β7 (dist P v) - α7 ≤ θ ∧ θ ≤ 3 * α7 - β7 (dist P v) ∧
      Overlaps r7 P (F.nbr 1) ∧
      (Overlaps r7 P (F.nbr 0) ↔ θ < β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 (dist P v) < θ) ∧
      (Overlaps r7 P (F.nbr 0) ∨ Overlaps r7 P (F.nbr 2)) ∧
      ((Overlaps r7 P (F.nbr 0) ∧ ¬ Overlaps r7 P (F.nbr 2)) ∨
       (¬ Overlaps r7 P (F.nbr 0) ∧ Overlaps r7 P (F.nbr 2)) →
        β7 (dist P v) ≤ 3 * α7 / 2 ∧ ρ7 ≤ dist P v) := by
  set ρ := dist P v
  have hρ0 : 0 < ρ := dist_pos.mpr hPv
  have hρ2 : ρ ≤ 2 * r7 := hPr.le
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hα_lt_β : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρ0, hPr⟩
  have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hρ2
  have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
  have hβ_lt_2a : β7 ρ < 2 * α7 := by linarith
  obtain ⟨θ, hP_eq, hlo, hhi⟩ := (lem_2_3_freearc_a V U v F P hPv hPr hadm).2.2.2 3 (Or.inr (Or.inl rfl)) hprof
  change β7 ρ - α7 ≤ θ at hlo
  change θ ≤ ((3 : ℕ) : ℝ) * α7 - β7 ρ at hhi
  norm_num at hhi
  have hov : ∀ (j : ℤ),
      Overlaps r7 P (F.nbr j) ↔ Real.arccos (Real.cos (θ - (j : ℝ) * α7)) < β7 ρ := by
    intro j
    unfold Overlaps
    rw [hP_eq]
    exact (lem_2_2_polar F.φ ρ θ ((j : ℝ) * α7) hρ0 hρ2).1
  have hov1 : Overlaps r7 P (F.nbr 1) := by
    rw [hov 1]
    have h1 : Real.arccos (Real.cos (θ - ((1 : ℤ) : ℝ) * α7)) = |θ - α7| := by
      have : ((1 : ℤ) : ℝ) * α7 = α7 := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h1, abs_lt]
    constructor <;> linarith
  have hov0 : Overlaps r7 P (F.nbr 0) ↔ θ < β7 ρ := by
    rw [hov 0]
    have h0 : Real.arccos (Real.cos (θ - ((0 : ℤ) : ℝ) * α7)) = |θ| := by
      have : θ - ((0 : ℤ) : ℝ) * α7 = θ := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h0, abs_lt]
    exact ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
  have hov2 : Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 ρ < θ := by
    rw [hov 2]
    have h2 : Real.arccos (Real.cos (θ - ((2 : ℤ) : ℝ) * α7)) = |θ - 2 * α7| := by
      have : ((2 : ℤ) : ℝ) * α7 = 2 * α7 := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h2, abs_lt]
    exact ⟨fun h => by linarith, fun h => ⟨by linarith, by linarith⟩⟩
  have hor : Overlaps r7 P (F.nbr 0) ∨ Overlaps r7 P (F.nbr 2) := by
    rw [hov0, hov2]
    by_cases h : θ < β7 ρ
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hexcl : (Overlaps r7 P (F.nbr 0) ∧ ¬ Overlaps r7 P (F.nbr 2)) ∨
      (¬ Overlaps r7 P (F.nbr 0) ∧ Overlaps r7 P (F.nbr 2)) →
      β7 ρ ≤ 3 * α7 / 2 ∧ ρ7 ≤ ρ := by
    intro h
    rw [hov0, hov2] at h
    have hβ_le : β7 ρ ≤ 3 * α7 / 2 := by
      rcases h with ⟨_, hn2⟩ | ⟨hn0, _⟩ <;> linarith
    have hρ_ge : ρ7 ≤ ρ := by
      by_contra hlt; push Not at hlt
      have hρ7_pos : 0 < ρ7 := text_2_beta_properties.2.2.2.2.2.2.1
      have hρ7_lt : ρ7 < 2 * r7 := text_2_beta_properties.2.2.2.2.2.2.2.1
      have hβ_gt : β7 ρ7 < β7 ρ :=
        text_2_beta_properties.2.2.1 ⟨hρ0, hρ2⟩ ⟨hρ7_pos, hρ7_lt.le⟩ hlt
      rw [text_2_beta_properties.2.2.2.2.2.2.2.2] at hβ_gt
      linarith
    exact ⟨hβ_le, hρ_ge⟩
  exact ⟨θ, hP_eq, hlo, hhi, hov1, hov0, hov2, hor, hexcl⟩

/-- **Lemma 2.3(c) (Free-Arc Lemma, part c)**. -/
theorem lem_2_3_freearc_c (V U : Set H2) (v : H2) (F : SiteFrame V v)
    (hprof : HasProfile V U v 4 F)
    (P : H2) (hPv : P ≠ v) (hPr : dist P v < 2 * r7)
    (hadm : IsAdmissible r7 (V \ U) P) :
    ∃ θ : ℝ, P = F.polar (dist P v) θ ∧
      β7 (dist P v) - α7 ≤ θ ∧ θ ≤ 4 * α7 - β7 (dist P v) ∧
      (Overlaps r7 P (F.nbr 0) ↔ θ < β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 1) ↔ θ < α7 + β7 (dist P v)) ∧
      (Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 (dist P v) < θ) ∧
      (Overlaps r7 P (F.nbr 3) ↔ 3 * α7 - β7 (dist P v) < θ) ∧
      (¬ Overlaps r7 P (F.nbr 0) → ¬ Overlaps r7 P (F.nbr 3) →
        β7 (dist P v) ≤ θ ∧ θ ≤ 3 * α7 - β7 (dist P v) ∧
        Overlaps r7 P (F.nbr 1) ∧ Overlaps r7 P (F.nbr 2)) := by
  set ρ := dist P v
  have hρ0 : 0 < ρ := dist_pos.mpr hPv
  have hρ2 : ρ ≤ 2 * r7 := hPr.le
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hα_lt_β : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρ0, hPr⟩
  have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hρ2
  have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
  have hβ_lt_2a : β7 ρ < 2 * α7 := by linarith
  obtain ⟨θ, hP_eq, hlo, hhi⟩ := (lem_2_3_freearc_a V U v F P hPv hPr hadm).2.2.2 4 (Or.inr (Or.inr rfl)) hprof
  change β7 ρ - α7 ≤ θ at hlo
  change θ ≤ ((4 : ℕ) : ℝ) * α7 - β7 ρ at hhi
  norm_num at hhi
  have hov : ∀ (j : ℤ),
      Overlaps r7 P (F.nbr j) ↔ Real.arccos (Real.cos (θ - (j : ℝ) * α7)) < β7 ρ := by
    intro j
    unfold Overlaps
    rw [hP_eq]
    exact (lem_2_2_polar F.φ ρ θ ((j : ℝ) * α7) hρ0 hρ2).1
  have hov0 : Overlaps r7 P (F.nbr 0) ↔ θ < β7 ρ := by
    rw [hov 0]
    have h0 : Real.arccos (Real.cos (θ - ((0 : ℤ) : ℝ) * α7)) = |θ| := by
      have : θ - ((0 : ℤ) : ℝ) * α7 = θ := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h0, abs_lt]
    exact ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
  have hov1 : Overlaps r7 P (F.nbr 1) ↔ θ < α7 + β7 ρ := by
    rw [hov 1]
    have h1 : Real.arccos (Real.cos (θ - ((1 : ℤ) : ℝ) * α7)) = |θ - α7| := by
      have : ((1 : ℤ) : ℝ) * α7 = α7 := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h1, abs_lt]
    exact ⟨fun h => by linarith, fun h => ⟨by linarith, by linarith⟩⟩
  have hov2 : Overlaps r7 P (F.nbr 2) ↔ 2 * α7 - β7 ρ < θ := by
    rw [hov 2]
    have h2 : Real.arccos (Real.cos (θ - ((2 : ℤ) : ℝ) * α7)) = |θ - 2 * α7| := by
      have : ((2 : ℤ) : ℝ) * α7 = 2 * α7 := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h2, abs_lt]
    exact ⟨fun h => by linarith, fun h => ⟨by linarith, by linarith⟩⟩
  have hov3 : Overlaps r7 P (F.nbr 3) ↔ 3 * α7 - β7 ρ < θ := by
    rw [hov 3]
    have h3 : Real.arccos (Real.cos (θ - ((3 : ℤ) : ℝ) * α7)) = |θ - 3 * α7| := by
      have : ((3 : ℤ) : ℝ) * α7 = 3 * α7 := by norm_num
      rw [this]
      exact arccos_cos_eq_abs (by linarith) (by linarith)
    rw [h3, abs_lt]
    exact ⟨fun h => by linarith, fun h => ⟨by linarith, by linarith⟩⟩
  refine ⟨θ, hP_eq, hlo, hhi, hov0, hov1, hov2, hov3, ?_⟩
  intro hn0 hn3
  rw [hov0] at hn0; push Not at hn0
  rw [hov3] at hn3; push Not at hn3
  refine ⟨hn0, hn3, ?_, ?_⟩
  · rw [hov1]; linarith
  · rw [hov2]; linarith

/-- **Lemma 2.3(d) (Free-Arc Lemma, part d)**. -/
theorem lem_2_3_freearc_d (v w : H2) (hadj : Adj37 v w) :
    ¬ Overlaps r7 v w := by
  unfold Overlaps Adj37 at *
  linarith

/-- **Lemma 2.3(d) consequence**. -/
theorem lem_2_3_freearc_d_conseq (X : Finset H2) (hpack : IsPacking r7 (X : Set H2)) (q : H2)
    (h2 : ∃ P₁ ∈ X, ∃ P₂ ∈ X, P₁ ≠ P₂ ∧ Overlaps r7 P₁ q ∧ Overlaps r7 P₂ q) :
    q ∉ X := by
  intro hqX
  rcases h2 with ⟨P₁, hP₁, P₂, hP₂, hne, hov1, hov2⟩
  by_cases h1 : P₁ = q
  · subst h1
    have hge := hpack P₂ hP₂ P₁ hqX hne.symm
    unfold Overlaps at hov2
    linarith
  · have hge := hpack P₁ hP₁ q hqX h1
    unfold Overlaps at hov1
    linarith

/-! ### Isometry action on `detH` and normalization of equilateral triangles -/

lemma detH_reflXAxis (p q r : H2) :
    H2.detH (H2.reflXAxis p) (H2.reflXAxis q) (H2.reflXAxis r) = -H2.detH p q r := by
  unfold H2.detH; simp only [reflXAxis_x, reflXAxis_y, reflXAxis_z]; ring

lemma detH_rotOrigin (φ : ℝ) (p q r : H2) :
    H2.detH (H2.rotOrigin φ p) (H2.rotOrigin φ q) (H2.rotOrigin φ r) = H2.detH p q r := by
  unfold H2.detH; simp only [rotOrigin_x, rotOrigin_y, rotOrigin_z]
  have hcs := Real.cos_sq_add_sin_sq φ
  linear_combination (p.x * (q.y * r.z - q.z * r.y) - p.y * (q.x * r.z - q.z * r.x) +
    p.z * (q.x * r.y - q.y * r.x)) * hcs

lemma detH_boostX (t : ℝ) (p q r : H2) :
    H2.detH (H2.boostX t p) (H2.boostX t q) (H2.boostX t r) = H2.detH p q r := by
  unfold H2.detH; simp only [boostX_x, boostX_y, boostX_z]
  have hch := Real.cosh_sq_sub_sinh_sq t
  linear_combination (p.x * (q.y * r.z - q.z * r.y) - p.y * (q.x * r.z - q.z * r.x) +
    p.z * (q.x * r.y - q.y * r.x)) * hch

/-- Normalize any pair of adjacent sites `(v, v')` to `(origin, polarOrigin (2 * r7) 0)`
    using orientation-preserving isometries (so `detH` is preserved identically!). -/
lemma exists_iso_pair_preserves_detH (v v' : H2) (hvv' : Adj37 v v') :
    ∃ g : H2 ≃ᵢ H2,
      g v = H2.origin ∧
      g v' = H2.polarOrigin (2 * r7) 0 ∧
      ∀ a b c : H2, H2.detH (g a) (g b) (g c) = H2.detH a b c := by
  obtain ⟨θv, _, _, hv_eq⟩ := exists_polarOrigin v
  set ρv := dist H2.origin v
  let g1 : H2 ≃ᵢ H2 := (H2.rotOrigin (-θv)).trans (H2.boostX (-ρv))
  have hg1_apply : ∀ p : H2, g1 p = H2.boostX (-ρv) (H2.rotOrigin (-θv) p) := fun _ => rfl
  have hg1_v : g1 v = H2.origin := by
    rw [hg1_apply, hv_eq]
    have hcs := Real.cos_sq_add_sin_sq θv
    have hch := Real.cosh_sq_sub_sinh_sq ρv
    ext
    · simp only [boostX_x, rotOrigin_x, rotOrigin_z, H2.polarOrigin, H2.origin,
        Real.cos_neg, Real.sin_neg, Real.cosh_neg, Real.sinh_neg]
      linear_combination Real.sinh ρv * Real.cosh ρv * hcs
    · simp only [boostX_y, rotOrigin_y, H2.polarOrigin, H2.origin, Real.cos_neg, Real.sin_neg]
      ring
    · simp only [boostX_z, rotOrigin_x, rotOrigin_z, H2.polarOrigin, H2.origin,
        Real.cos_neg, Real.sin_neg, Real.cosh_neg, Real.sinh_neg]
      linear_combination -(Real.sinh ρv ^ 2) * hcs + hch
  have hg1_det : ∀ a b c : H2, H2.detH (g1 a) (g1 b) (g1 c) = H2.detH a b c := by
    intro a b c
    rw [hg1_apply, hg1_apply, hg1_apply, detH_boostX, detH_rotOrigin]
  obtain ⟨θ', _, _, hv'_eq⟩ := exists_polarOrigin (g1 v')
  have hdv' : dist H2.origin (g1 v') = 2 * r7 := by
    rw [← hg1_v, g1.dist_eq]; exact hvv'
  rw [hdv'] at hv'_eq
  let g : H2 ≃ᵢ H2 := g1.trans (H2.rotOrigin (-θ'))
  have hg_apply : ∀ p : H2, g p = H2.rotOrigin (-θ') (g1 p) := fun _ => rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hg_apply, hg1_v]
    ext <;> simp [H2.origin]
  · rw [hg_apply, hv'_eq]
    have hcs := Real.cos_sq_add_sin_sq θ'
    ext
    · simp only [rotOrigin_x, H2.polarOrigin, Real.cos_neg, Real.sin_neg, Real.cos_zero, mul_one]
      linear_combination Real.sinh (2 * r7) * hcs
    · simp only [rotOrigin_y, H2.polarOrigin, Real.cos_neg, Real.sin_neg, Real.sin_zero, mul_zero]
      ring
    · simp only [rotOrigin_z, H2.polarOrigin]
  · intro a b c
    rw [hg_apply, hg_apply, hg_apply, detH_rotOrigin, hg1_det]

lemma detH_origin_xAxis (Q : H2) :
    H2.detH H2.origin (H2.polarOrigin (2 * r7) 0) Q = Real.sinh (2 * r7) * Q.y := by
  unfold H2.detH H2.origin H2.polarOrigin
  simp [Real.cos_zero, Real.sin_zero]

/-! ### Conical combination lemmas for the Edge Lemma and Reuleaux Lemma -/

/-- If `x ∈ H2` is a nonnegative combination `a • u + b • v` in `ℝ³` (`a, b ≥ 0`), then
    `dist u x + dist x v = dist u v`. -/
lemma dist_add_of_conical_two {u v x : H2} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x.x = a * u.x + b * v.x) (hy : x.y = a * u.y + b * v.y) (hz : x.z = a * u.z + b * v.z) :
    dist u x + dist x v = dist u v := by
  have hux : H2.lorentz u x = a + b * H2.lorentz u v := by
    unfold H2.lorentz; rw [hx, hy, hz]; nlinarith [u.on_sheet]
  have hxv : H2.lorentz x v = a * H2.lorentz u v + b := by
    unfold H2.lorentz; rw [hx, hy, hz]; nlinarith [v.on_sheet]
  have hxx : a ^ 2 + 2 * a * b * H2.lorentz u v + b ^ 2 = 1 := by
    have h1 := x.on_sheet
    rw [hx, hy, hz] at h1
    unfold H2.lorentz
    nlinarith [u.on_sheet, v.on_sheet]
  have hdet : H2.detH u x v = 0 := by
    unfold H2.detH; rw [hx, hy, hz]; ring
  have hgram := H2.gram_det_identity u x v
  rw [hdet] at hgram
  have hc_ge : 1 ≤ H2.lorentz u v := H2.one_le_lorentz u v
  have hdiff_nonneg : 0 ≤ H2.lorentz u v - H2.lorentz u x * H2.lorentz x v := by
    rw [hux, hxv]
    have h1 : H2.lorentz u v - (a + b * H2.lorentz u v) * (a * H2.lorentz u v + b) =
        a * b * (H2.lorentz u v ^ 2 - 1) := by
      nlinarith [hxx]
    rw [h1]
    have : 0 ≤ H2.lorentz u v ^ 2 - 1 := by nlinarith
    positivity
  have hux_sq : 0 ≤ H2.lorentz u x ^ 2 - 1 := by nlinarith [H2.one_le_lorentz u x]
  have hxv_sq : 0 ≤ H2.lorentz x v ^ 2 - 1 := by nlinarith [H2.one_le_lorentz x v]
  have hsqrt_eq : H2.lorentz u v - H2.lorentz u x * H2.lorentz x v =
      Real.sqrt (H2.lorentz u x ^ 2 - 1) * Real.sqrt (H2.lorentz x v ^ 2 - 1) := by
    have hsq : (H2.lorentz u v - H2.lorentz u x * H2.lorentz x v) ^ 2 =
        (Real.sqrt (H2.lorentz u x ^ 2 - 1) * Real.sqrt (H2.lorentz x v ^ 2 - 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hux_sq, Real.sq_sqrt hxv_sq]
      linarith
    have hrhs_nonneg : 0 ≤ Real.sqrt (H2.lorentz u x ^ 2 - 1) * Real.sqrt (H2.lorentz x v ^ 2 - 1) := by
      positivity
    nlinarith [(sq_eq_sq₀ hdiff_nonneg hrhs_nonneg).mp hsq]
  have hcosh_eq : Real.cosh (dist u x + dist x v) = Real.cosh (dist u v) := by
    rw [Real.cosh_add, H2.cosh_dist, H2.cosh_dist, H2.cosh_dist, sinh_dist, sinh_dist]
    linarith [hsqrt_eq]
  have h0 : 0 ≤ dist u x + dist x v := add_nonneg dist_nonneg dist_nonneg
  have h1 : 0 ≤ dist u v := dist_nonneg
  rw [← Real.arcosh_cosh h0, ← Real.arcosh_cosh h1, hcosh_eq]

/-- **Lemma 2.4 (Edge Lemma)**. -/
theorem lem_2_4_edge (v v' o : H2)
    (hvv' : Adj37 v v') (hvo : Adj37 v o) (hv'o : Adj37 v' o) :
    (∀ P : H2, Overlaps r7 P v → Overlaps r7 P v' → 2 * r7 ≤ dist P o →
      H2.detH v v' P * H2.detH v v' o < 0) ∧
    (∀ P P' : H2, Overlaps r7 P v → Overlaps r7 P v' →
      Overlaps r7 P' v → Overlaps r7 P' v' →
      0 < H2.detH v v' P * H2.detH v v' P' → dist P P' < 2 * r7) := by
  obtain ⟨g, hgv, hgv', hgdet⟩ := exists_iso_pair_preserves_detH v v' hvv'
  have hsh2r : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  constructor
  · -- Part (i)
    intro P hPv hPv' hPo
    rw [← hgdet v v' P, ← hgdet v v' o, hgv, hgv', detH_origin_xAxis, detH_origin_xAxis]
    obtain ⟨θo, hθo0, hθo2pi, hgo_eq⟩ := exists_polarOrigin (g o)
    have hdo_orig : dist H2.origin (g o) = 2 * r7 := by
      rw [← hgv, g.dist_eq]; exact hvo
    rw [hdo_orig] at hgo_eq
    have hdo_v' : dist (g o) (H2.polarOrigin (2 * r7) 0) = 2 * r7 := by
      rw [← hgv', g.dist_eq, dist_comm]; exact hv'o
    rw [hgo_eq] at hdo_v'
    have harccos_o : Real.arccos (Real.cos θo) = α7 := by
      have hpol := (lem_2_2_polar (IsometryEquiv.refl H2) (2 * r7) θo 0
        (by linarith [r7_pos]) (le_refl _)).2.mp hdo_v'
      simpa [text_2_beta_properties.2.2.2.2.1] using hpol
    have hPne : P ≠ v := by
      rintro rfl; unfold Overlaps Adj37 at *; linarith
    have hρP_pos : 0 < dist H2.origin (g P) := by
      rw [← hgv, g.dist_eq, dist_comm]; exact dist_pos.mpr hPne
    have hρP_lt : dist H2.origin (g P) < 2 * r7 := by
      rw [← hgv, g.dist_eq, dist_comm]; exact hPv
    set ρ := dist H2.origin (g P)
    obtain ⟨θP_raw, _, _, hgP_raw⟩ := exists_polarOrigin (g P)
    set kP : ℤ := ⌈(θP_raw - Real.pi) / (2 * Real.pi)⌉
    set θP := θP_raw - (kP : ℝ) * (2 * Real.pi)
    have hθP_lo : -Real.pi < θP := by
      have h1 : (kP : ℝ) < (θP_raw - Real.pi) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
      have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
      have h2 : (kP : ℝ) * (2 * Real.pi) < θP_raw - Real.pi + 2 * Real.pi := by
        have := mul_lt_mul_of_pos_right h1 h2pi
        rw [add_mul, div_mul_cancel₀ _ h2pi.ne', one_mul] at this
        exact this
      linarith
    have hθP_hi : θP ≤ Real.pi := by
      have h1 : (θP_raw - Real.pi) / (2 * Real.pi) ≤ (kP : ℝ) := Int.le_ceil _
      have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
      have h2 : θP_raw - Real.pi ≤ (kP : ℝ) * (2 * Real.pi) := (div_le_iff₀ h2pi).mp h1
      linarith
    have hgP_eq : g P = H2.polarOrigin ρ θP := by
      rw [hgP_raw]
      have : θP_raw = θP + (kP : ℝ) * (2 * Real.pi) := by ring
      rw [this, polarOrigin_add_int_mul_two_pi]
    have hβ_gt_a : α7 < β7 ρ := text_2_beta_properties.2.2.2.2.2.1 ρ ⟨hρP_pos, hρP_lt⟩
    have hβ_lt_pi2 : β7 ρ < Real.pi / 2 := beta7_lt_pi_div_two hρP_pos hρP_lt.le
    have hPv'_g : dist (H2.polarOrigin ρ θP) (H2.polarOrigin (2 * r7) 0) < 2 * r7 := by
      rw [← hgP_eq, ← hgv', g.dist_eq]; exact hPv'
    have hθP_abs : |θP| < β7 ρ := by
      have h1 := (lem_2_2_polar (IsometryEquiv.refl H2) ρ θP 0 hρP_pos hρP_lt.le).1.mp hPv'_g
      simpa [arccos_cos_eq_abs hθP_lo.le hθP_hi] using h1
    have hPo_g : 2 * r7 ≤ dist (H2.polarOrigin ρ θP) (H2.polarOrigin (2 * r7) θo) := by
      rw [← hgP_eq, ← hgo_eq, g.dist_eq]; exact hPo
    have hθP_o_ge : β7 ρ ≤ Real.arccos (Real.cos (θP - θo)) := by
      by_contra hlt; push Not at hlt
      have h1 := (lem_2_2_polar (IsometryEquiv.refl H2) ρ θP θo hρP_pos hρP_lt.le).1.mpr hlt
      change dist (H2.polarOrigin ρ θP) (H2.polarOrigin (2 * r7) θo) < 2 * r7 at h1
      linarith
    have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
    have hα_lt_pi : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
    have hθo_cases : θo = α7 ∨ θo = 2 * Real.pi - α7 := by
      by_cases hle : θo ≤ Real.pi
      · left
        rw [Real.arccos_cos hθo0 hle] at harccos_o; exact harccos_o
      · right
        push Not at hle
        have : Real.cos θo = Real.cos (2 * Real.pi - θo) := by rw [Real.cos_two_pi_sub]
        rw [this, Real.arccos_cos (by linarith) (by linarith)] at harccos_o
        linarith
    have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρP_pos
    have hsin_a : 0 < Real.sin α7 := Real.sin_pos_of_pos_of_lt_pi hα_pos hα_lt_pi
    rcases hθo_cases with rfl | rfl
    · have hθP_neg : θP < 0 := by
        by_contra hge; push Not at hge
        have h1 : |θP - α7| < β7 ρ := by rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hθP_abs).2]
        have h2 : Real.arccos (Real.cos (θP - α7)) ≤ |θP - α7| := arccos_cos_le_abs _
        linarith
      have hsinP : Real.sin θP < 0 := by
        have h1 : Real.sin (-θP) > 0 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [(abs_lt.mp hθP_abs).1])
        rw [Real.sin_neg] at h1; linarith
      rw [hgP_eq, hgo_eq]
      simp only [H2.polarOrigin]
      have h1 : Real.sinh (2 * r7) * (Real.sinh ρ * Real.sin θP) < 0 := by nlinarith [mul_pos hsh2r hshρ]
      have h2 : 0 < Real.sinh (2 * r7) * (Real.sinh (2 * r7) * Real.sin α7) := by positivity
      nlinarith
    · have hθP_pos : 0 < θP := by
        by_contra hle; push Not at hle
        have hcos_eq : Real.cos (θP - (2 * Real.pi - α7)) = Real.cos (θP + α7) := by
          have : θP - (2 * Real.pi - α7) = (θP + α7) + (-1 : ℤ) * (2 * Real.pi) := by ring
          rw [this, Real.cos_add_int_mul_two_pi]
        rw [hcos_eq] at hθP_o_ge
        have h1 : |θP + α7| < β7 ρ := by rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hθP_abs).1]
        have h2 : Real.arccos (Real.cos (θP + α7)) ≤ |θP + α7| := arccos_cos_le_abs _
        linarith
      have hsinP : 0 < Real.sin θP :=
        Real.sin_pos_of_pos_of_lt_pi hθP_pos (by linarith [(abs_lt.mp hθP_abs).2])
      rw [hgP_eq, hgo_eq]
      simp only [H2.polarOrigin, Real.sin_two_pi_sub]
      have h1 : 0 < Real.sinh (2 * r7) * (Real.sinh ρ * Real.sin θP) := by positivity
      have h2 : Real.sinh (2 * r7) * (Real.sinh (2 * r7) * -Real.sin α7) < 0 := by
        nlinarith [mul_pos hsh2r hsh2r]
      nlinarith
  · -- Part (ii)
    intro P P' hPv hPv' hP'v hP'v' hsame
    have hsame_g : 0 < (g P).y * (g P').y := by
      rw [← hgdet v v' P, ← hgdet v v' P', hgv, hgv', detH_origin_xAxis, detH_origin_xAxis] at hsame
      have : 0 < Real.sinh (2 * r7) ^ 2 := sq_pos_of_pos hsh2r
      nlinarith
    have hcore : ∀ A B : H2,
        H2.lorentz A H2.origin < Real.cosh (2 * r7) →
        H2.lorentz A (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) →
        H2.lorentz B H2.origin < Real.cosh (2 * r7) →
        H2.lorentz B (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) →
        0 < A.y → 0 < B.y → A.x * B.y ≤ A.y * B.x →
        dist A B < 2 * r7 := by
      intro A B hAo hAw hBo hBw hAy hBy hcross
      set O := H2.origin
      set W := H2.polarOrigin (2 * r7) 0
      have hWx : W.x = Real.sinh (2 * r7) := by simp [W, H2.polarOrigin]
      have hWy : W.y = 0 := by simp [W, H2.polarOrigin]
      have hWz : W.z = Real.cosh (2 * r7) := by simp [W, H2.polarOrigin]
      set c3 : ℝ := B.y / A.y
      set c2 : ℝ := (B.x - c3 * A.x) / W.x
      set c1 : ℝ := B.z - c2 * W.z - c3 * A.z
      have hc3 : 0 < c3 := div_pos hBy hAy
      have hc2 : 0 ≤ c2 := by
        dsimp only [c2]; rw [hWx]
        apply div_nonneg _ hsh2r.le
        have hnum : B.x - c3 * A.x = (B.x * A.y - B.y * A.x) / A.y := by
          dsimp only [c3]; field_simp [hAy.ne']
        rw [hnum]
        exact div_nonneg (by linarith) hAy.le
      have hBx : B.x = c1 * O.x + c2 * W.x + c3 * A.x := by
        simp only [O, H2.origin, c2, hWx]
        field_simp [hsh2r.ne']; ring
      have hBy_eq : B.y = c1 * O.y + c2 * W.y + c3 * A.y := by
        simp only [O, H2.origin, hWy, c3]
        field_simp [hAy.ne']; ring
      have hBz : B.z = c1 * O.z + c2 * W.z + c3 * A.z := by
        simp only [O, H2.origin, c1]; ring
      by_cases hc1 : 0 ≤ c1
      · have hsum_le : c1 + c2 + c3 ≤ 1 := by
          have h1 : H2.lorentz B B = c1 * H2.lorentz B O + c2 * H2.lorentz B W + c3 * H2.lorentz B A := by
            unfold H2.lorentz; rw [hBx, hBy_eq, hBz]; ring
          rw [H2.lorentz_self] at h1
          have hBO := H2.one_le_lorentz B O
          have hBW := H2.one_le_lorentz B W
          have hBA := H2.one_le_lorentz B A
          nlinarith
        have hlAB : H2.lorentz A B < Real.cosh (2 * r7) := by
          have h1 : H2.lorentz A B = c1 * H2.lorentz A O + c2 * H2.lorentz A W + c3 * H2.lorentz A A := by
            unfold H2.lorentz; rw [hBx, hBy_eq, hBz]; ring
          rw [H2.lorentz_self] at h1
          have hc2r_gt1 : 1 < Real.cosh (2 * r7) := Real.one_lt_cosh.mpr (by linarith [r7_pos])
          nlinarith
        rw [H2.dist_eq_arcosh, ← Real.arcosh_cosh (by linarith [r7_pos] : 0 ≤ 2 * r7)]
        exact (Real.arcosh_lt_arcosh (by linarith [H2.one_le_lorentz A B]) (Real.cosh_pos _)).mpr hlAB
      · push Not at hc1
        set s1 : ℝ := -c1
        have hs1 : 0 < s1 := by linarith
        let wx : ℝ := s1 * O.x + B.x
        let wy : ℝ := s1 * O.y + B.y
        let wz : ℝ := s1 * O.z + B.z
        have hnorm_sq : wz ^ 2 - wx ^ 2 - wy ^ 2 = s1 ^ 2 + 2 * s1 * H2.lorentz O B + 1 := by
          change (s1 * O.z + B.z) ^ 2 - (s1 * O.x + B.x) ^ 2 - (s1 * O.y + B.y) ^ 2 = _
          unfold H2.lorentz
          have hO := O.on_sheet
          have hB := B.on_sheet
          linear_combination s1 ^ 2 * hO + hB
        have hnorm_pos : 0 < wz ^ 2 - wx ^ 2 - wy ^ 2 := by
          rw [hnorm_sq]
          have hOB := H2.one_le_lorentz O B
          have h1 : 0 < 2 * s1 * H2.lorentz O B := by positivity
          have h2 : 0 ≤ s1 ^ 2 := sq_nonneg s1
          linarith
        let N : ℝ := Real.sqrt (wz ^ 2 - wx ^ 2 - wy ^ 2)
        have hN_pos : 0 < N := Real.sqrt_pos.mpr hnorm_pos
        have hwz_pos : 0 < wz := add_pos (mul_pos hs1 O.hz) B.hz
        let X : H2 :=
          { x := wx / N
            y := wy / N
            z := wz / N
            hz := div_pos hwz_pos hN_pos
            on_sheet := by
              rw [div_pow, div_pow, div_pow, ← sub_div, ← sub_div]
              change (wz ^ 2 - wx ^ 2 - wy ^ 2) / Real.sqrt (wz ^ 2 - wx ^ 2 - wy ^ 2) ^ 2 = 1
              rw [Real.sq_sqrt hnorm_pos.le, div_self hnorm_pos.ne'] }
        have hX_OB : dist O X + dist X B = dist O B :=
          dist_add_of_conical_two (div_nonneg hs1.le hN_pos.le) (div_nonneg zero_le_one hN_pos.le)
            (by change wx / N = s1 / N * O.x + 1 / N * B.x; dsimp only [wx]; ring)
            (by change wy / N = s1 / N * O.y + 1 / N * B.y; dsimp only [wy]; ring)
            (by change wz / N = s1 / N * O.z + 1 / N * B.z; dsimp only [wz]; ring)
        have hX_WA : dist W X + dist X A = dist W A :=
          dist_add_of_conical_two (div_nonneg hc2 hN_pos.le) (div_nonneg hc3.le hN_pos.le)
            (by change (s1 * O.x + B.x) / N = c2 / N * W.x + c3 / N * A.x; rw [hBx]; dsimp only [s1]; ring)
            (by change (s1 * O.y + B.y) / N = c2 / N * W.y + c3 / N * A.y; rw [hBy_eq]; dsimp only [s1]; ring)
            (by change (s1 * O.z + B.z) / N = c2 / N * W.z + c3 / N * A.z; rw [hBz]; dsimp only [s1]; ring)
        have hd_OW : dist O W = 2 * r7 := dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])
        have hd_OB : dist O B < 2 * r7 := by
          rw [H2.dist_eq_arcosh, ← Real.arcosh_cosh (by linarith [r7_pos] : 0 ≤ 2 * r7)]
          rw [Real.arcosh_lt_arcosh (by linarith [H2.one_le_lorentz O B]) (Real.cosh_pos _), H2.lorentz_symm]
          exact hBo
        have hd_WA : dist W A < 2 * r7 := by
          rw [H2.dist_eq_arcosh, ← Real.arcosh_cosh (by linarith [r7_pos] : 0 ≤ 2 * r7)]
          rw [Real.arcosh_lt_arcosh (by linarith [H2.one_le_lorentz W A]) (Real.cosh_pos _), H2.lorentz_symm]
          exact hAw
        have htri1 : dist O W ≤ dist O X + dist X W := dist_triangle O X W
        have htri2 : dist A B ≤ dist A X + dist X B := dist_triangle A X B
        rw [dist_comm X W] at htri1
        rw [dist_comm A X] at htri2
        linarith
    have hlt_l : ∀ X Y : H2, Overlaps r7 X Y → H2.lorentz (g X) (g Y) < Real.cosh (2 * r7) := by
      intro X Y hXY
      rw [← H2.cosh_dist, g.dist_eq]
      have : dist X Y < 2 * r7 := hXY
      rw [← Real.arcosh_lt_arcosh (Real.cosh_pos _) (Real.cosh_pos _),
          Real.arcosh_cosh dist_nonneg, Real.arcosh_cosh (by linarith [r7_pos])]
      exact this
    have hPo' : H2.lorentz (g P) H2.origin < Real.cosh (2 * r7) := by rw [← hgv]; exact hlt_l P v hPv
    have hPw' : H2.lorentz (g P) (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) := by
      rw [← hgv']; exact hlt_l P v' hPv'
    have hP'o' : H2.lorentz (g P') H2.origin < Real.cosh (2 * r7) := by rw [← hgv]; exact hlt_l P' v hP'v
    have hP'w' : H2.lorentz (g P') (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) := by
      rw [← hgv']; exact hlt_l P' v' hP'v'
    rw [← g.dist_eq]
    by_cases hPy : 0 < (g P).y
    · have hP'y : 0 < (g P').y := by nlinarith
      by_cases hcr : (g P).x * (g P').y ≤ (g P).y * (g P').x
      · exact hcore (g P) (g P') hPo' hPw' hP'o' hP'w' hPy hP'y hcr
      · rw [dist_comm]
        exact hcore (g P') (g P) hP'o' hP'w' hPo' hPw' hP'y hPy (by linarith)
    · have hPy_neg : (g P).y < 0 := by
        by_contra hge; push Not at hge
        have : (g P).y = 0 := le_antisymm (le_of_not_gt hPy) hge
        rw [this, zero_mul] at hsame_g; exact lt_irrefl 0 hsame_g
      have hP'y_neg : (g P').y < 0 := by nlinarith
      let A := H2.reflXAxis (g P)
      let B := H2.reflXAxis (g P')
      have hO_fix : H2.reflXAxis H2.origin = H2.origin := by ext <;> simp [H2.origin]
      have hW_fix : H2.reflXAxis (H2.polarOrigin (2 * r7) 0) = H2.polarOrigin (2 * r7) 0 := by
        ext <;> simp [H2.polarOrigin]
      have hl_refl : ∀ X Y : H2, H2.lorentz (H2.reflXAxis X) (H2.reflXAxis Y) = H2.lorentz X Y := by
        intro X Y; unfold H2.lorentz; simp only [reflXAxis_x, reflXAxis_y, reflXAxis_z]; ring
      have hAo : H2.lorentz A H2.origin < Real.cosh (2 * r7) := by rw [← hO_fix, hl_refl]; exact hPo'
      have hAw : H2.lorentz A (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) := by
        rw [← hW_fix, hl_refl]; exact hPw'
      have hBo : H2.lorentz B H2.origin < Real.cosh (2 * r7) := by rw [← hO_fix, hl_refl]; exact hP'o'
      have hBw : H2.lorentz B (H2.polarOrigin (2 * r7) 0) < Real.cosh (2 * r7) := by
        rw [← hW_fix, hl_refl]; exact hP'w'
      have hAy : 0 < A.y := by dsimp [A]; linarith
      have hBy : 0 < B.y := by dsimp [B]; linarith
      rw [← H2.reflXAxis.dist_eq]
      by_cases hcr : A.x * B.y ≤ A.y * B.x
      · exact hcore A B hAo hAw hBo hBw hAy hBy hcr
      · rw [dist_comm]
        exact hcore B A hBo hBw hAo hAw hBy hAy (by linarith)

/-! ### Lemma 2.5: Reuleaux-Triangle Lemma -/

/-- **Lemma 2.5 (Reuleaux-Triangle Lemma)**. -/
theorem lem_2_5_reuleaux (u v w P Q : H2)
    (huv : Adj37 u v) (hvw : Adj37 v w) (hwu : Adj37 w u)
    (hPu : Overlaps r7 P u) (hPv : Overlaps r7 P v) (hPw : Overlaps r7 P w)
    (hQu : Overlaps r7 Q u) (hQv : Overlaps r7 Q v) (hQw : Overlaps r7 Q w) :
    dist P Q < 2 * r7 := by
  have hD_ne : H2.detH u v w ≠ 0 := by
    have hgram := H2.gram_det_identity u v w
    have huv_l : H2.lorentz u v = Real.cosh (2 * r7) := by rw [← H2.cosh_dist]; exact congrArg Real.cosh huv
    have hvw_l : H2.lorentz v w = Real.cosh (2 * r7) := by rw [← H2.cosh_dist]; exact congrArg Real.cosh hvw
    have huw_l : H2.lorentz u w = Real.cosh (2 * r7) := by
      rw [← H2.cosh_dist, dist_comm]; exact congrArg Real.cosh hwu
    rw [huv_l, hvw_l, huw_l] at hgram
    set c2 := Real.cosh (2 * r7)
    have hc2_gt1 : 1 < c2 := Real.one_lt_cosh.mpr (by linarith [r7_pos])
    have hpos : 0 < (c2 ^ 2 - 1) * (c2 ^ 2 - 1) - (c2 - c2 * c2) ^ 2 := by
      have : (c2 ^ 2 - 1) * (c2 ^ 2 - 1) - (c2 - c2 * c2) ^ 2 = (c2 - 1) ^ 2 * (2 * c2 + 1) := by ring
      rw [this]; positivity
    intro h0
    rw [h0] at hgram
    nlinarith
  have hnot_two_nonpos : ∀ a b c X : H2,
      Adj37 a b → Adj37 b c → Adj37 c a →
      Overlaps r7 X a → Overlaps r7 X b → Overlaps r7 X c →
      H2.detH a b c ≠ 0 →
      ¬ (H2.detH a X c / H2.detH a b c ≤ 0 ∧ H2.detH a b X / H2.detH a b c ≤ 0) := by
    intro a b c X hab hbc hca hXa hXb hXc hD ⟨hb_le, hc_le⟩
    set D := H2.detH a b c
    set α := H2.detH X b c / D
    set β := H2.detH a X c / D
    set γ := H2.detH a b X / D
    have hXx_mul : X.x * D = H2.detH X b c * a.x + H2.detH a X c * b.x + H2.detH a b X * c.x := by
      dsimp only [D]; unfold H2.detH; ring
    have hXy_mul : X.y * D = H2.detH X b c * a.y + H2.detH a X c * b.y + H2.detH a b X * c.y := by
      dsimp only [D]; unfold H2.detH; ring
    have hXz_mul : X.z * D = H2.detH X b c * a.z + H2.detH a X c * b.z + H2.detH a b X * c.z := by
      dsimp only [D]; unfold H2.detH; ring
    have hXx : X.x = α * a.x + β * b.x + γ * c.x := by
      dsimp only [α, β, γ]
      have : (H2.detH X b c * a.x + H2.detH a X c * b.x + H2.detH a b X * c.x) / D =
          H2.detH X b c / D * a.x + H2.detH a X c / D * b.x + H2.detH a b X / D * c.x := by ring
      rw [← this, ← hXx_mul, mul_div_cancel_right₀ _ hD]
    have hXy : X.y = α * a.y + β * b.y + γ * c.y := by
      dsimp only [α, β, γ]
      have : (H2.detH X b c * a.y + H2.detH a X c * b.y + H2.detH a b X * c.y) / D =
          H2.detH X b c / D * a.y + H2.detH a X c / D * b.y + H2.detH a b X / D * c.y := by ring
      rw [← this, ← hXy_mul, mul_div_cancel_right₀ _ hD]
    have hXz : X.z = α * a.z + β * b.z + γ * c.z := by
      dsimp only [α, β, γ]
      have : (H2.detH X b c * a.z + H2.detH a X c * b.z + H2.detH a b X * c.z) / D =
          H2.detH X b c / D * a.z + H2.detH a X c / D * b.z + H2.detH a b X / D * c.z := by ring
      rw [← this, ← hXz_mul, mul_div_cancel_right₀ _ hD]
    set c2 := Real.cosh (2 * r7)
    have hc2_gt1 : 1 < c2 := Real.one_lt_cosh.mpr (by linarith [r7_pos])
    have hlab : H2.lorentz a b = c2 := by rw [← H2.cosh_dist]; exact congrArg Real.cosh hab
    have hlbc : H2.lorentz b c = c2 := by rw [← H2.cosh_dist]; exact congrArg Real.cosh hbc
    have hlac : H2.lorentz a c = c2 := by
      rw [← H2.cosh_dist, dist_comm]; exact congrArg Real.cosh hca
    have hlXa : H2.lorentz X a = α + β * c2 + γ * c2 := by
      have h1 : H2.lorentz X a = α * H2.lorentz a a + β * H2.lorentz b a + γ * H2.lorentz c a := by
        unfold H2.lorentz; rw [hXx, hXy, hXz]; ring
      rw [h1, H2.lorentz_self, H2.lorentz_symm b a, H2.lorentz_symm c a, hlab, hlac]; ring
    have hlXb : H2.lorentz X b = α * c2 + β + γ * c2 := by
      have h1 : H2.lorentz X b = α * H2.lorentz a b + β * H2.lorentz b b + γ * H2.lorentz c b := by
        unfold H2.lorentz; rw [hXx, hXy, hXz]; ring
      rw [h1, H2.lorentz_self, hlab, H2.lorentz_symm c b, hlbc]; ring
    have hlXb_lt : H2.lorentz X b < c2 := by
      rw [← H2.cosh_dist]
      have : dist X b < 2 * r7 := hXb
      rw [← Real.arcosh_lt_arcosh (Real.cosh_pos _) (Real.cosh_pos _),
          Real.arcosh_cosh dist_nonneg, Real.arcosh_cosh (by linarith [r7_pos])]
      exact this
    have hlXa_ge : 1 ≤ H2.lorentz X a := H2.one_le_lorentz X a
    have hcomb : H2.lorentz X b = c2 * H2.lorentz X a + (-β) * (c2 ^ 2 - 1) + (-γ) * (c2 ^ 2 - c2) := by
      rw [hlXa, hlXb]; ring
    have h1 : 0 ≤ (-β) * (c2 ^ 2 - 1) := mul_nonneg (by linarith) (by nlinarith)
    have h2 : 0 ≤ (-γ) * (c2 ^ 2 - c2) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have hdet_cyc1 : H2.detH v w u = H2.detH u v w := by unfold H2.detH; ring
  have hdet_cyc2 : H2.detH w u v = H2.detH u v w := by unfold H2.detH; ring
  have hEdge_uv := (lem_2_4_edge u v w huv (by unfold Adj37 at *; rwa [dist_comm]) hvw).2
  have hEdge_vw := (lem_2_4_edge v w u hvw (by unfold Adj37 at *; rwa [dist_comm]) hwu).2
  have hEdge_wu := (lem_2_4_edge w u v hwu (by unfold Adj37 at *; rwa [dist_comm]) huv).2
  set D := H2.detH u v w
  have hD_sq : 0 < D ^ 2 := sq_pos_of_ne_zero hD_ne
  set aP := H2.detH P v w / D
  set bP := H2.detH u P w / D
  set cP := H2.detH u v P / D
  set aQ := H2.detH Q v w / D
  set bQ := H2.detH u Q w / D
  set cQ := H2.detH u v Q / D
  have hP_bc : ¬ (bP ≤ 0 ∧ cP ≤ 0) :=
    hnot_two_nonpos u v w P huv hvw hwu hPu hPv hPw hD_ne
  have hP_ca : ¬ (cP ≤ 0 ∧ aP ≤ 0) := by
    have h := hnot_two_nonpos v w u P hvw hwu huv hPv hPw hPu (by rwa [hdet_cyc1])
    have h1 : H2.detH v P u = H2.detH u v P := by unfold H2.detH; ring
    have h2 : H2.detH v w P = H2.detH P v w := by unfold H2.detH; ring
    simpa [aP, cP, D, hdet_cyc1, h1, h2] using h
  have hP_ab : ¬ (aP ≤ 0 ∧ bP ≤ 0) := by
    have h := hnot_two_nonpos w u v P hwu huv hvw hPw hPu hPv (by rwa [hdet_cyc2])
    have h1 : H2.detH w P v = H2.detH P v w := by unfold H2.detH; ring
    have h2 : H2.detH w u P = H2.detH u P w := by unfold H2.detH; ring
    simpa [aP, bP, D, hdet_cyc2, h1, h2] using h
  have hQ_bc : ¬ (bQ ≤ 0 ∧ cQ ≤ 0) :=
    hnot_two_nonpos u v w Q huv hvw hwu hQu hQv hQw hD_ne
  have hQ_ca : ¬ (cQ ≤ 0 ∧ aQ ≤ 0) := by
    have h := hnot_two_nonpos v w u Q hvw hwu huv hQv hQw hQu (by rwa [hdet_cyc1])
    have h1 : H2.detH v Q u = H2.detH u v Q := by unfold H2.detH; ring
    have h2 : H2.detH v w Q = H2.detH Q v w := by unfold H2.detH; ring
    simpa [aQ, cQ, D, hdet_cyc1, h1, h2] using h
  have hQ_ab : ¬ (aQ ≤ 0 ∧ bQ ≤ 0) := by
    have h := hnot_two_nonpos w u v Q hwu huv hvw hQw hQu hQv (by rwa [hdet_cyc2])
    have h1 : H2.detH w Q v = H2.detH Q v w := by unfold H2.detH; ring
    have h2 : H2.detH w u Q = H2.detH u Q w := by unfold H2.detH; ring
    simpa [aQ, bQ, D, hdet_cyc2, h1, h2] using h
  by_cases hc : 0 < cP ∧ 0 < cQ
  · apply hEdge_uv P Q hPu hPv hQu hQv
    have hmul : 0 < cP * cQ := mul_pos hc.1 hc.2
    have heq : cP * cQ = H2.detH u v P * H2.detH u v Q / D ^ 2 := by dsimp [cP, cQ]; ring
    rw [heq, div_pos_iff_of_pos_right hD_sq] at hmul
    exact hmul
  · by_cases ha : 0 < aP ∧ 0 < aQ
    · apply hEdge_vw P Q hPv hPw hQv hQw
      have hmul : 0 < aP * aQ := mul_pos ha.1 ha.2
      have h1 : H2.detH v w P = H2.detH P v w := by unfold H2.detH; ring
      have h2 : H2.detH v w Q = H2.detH Q v w := by unfold H2.detH; ring
      have heq : aP * aQ = H2.detH v w P * H2.detH v w Q / D ^ 2 := by dsimp [aP, aQ]; rw [h1, h2]; ring
      rw [heq, div_pos_iff_of_pos_right hD_sq] at hmul
      exact hmul
    · have hb : 0 < bP ∧ 0 < bQ := by
        constructor <;> by_contra hle <;> push Not at hle
        · have hcP : 0 < cP := by by_contra h; push Not at h; exact hP_bc ⟨hle, h⟩
          have haP : 0 < aP := by by_contra h; push Not at h; exact hP_ab ⟨h, hle⟩
          have hcQ : cQ ≤ 0 := by by_contra h; push Not at h; exact hc ⟨hcP, h⟩
          have haQ : aQ ≤ 0 := by by_contra h; push Not at h; exact ha ⟨haP, h⟩
          exact hQ_ca ⟨hcQ, haQ⟩
        · have hcQ : 0 < cQ := by by_contra h; push Not at h; exact hQ_bc ⟨hle, h⟩
          have haQ : 0 < aQ := by by_contra h; push Not at h; exact hQ_ab ⟨h, hle⟩
          have hcP : cP ≤ 0 := by by_contra h; push Not at h; exact hc ⟨h, hcQ⟩
          have haP : aP ≤ 0 := by by_contra h; push Not at h; exact ha ⟨h, haQ⟩
          exact hP_ca ⟨hcP, haP⟩
      apply hEdge_wu P Q hPw hPu hQw hQu
      have hmul : 0 < bP * bQ := mul_pos hb.1 hb.2
      have h1 : H2.detH w u P = H2.detH u P w := by unfold H2.detH; ring
      have h2 : H2.detH w u Q = H2.detH u Q w := by unfold H2.detH; ring
      have heq : bP * bQ = H2.detH w u P * H2.detH w u Q / D ^ 2 := by dsimp [bP, bQ]; rw [h1, h2]; ring
      rw [heq, div_pos_iff_of_pos_right hD_sq] at hmul
      exact hmul

end FejesTothP7.Proofs
