/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.TipGeom

/-!
# Good Sets and Joining Lemmas (Section 4)

All results here are hypothesis-parametrized on the global tiling properties of `sites37`
(`IsPacking r7 sites37`, existence of `SiteFrame sites37 v`, covering radius `Rc7`, and
Lemma 2.1 triviality characterization), so they compile independently of the `{3, 7}`
construction and instantiate directly in `Paper/Statements.lean`.

We prove:
- `lem_4_1_bridge` (Bridge and Deletion Remarks, parts a–c)
- `rem_4_2_tau3_edge_count` (`τ₃` Edge-Count)
- `lem_4_3_join_le_two` (Joining with at most two unfixed neighbors)
- `lem_4_4_join_tau3` (Profile-`τ₃` joining lemma)
- `lem_4_5_nine_site` (Nine-site closing lemma, with Steps 1–5)
-/

noncomputable section

open Classical

namespace FejesTothP7.Proofs

/-! ### Basic helpers on `H2.mid`, `SiteFrame` alignment, and `FixedSites`/`UnfixedSites` -/

lemma mid_comm (p q : H2) : H2.mid p q = H2.mid q p := by
  ext <;> simp only [H2.mid, add_comm, H2.lorentz_symm]

lemma fixedSites_eq_diff_unfixed (c₀ : H2) (s : Finset H2) :
    FixedSites c₀ s = sites37 \ UnfixedSites c₀ s := by
  ext x
  simp only [FixedSites, oneVacancy, UnfixedSites, Set.mem_sdiff, Set.mem_singleton_iff,
    Set.mem_union, Finset.mem_coe]
  tauto

lemma isAdmissible_of_mem_rearrangement (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X) {P : H2} (hP : P ∈ X) :
    IsAdmissible r7 (sites37 \ UnfixedSites c₀ s) P := by
  rw [← fixedSites_eq_diff_unfixed]
  intro f hf
  have hP_in : P ∈ (oneVacancy c₀ \ (s : Set H2)) ∪ (X : Set H2) := Or.inr hP
  have hf_in : f ∈ (oneVacancy c₀ \ (s : Set H2)) ∪ (X : Set H2) := Or.inl hf
  have hne : P ≠ f := by
    intro heq
    subst heq
    exact Set.disjoint_left.mp hX.2.2.1 hf hP
  exact hX.2.2.2 P hP_in f hf_in hne

end FejesTothP7.Proofs

namespace FejesTothP7

open FejesTothP7.Proofs

lemma SiteFrame.nbr_mod_seven {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    F.nbr k = F.nbr ((k % 7 : ℤ)) :=
  FejesTothP7.Proofs.SiteFrame.nbr_mod_seven F k

/-- Distance between consecutive neighbors `F.nbr k` and `F.nbr (k + 1)` is `2 * r7`. -/
lemma SiteFrame.adj_nbr_consec {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    Adj37 (F.nbr k) (F.nbr (k + 1)) := by
  unfold Adj37 SiteFrame.nbr
  rw [F.φ.dist_eq]
  have hpol := (lem_2_2_polar (IsometryEquiv.refl H2) (2 * r7) ((k : ℝ) * α7) (((k + 1 : ℤ) : ℝ) * α7)
    (by linarith [r7_pos]) (le_refl _)).2
  apply hpol.mpr
  have hsub : (k : ℝ) * α7 - ((k + 1 : ℤ) : ℝ) * α7 = -α7 := by push_cast; ring
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hα_lt : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
  rw [hsub, arccos_cos_eq_abs (by linarith) (by linarith), abs_of_neg (by linarith),
      neg_neg, text_2_beta_properties.2.2.2.2.1]

/-- Distance from `v` to any neighbor `F.nbr k` is `2 * r7`. -/
lemma SiteFrame.adj_self_nbr {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    Adj37 v (F.nbr k) := by
  unfold Adj37
  calc dist v (F.nbr k)
      = dist (F.φ H2.origin) (F.φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))) := by
        rw [F.origin_eq, SiteFrame.nbr]
    _ = dist H2.origin (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) := F.φ.dist_eq _ _
    _ = 2 * r7 := dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])

/-- Any neighbor `F.nbr k` (`k : ℤ`) belongs to `V`. -/
lemma SiteFrame.nbr_mem_int {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    F.nbr k ∈ V := by
  rw [F.nbr_mod_seven]
  have h0 : 0 ≤ k % 7 := Int.emod_nonneg k (by norm_num)
  have h7 : k % 7 < 7 := Int.emod_lt_of_pos k (by norm_num)
  let j : Fin 7 := ⟨(k % 7).toNat, by omega⟩
  have hj : (j : ℤ) = k % 7 := Int.toNat_of_nonneg h0
  rw [← hj]
  have hcast : ((j : ℤ) : ℝ) = (j : ℝ) := by norm_cast
  unfold SiteFrame.nbr
  rw [hcast]
  exact F.nbr_mem j

/-- Two neighbors `F.nbr i`, `F.nbr j` (`i, j : Fin 7`) are equal iff `i = j`. -/
lemma SiteFrame.nbr_injective {V : Set H2} {v : H2} (F : SiteFrame V v) {i j : Fin 7}
    (h : F.nbr i = F.nbr j) : i = j := by
  unfold SiteFrame.nbr at h
  have h1 := F.φ.injective h
  have hcos : Real.cos (((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7) = 1 := by
    have hl : H2.lorentz (H2.polarOrigin (2 * r7) (((i : ℤ) : ℝ) * α7))
        (H2.polarOrigin (2 * r7) (((j : ℤ) : ℝ) * α7)) = 1 := by
      rw [h1, H2.lorentz_self]
    rw [lorentz_polarOrigin] at hl
    have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
    have hsh_pos : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    nlinarith [sq_pos_of_pos hsh_pos]
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have h7a : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
  have hdiff_ne : i ≠ j → False := by
    intro hne
    have hval : i.1 ≠ j.1 := fun he => hne (Fin.ext he)
    have hcases : (1 : ℝ) ≤ |(i.1 : ℝ) - (j.1 : ℝ)| ∧ |(i.1 : ℝ) - (j.1 : ℝ)| ≤ 6 := by
      have hi := i.2; have hj := j.2
      by_cases hlt : i.1 < j.1
      · have h1 : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast (by omega : i.1 + 1 ≤ j.1)
        have h6 : (j.1 : ℝ) ≤ (i.1 : ℝ) + 6 := by exact_mod_cast (by omega : j.1 ≤ i.1 + 6)
        rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
      · have hgt : j.1 < i.1 := by omega
        have h1 : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast (by omega : j.1 + 1 ≤ i.1)
        have h6 : (i.1 : ℝ) ≤ (j.1 : ℝ) + 6 := by exact_mod_cast (by omega : i.1 ≤ j.1 + 6)
        rw [abs_of_nonneg (by linarith)]; exact ⟨by linarith, by linarith⟩
    set d := |((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7|
    have hd_eq : d = |(i.1 : ℝ) - (j.1 : ℝ)| * α7 := by
      dsimp [d]
      have : ((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7 = ((i.1 : ℝ) - (j.1 : ℝ)) * α7 := by
        push_cast; ring
      rw [this, abs_mul, abs_of_pos hα_pos]
    have hd_lo : α7 ≤ d := by rw [hd_eq]; nlinarith [hcases.1]
    have hd_hi : d ≤ 6 * α7 := by rw [hd_eq]; nlinarith [hcases.2]
    have hcos_d : Real.cos d = 1 := by
      dsimp [d]
      by_cases hs : 0 ≤ ((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7
      · rwa [abs_of_nonneg hs]
      · rw [abs_of_neg (lt_of_not_ge hs), Real.cos_neg]; exact hcos
    by_cases hpi : d ≤ Real.pi
    · have : Real.cos d < Real.cos 0 :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hpi (by linarith)
      rw [Real.cos_zero] at this; linarith
    · push Not at hpi
      have : Real.cos (2 * Real.pi - d) < Real.cos 0 :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) (by linarith)
      rw [Real.cos_two_pi_sub, Real.cos_zero] at this; linarith
  by_contra hne
  exact hdiff_ne hne

/-- Two neighbors `F.nbr i` and `F.nbr j` (`i, j : Fin 7`) are adjacent iff they are cyclically consecutive. -/
lemma SiteFrame.adj_nbr_iff {V : Set H2} {v : H2} (F : SiteFrame V v) (i j : Fin 7) :
    Adj37 (F.nbr i) (F.nbr j) ↔ (i.1 + 1) % 7 = j.1 ∨ (j.1 + 1) % 7 = i.1 := by
  constructor
  · intro hadj
    unfold Adj37 SiteFrame.nbr at hadj
    have hpol := (lem_2_2_polar F.φ (2 * r7) (((i : ℤ) : ℝ) * α7) (((j : ℤ) : ℝ) * α7)
      (by linarith [r7_pos]) (le_refl _)).2.mp hadj
    rw [text_2_beta_properties.2.2.2.2.1] at hpol
    have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
    have h7a : (7 : ℝ) * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
    have hcos_eq : Real.cos (((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7) = Real.cos α7 := by
      have h1 := congrArg Real.cos hpol
      rwa [Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)] at h1
    by_contra hnot
    push Not at hnot
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, Real.cos_zero] at hcos_eq
      have : Real.cos α7 < Real.cos 0 :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) hα_pos
      rw [Real.cos_zero] at this; linarith
    · have hi := i.2; have hj := j.2
      have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      have hdist_nat : (2 : ℝ) ≤ |(i.1 : ℝ) - (j.1 : ℝ)| ∧ |(i.1 : ℝ) - (j.1 : ℝ)| ≤ 5 := by
        have h1 : i.1 + 1 ≠ j.1 ∧ j.1 + 1 ≠ i.1 ∧ ¬ (i.1 = 6 ∧ j.1 = 0) ∧ ¬ (j.1 = 6 ∧ i.1 = 0) := by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> (try rcases h with ⟨h1, h2⟩) <;> omega
        by_cases hlt : i.1 < j.1
        · have ha : (i.1 : ℝ) + 2 ≤ (j.1 : ℝ) := by exact_mod_cast (by omega : i.1 + 2 ≤ j.1)
          have hb : (j.1 : ℝ) ≤ (i.1 : ℝ) + 5 := by exact_mod_cast (by omega : j.1 ≤ i.1 + 5)
          rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
        · have ha : (j.1 : ℝ) + 2 ≤ (i.1 : ℝ) := by exact_mod_cast (by omega : j.1 + 2 ≤ i.1)
          have hb : (i.1 : ℝ) ≤ (j.1 : ℝ) + 5 := by exact_mod_cast (by omega : i.1 ≤ j.1 + 5)
          rw [abs_of_nonneg (by linarith)]; exact ⟨by linarith, by linarith⟩
      set d := |((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7|
      have hd_eq : d = |(i.1 : ℝ) - (j.1 : ℝ)| * α7 := by
        dsimp [d]
        have : ((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7 = ((i.1 : ℝ) - (j.1 : ℝ)) * α7 := by push_cast; ring
        rw [this, abs_mul, abs_of_pos hα_pos]
      have hd_lo : 2 * α7 ≤ d := by rw [hd_eq]; nlinarith [hdist_nat.1]
      have hd_hi : d ≤ 5 * α7 := by rw [hd_eq]; nlinarith [hdist_nat.2]
      have hcos_d : Real.cos d = Real.cos α7 := by
        dsimp [d]
        by_cases hs : 0 ≤ ((i : ℤ) : ℝ) * α7 - ((j : ℤ) : ℝ) * α7
        · rwa [abs_of_nonneg hs]
        · rw [abs_of_neg (lt_of_not_ge hs), Real.cos_neg]; exact hcos_eq
      by_cases hpi : d ≤ Real.pi
      · have : Real.cos d < Real.cos α7 :=
          Real.cos_lt_cos_of_nonneg_of_le_pi hα_pos.le hpi (by linarith)
        linarith
      · push Not at hpi
        have : Real.cos (2 * Real.pi - d) < Real.cos α7 :=
          Real.cos_lt_cos_of_nonneg_of_le_pi hα_pos.le (by linarith) (by linarith)
        rw [Real.cos_two_pi_sub] at this; linarith
  · rintro (h | h)
    · have : F.nbr j = F.nbr ((i : ℤ) + 1) := by
        rw [F.nbr_mod_seven ((i : ℤ) + 1), F.nbr_mod_seven (j : ℤ)]
        congr 1; omega
      rw [this]; exact F.adj_nbr_consec i
    · have : F.nbr i = F.nbr ((j : ℤ) + 1) := by
        rw [F.nbr_mod_seven ((j : ℤ) + 1), F.nbr_mod_seven (i : ℤ)]
        congr 1; omega
      rw [this]; unfold Adj37; rw [dist_comm]; exact F.adj_nbr_consec j

/-- Rotate a `SiteFrame` by `s : ℤ` steps (so `F'.nbr k = F.nbr (k + s)`). -/
def SiteFrame.rotate {V : Set H2} {v : H2} (F : SiteFrame V v) (s : ℤ) : SiteFrame V v where
  φ := (H2.rotOrigin ((s : ℝ) * α7)).trans F.φ
  origin_eq := by
    change F.φ (H2.rotOrigin _ H2.origin) = v
    have : H2.rotOrigin ((s : ℝ) * α7) H2.origin = H2.origin := by ext <;> simp [H2.origin]
    rw [this, F.origin_eq]
  nbr_mem := by
    intro k
    change F.φ (H2.rotOrigin ((s : ℝ) * α7) (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))) ∈ V
    have hrot : H2.rotOrigin ((s : ℝ) * α7) (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) =
        H2.polarOrigin (2 * r7) ((((k : ℤ) + s : ℤ) : ℝ) * α7) := by
      have harg : (((k : ℤ) + s : ℤ) : ℝ) * α7 = (k : ℝ) * α7 + (s : ℝ) * α7 := by push_cast; ring
      rw [harg]
      ext <;> simp [H2.polarOrigin, Real.cos_add, Real.sin_add] <;> ring
    rw [hrot]
    exact F.nbr_mem_int ((k : ℤ) + s)
  nbr_iff := by
    intro w hw
    rw [F.nbr_iff w hw]
    have hrot : ∀ (r a b : ℝ), H2.rotOrigin b (H2.polarOrigin r a) = H2.polarOrigin r (a + b) := by
      intro r a b
      ext <;> simp [H2.polarOrigin, Real.cos_add, Real.sin_add] <;> ring
    constructor
    · rintro ⟨k, rfl⟩
      let j : Fin 7 := ⟨(((k : ℤ) - s) % 7).toNat, by omega⟩
      refine ⟨j, ?_⟩
      change F.φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) =
        F.φ (H2.rotOrigin ((s : ℝ) * α7) (H2.polarOrigin (2 * r7) ((j : ℝ) * α7)))
      rw [hrot]
      have hcast : ((j : ℝ) * α7 + (s : ℝ) * α7) = (((j : ℤ) + s : ℤ) : ℝ) * α7 := by push_cast; ring
      rw [hcast]
      change F.nbr k = F.nbr ((j : ℤ) + s)
      rw [F.nbr_mod_seven k, F.nbr_mod_seven ((j : ℤ) + s)]
      congr 1
      have hj_eq : (j : ℤ) = ((k : ℤ) - s) % 7 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [hj_eq]
      omega
    · rintro ⟨j, rfl⟩
      change ∃ k : Fin 7, F.φ (H2.rotOrigin ((s : ℝ) * α7) (H2.polarOrigin (2 * r7) ((j : ℝ) * α7))) =
        F.φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))
      rw [hrot]
      let k : Fin 7 := ⟨(((j : ℤ) + s) % 7).toNat, by omega⟩
      refine ⟨k, ?_⟩
      have hcast : ((j : ℝ) * α7 + (s : ℝ) * α7) = (((j : ℤ) + s : ℤ) : ℝ) * α7 := by push_cast; ring
      rw [hcast]
      change F.nbr ((j : ℤ) + s) = F.nbr k
      rw [F.nbr_mod_seven ((j : ℤ) + s), F.nbr_mod_seven k]
      congr 1
      have hk_eq : (k : ℤ) = ((j : ℤ) + s) % 7 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [hk_eq]
      omega

lemma SiteFrame.rotate_nbr {V : Set H2} {v : H2} (F : SiteFrame V v) (s k : ℤ) :
    (F.rotate s).nbr k = F.nbr (k + s) := by
  unfold SiteFrame.rotate SiteFrame.nbr
  change F.φ (H2.rotOrigin ((s : ℝ) * α7) (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))) = _
  congr 1
  have harg : (((k + s : ℤ) : ℝ) * α7) = (k : ℝ) * α7 + (s : ℝ) * α7 := by push_cast; ring
  rw [harg]
  ext <;> simp [H2.polarOrigin, Real.cos_add, Real.sin_add] <;> ring

/-- Reflect a `SiteFrame` across ray `θ = 0` (so `F'.nbr k = F.nbr (-k)`). -/
def SiteFrame.reflect {V : Set H2} {v : H2} (F : SiteFrame V v) : SiteFrame V v where
  φ := H2.reflXAxis.trans F.φ
  origin_eq := by
    change F.φ (H2.reflXAxis H2.origin) = v
    have : H2.reflXAxis H2.origin = H2.origin := by ext <;> simp [H2.origin]
    rw [this, F.origin_eq]
  nbr_mem := by
    intro k
    change F.φ (H2.reflXAxis (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))) ∈ V
    have href : H2.reflXAxis (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) =
        H2.polarOrigin (2 * r7) (((-(k : ℤ) : ℤ) : ℝ) * α7) := by
      have harg : ((-(k : ℤ) : ℤ) : ℝ) * α7 = -((k : ℝ) * α7) := by push_cast; ring
      rw [harg]
      ext <;> simp [H2.polarOrigin, Real.cos_neg, Real.sin_neg]
    rw [href]
    exact F.nbr_mem_int (-(k : ℤ))
  nbr_iff := by
    intro w hw
    rw [F.nbr_iff w hw]
    have href : ∀ (r a : ℝ), H2.reflXAxis (H2.polarOrigin r a) = H2.polarOrigin r (-a) := by
      intro r a
      ext <;> simp [H2.polarOrigin, Real.cos_neg, Real.sin_neg]
    constructor
    · rintro ⟨k, rfl⟩
      let j : Fin 7 := ⟨((-(k : ℤ)) % 7).toNat, by omega⟩
      refine ⟨j, ?_⟩
      change F.φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7)) =
        F.φ (H2.reflXAxis (H2.polarOrigin (2 * r7) ((j : ℝ) * α7)))
      rw [href]
      have hcast : -((j : ℝ) * α7) = (((-(j : ℤ) : ℤ) : ℝ) * α7) := by push_cast; ring
      rw [hcast]
      change F.nbr k = F.nbr (-(j : ℤ))
      rw [F.nbr_mod_seven k, F.nbr_mod_seven (-(j : ℤ))]
      congr 1
      have hj_eq : (j : ℤ) = (-(k : ℤ)) % 7 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [hj_eq]; omega
    · rintro ⟨j, rfl⟩
      change ∃ k : Fin 7, F.φ (H2.reflXAxis (H2.polarOrigin (2 * r7) ((j : ℝ) * α7))) =
        F.φ (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))
      rw [href]
      let k : Fin 7 := ⟨((-(j : ℤ)) % 7).toNat, by omega⟩
      refine ⟨k, ?_⟩
      have hcast : -((j : ℝ) * α7) = (((-(j : ℤ) : ℤ) : ℝ) * α7) := by push_cast; ring
      rw [hcast]
      change F.nbr (-(j : ℤ)) = F.nbr k
      rw [F.nbr_mod_seven (-(j : ℤ)), F.nbr_mod_seven k]
      congr 1
      have hk_eq : (k : ℤ) = (-(j : ℤ)) % 7 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [hk_eq]; omega

lemma SiteFrame.reflect_nbr {V : Set H2} {v : H2} (F : SiteFrame V v) (k : ℤ) :
    F.reflect.nbr k = F.nbr (-k) := by
  unfold SiteFrame.reflect SiteFrame.nbr
  change F.φ (H2.reflXAxis (H2.polarOrigin (2 * r7) ((k : ℝ) * α7))) = _
  congr 1
  have harg : ((-k : ℤ) : ℝ) * α7 = -((k : ℝ) * α7) := by push_cast; ring
  rw [harg]
  ext <;> simp [H2.polarOrigin, Real.cos_neg, Real.sin_neg]

/-- Align any `SiteFrame V v` to send `0 ↦ a` and `1 ↦ b` for any adjacent neighbors `a, b ∈ V` of `v`. -/
lemma SiteFrame.align {V : Set H2} {v a b : H2} (F : SiteFrame V v)
    (ha : a ∈ V) (hb : b ∈ V) (hva : Adj37 v a) (hvb : Adj37 v b) (hab : Adj37 a b) :
    ∃ F' : SiteFrame V v, F'.nbr 0 = a ∧ F'.nbr 1 = b := by
  obtain ⟨ja, hja⟩ := (F.nbr_iff a ha).mp hva
  obtain ⟨jb, hjb⟩ := (F.nbr_iff b hb).mp hvb
  have hja' : F.nbr ja = a := by simpa [SiteFrame.nbr] using hja.symm
  have hjb' : F.nbr jb = b := by simpa [SiteFrame.nbr] using hjb.symm
  rw [← hja', ← hjb'] at hab
  rcases (F.adj_nbr_iff ja jb).mp hab with h1 | h2
  · refine ⟨F.rotate ja, ?_, ?_⟩
    · rw [F.rotate_nbr, zero_add]; exact hja'
    · rw [F.rotate_nbr, F.nbr_mod_seven, ← hjb', F.nbr_mod_seven]
      congr 1; omega
  · refine ⟨(F.rotate ja).reflect, ?_, ?_⟩
    · rw [SiteFrame.reflect_nbr, F.rotate_nbr, neg_zero, zero_add]; exact hja'
    · rw [SiteFrame.reflect_nbr, F.rotate_nbr, F.nbr_mod_seven, ← hjb', F.nbr_mod_seven]
      congr 1; omega

/-- Given `F : SiteFrame V v` and a site `d ∈ V` adjacent to both `v` and `F.nbr k` with `d ≠ F.nbr (k - 1)`,
    we must have `d = F.nbr (k + 1)`. -/
lemma SiteFrame.nbr_next_of_common_nbr {V : Set H2} {v d : H2} (F : SiteFrame V v) (k : Fin 7)
    (hd : d ∈ V) (hvd : Adj37 v d) (hkd : Adj37 (F.nbr k) d) (hne : d ≠ F.nbr ((k : ℤ) - 1)) :
    d = F.nbr ((k : ℤ) + 1) := by
  obtain ⟨jd, hjd⟩ := (F.nbr_iff d hd).mp hvd
  have hjd' : F.nbr jd = d := by simpa [SiteFrame.nbr] using hjd.symm
  rw [← hjd'] at hkd hne ⊢
  rcases (F.adj_nbr_iff k jd).mp hkd with h1 | h2
  · rw [F.nbr_mod_seven jd, F.nbr_mod_seven ((k : ℤ) + 1)]
    congr 1; omega
  · exfalso; apply hne
    rw [F.nbr_mod_seven jd, F.nbr_mod_seven ((k : ℤ) - 1)]
    congr 1; omega

/-- Symmetric version: adjacent to `v` and `F.nbr k` with `d ≠ F.nbr (k + 1)` forces `d = F.nbr (k - 1)`. -/
lemma SiteFrame.nbr_prev_of_common_nbr {V : Set H2} {v d : H2} (F : SiteFrame V v) (k : Fin 7)
    (hd : d ∈ V) (hvd : Adj37 v d) (hkd : Adj37 (F.nbr k) d) (hne : d ≠ F.nbr ((k : ℤ) + 1)) :
    d = F.nbr ((k : ℤ) - 1) := by
  obtain ⟨jd, hjd⟩ := (F.nbr_iff d hd).mp hvd
  have hjd' : F.nbr jd = d := by simpa [SiteFrame.nbr] using hjd.symm
  rw [← hjd'] at hkd hne ⊢
  rcases (F.adj_nbr_iff k jd).mp hkd with h1 | h2
  · exfalso; apply hne
    rw [F.nbr_mod_seven jd, F.nbr_mod_seven ((k : ℤ) + 1)]
    congr 1; omega
  · rw [F.nbr_mod_seven jd, F.nbr_mod_seven ((k : ℤ) - 1)]
    congr 1; omega

end FejesTothP7

namespace FejesTothP7.Proofs

/-! ### Lemma 4.1: Bridge and Deletion Remarks -/

/-- **Lemma 4.1 (Bridge and Deletion Remarks)**, hypothesis-parametrized on global tiling properties. -/
theorem lem_4_1_bridge (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37)) :
    (∀ s' X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s' X →
      ¬ IsTrivialRearrangement (oneVacancy c₀) s' X →
      2 ≤ (X.filter (fun p => p ∉ sites37)).card) ∧
    (∀ c ∈ oneVacancy c₀, IsGood c₀ {c}) ∧
    (∀ s : Finset H2, ∀ c : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p c)).card) ∧
    (∀ s s' : Finset H2, IsGood c₀ s → s' ⊆ s → IsGood c₀ s') ∧
    (∀ s : Finset H2, ∀ c q : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c → IsQualifying c₀ s c q →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p q)).card ∧ q ∉ X) := by
  -- Part (a1)
  have ha1 : ∀ s' X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s' X →
      ¬ IsTrivialRearrangement (oneVacancy c₀) s' X →
      2 ≤ (X.filter (fun p => p ∉ sites37)).card := by
    intro s' X hX hnt
    by_contra hlt; push Not at hlt
    set Off := X.filter (fun p => p ∉ sites37)
    have hOff_ne0 : Off.card ≠ 0 := by
      intro h0
      have hsub : (X : Set H2) ⊆ sites37 := by
        intro p hp
        by_contra hnot
        have : p ∈ Off := Finset.mem_filter.mpr ⟨hp, hnot⟩
        rw [Finset.card_eq_zero.mp h0] at this
        exact Finset.notMem_empty p this
      exact hnt ((hTriv s' X hX).mpr hsub)
    have hOff_eq1 : Off.card = 1 := by omega
    obtain ⟨Y, hY_eq⟩ := Finset.card_eq_one.mp hOff_eq1
    have hY_mem : Y ∈ Off := by rw [hY_eq]; exact Finset.mem_singleton_self Y
    have hY_X : Y ∈ X := (Finset.mem_filter.mp hY_mem).1
    have hY_notS : Y ∉ sites37 := (Finset.mem_filter.mp hY_mem).2
    -- All other elements of X belong to sites37 and are disjoint from oneVacancy c₀ \ s',
    -- so X.erase Y ⊆ insert c₀ s'.
    set X_in := X.erase Y
    have hX_in_sub : X_in ⊆ insert c₀ s' := by
      intro p hp
      have hpX : p ∈ X := Finset.mem_of_mem_erase hp
      have hpne : p ≠ Y := Finset.ne_of_mem_erase hp
      have hpS : p ∈ sites37 := by
        by_contra hnot
        have : p ∈ Off := Finset.mem_filter.mpr ⟨hpX, hnot⟩
        rw [hY_eq, Finset.mem_singleton] at this
        exact hpne this
      by_cases hpc0 : p = c₀
      · subst hpc0; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        by_contra hnot_s'
        have : p ∈ oneVacancy c₀ \ (s' : Set H2) := ⟨⟨hpS, hpc0⟩, hnot_s'⟩
        exact Set.disjoint_left.mp hX.2.2.1 this hpX
    set E := (insert c₀ s') \ X_in
    have hc0_not_s' : c₀ ∉ s' := fun h => (hX.1 h).2 rfl
    have hE_card : E.card = 2 := by
      have h1 : E.card = (insert c₀ s').card - X_in.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hX_in_sub]
      have h2 : (insert c₀ s').card = s'.card + 1 := Finset.card_insert_of_notMem hc0_not_s'
      have h3 : X_in.card = X.card - 1 := Finset.card_erase_of_mem hY_X
      have h4 : 1 ≤ X.card := Finset.card_pos.mpr ⟨Y, hY_X⟩
      have h5 : X.card = s'.card := hX.2.1
      omega
    -- Covering radius gives F ∈ sites37 with dist Y F ≤ Rc7 < 2 * r7
    obtain ⟨vF, hvF_S, hvF_dist⟩ := hCover Y
    have hY_ne_vF : Y ≠ vF := fun h => hY_notS (h ▸ hvF_S)
    have hvF_lt : dist Y vF < 2 * r7 := lt_of_le_of_lt hvF_dist (lt_trans eq_2_order.2.1 eq_2_order.2.2)
    -- Every site in sites37 \ E is occupied by (oneVacancy c₀ \ s') ∪ X_in, hence dist Y q ≥ 2 * r7!
    have hadm_E : IsAdmissible r7 (sites37 \ (E : Set H2)) Y := by
      intro q ⟨hqS, hq_notE⟩
      have hq_occ : q ∈ (oneVacancy c₀ \ (s' : Set H2)) ∪ (X : Set H2) := by
        by_cases hq_ins : q ∈ insert c₀ s'
        · have hq_Xin : q ∈ X_in := by
            by_contra hnot
            exact hq_notE (Finset.mem_sdiff.mpr ⟨hq_ins, hnot⟩)
          exact Or.inr (Finset.mem_of_mem_erase hq_Xin)
        · left
          refine ⟨⟨hqS, fun h => hq_ins (h ▸ Finset.mem_insert_self _ _)⟩,
            fun h => hq_ins (Finset.mem_insert_of_mem h)⟩
      exact hX.2.2.2 Y (Or.inr hY_X) q hq_occ (fun h => hY_notS (h ▸ hqS))
    have hvF_in_E : vF ∈ E := by
      by_contra hnot
      have hge := hadm_E vF ⟨hvF_S, hnot⟩
      linarith
    -- E.erase vF has card 1, so at most one neighbor of vF lies in E!
    obtain ⟨Fr⟩ := hFrame vF hvF_S
    have hE_erase_card : (E.erase vF).card = 1 := by
      rw [Finset.card_erase_of_mem hvF_in_E, hE_card]
    obtain ⟨w0, hw0_eq⟩ := Finset.card_eq_one.mp hE_erase_card
    have hfa := lem_2_3_freearc_a sites37 (E : Set H2) vF Fr Y hY_ne_vF hvF_lt hadm_E
    by_cases hex : ∃ j₀ : Fin 7, Fr.nbr j₀ = w0
    · rcases hex with ⟨j₀, hj₀⟩
      apply hfa.2.1
      refine ⟨j₀, fun j hj => ?_⟩
      have hj_ne_vF : Fr.nbr j ≠ vF := by
        intro heq
        have hadj := Fr.adj_self_nbr j
        unfold Adj37 at hadj
        rw [heq, dist_self] at hadj; linarith [r7_pos]
      have hj_in : Fr.nbr j ∈ E.erase vF := Finset.mem_erase.mpr ⟨hj_ne_vF, hj⟩
      rw [hw0_eq, Finset.mem_singleton] at hj_in
      exact Fr.nbr_injective (hj_in.trans hj₀.symm)
    · push Not at hex
      apply hfa.1
      intro j hj
      have hj_ne_vF : Fr.nbr j ≠ vF := by
        intro heq
        have hadj := Fr.adj_self_nbr j
        unfold Adj37 at hadj
        rw [heq, dist_self] at hadj; linarith [r7_pos]
      have hj_in : Fr.nbr j ∈ E.erase vF := Finset.mem_erase.mpr ⟨hj_ne_vF, hj⟩
      rw [hw0_eq, Finset.mem_singleton] at hj_in
      exact hex j hj_in
  -- Part (a2): singletons are good
  have ha2 : ∀ c ∈ oneVacancy c₀, IsGood c₀ {c} := by
    intro c hc
    refine ⟨by simpa using hc, fun X hX => ?_⟩
    by_contra hnt
    have h2 := ha1 {c} X hX hnt
    have hle : (X.filter (fun p => p ∉ sites37)).card ≤ X.card := Finset.card_filter_le _ _
    have h1 : X.card = 1 := by simpa using hX.2.1
    omega
  -- Helper: if Y ∈ X and no element of X.erase Y overlaps c, then X.erase Y is a rearrangement of s
  have hrearr_erase : ∀ (s : Finset H2) (c : H2), IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ∀ (X : Finset H2), IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
      ∀ Y ∈ X, (∀ p ∈ X.erase Y, ¬ Overlaps r7 p c) →
      IsRearrangement r7 (oneVacancy c₀) s (X.erase Y) := by
    intro s c hs hc hcs X hX Y hYX hno_ov
    refine ⟨hs.1, ?_, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hYX, hX.2.1, Finset.card_insert_of_notMem hcs]; omega
    · rw [Set.disjoint_left]
      intro p hp_fix hp_Xe
      by_cases hpc : p = c
      · subst hpc
        have hnov := hno_ov p hp_Xe
        unfold Overlaps at hnov
        rw [dist_self] at hnov; linarith [r7_pos]
      · have hp_fix' : p ∈ oneVacancy c₀ \ (insert c s : Finset H2) := by
          refine ⟨hp_fix.1, ?_⟩
          simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
          exact ⟨hpc, hp_fix.2⟩
        exact Set.disjoint_left.mp hX.2.2.1 hp_fix' (Finset.mem_of_mem_erase hp_Xe)
    · -- IsPacking r7 ((oneVacancy c₀ \ s) ∪ (X.erase Y))
      intro a ha b hb hab
      have hmem_case : ∀ x ∈ (oneVacancy c₀ \ (s : Set H2)) ∪ ((X.erase Y : Finset H2) : Set H2),
          x = c ∨ x ∈ (oneVacancy c₀ \ (insert c s : Finset H2)) ∪ (X : Set H2) := by
        intro x hx
        rcases hx with ⟨hx1, hx2⟩ | hxX
        · by_cases hxc : x = c
          · exact Or.inl hxc
          · right; left; exact ⟨hx1, by simpa [hxc] using hx2⟩
        · right; right; exact Finset.mem_of_mem_erase hxX
      rcases hmem_case a ha with rfl | ha' <;> rcases hmem_case b hb with rfl | hb'
      · exact absurd rfl hab
      · rcases hb' with ⟨hb1, _⟩ | hbX
        · exact hPack a hc.1 b hb1.1 hab
        · have hbXe : b ∈ X.erase Y := by
            rcases hb with ⟨hb1, hb2⟩ | hbXe
            · exfalso
              exact Set.disjoint_left.mp hX.2.2.1 ⟨hb1, by simpa [hab.symm] using hb2⟩ hbX
            · exact hbXe
          have hnov := hno_ov b hbXe
          unfold Overlaps at hnov; rw [dist_comm]; linarith
      · rcases ha' with ⟨ha1, _⟩ | haX
        · exact hPack a ha1.1 b hc.1 hab
        · have haXe : a ∈ X.erase Y := by
            rcases ha with ⟨ha1, ha2⟩ | haXe
            · exfalso
              exact Set.disjoint_left.mp hX.2.2.1 ⟨ha1, by simpa [hab] using ha2⟩ haX
            · exact haXe
          have hnov := hno_ov a haXe
          unfold Overlaps at hnov; linarith
      · exact hX.2.2.2 a ha' b hb' hab
  -- Part (b)
  have hb : ∀ s : Finset H2, ∀ c : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p c)).card := by
    intro s c hs hc hcs hncj X hX hnt
    by_contra hlt; push Not at hlt
    set Ov := X.filter (fun p => Overlaps r7 p c)
    by_cases hOv0 : Ov.card = 0
    · have hno_ov : ∀ p ∈ X, ¬ Overlaps r7 p c := by
        intro p hp hov
        have : p ∈ Ov := Finset.mem_filter.mpr ⟨hp, hov⟩
        rw [Finset.card_eq_zero.mp hOv0] at this
        exact Finset.notMem_empty p this
      by_cases hs_empty : s = ∅
      · subst hs_empty
        exact hncj (ha2 c hc)
      · have hs_pos : 1 ≤ s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs_empty)
        have hX_ge2 : 2 ≤ X.card := by
          rw [hX.2.1, Finset.card_insert_of_notMem hcs]; omega
        have hsub : (X : Set H2) ⊆ sites37 := by
          intro p hp
          obtain ⟨Y, hYX, hYne⟩ : ∃ Y ∈ X, Y ≠ p := by
            have hcard : 1 ≤ (X.erase p).card := by rw [Finset.card_erase_of_mem hp]; omega
            obtain ⟨Y, hY⟩ := Finset.card_pos.mp hcard
            exact ⟨Y, Finset.mem_of_mem_erase hY, Finset.ne_of_mem_erase hY⟩
          have hr := hrearr_erase s c hs hc hcs X hX Y hYX (fun q hq => hno_ov q (Finset.mem_of_mem_erase hq))
          have htr := hs.2 (X.erase Y) hr
          have hsubY := (hTriv s (X.erase Y) hr).mp htr
          exact hsubY (Finset.mem_erase.mpr ⟨hYne.symm, hp⟩)
        exact hnt ((hTriv (insert c s) X hX).mpr hsub)
    · have hOv1 : Ov.card = 1 := by omega
      obtain ⟨Y, hY_eq⟩ := Finset.card_eq_one.mp hOv1
      have hY_Ov : Y ∈ Ov := by rw [hY_eq]; exact Finset.mem_singleton_self Y
      have hY_X : Y ∈ X := (Finset.mem_filter.mp hY_Ov).1
      have hno_ov : ∀ p ∈ X.erase Y, ¬ Overlaps r7 p c := by
        intro p hp hov
        have : p ∈ Ov := Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hp, hov⟩
        rw [hY_eq, Finset.mem_singleton] at this
        exact Finset.ne_of_mem_erase hp this
      have hr := hrearr_erase s c hs hc hcs X hX Y hY_X hno_ov
      have htr := hs.2 (X.erase Y) hr
      have hsubY := (hTriv s (X.erase Y) hr).mp htr
      have hOff_sub : X.filter (fun p => p ∉ sites37) ⊆ {Y} := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpX, hpnotS⟩
        rw [Finset.mem_singleton]
        by_contra hne
        exact hpnotS (hsubY (Finset.mem_erase.mpr ⟨hne, hpX⟩))
      have hle1 : (X.filter (fun p => p ∉ sites37)).card ≤ 1 :=
        le_trans (Finset.card_le_card hOff_sub) (by simp)
      have hge2 := ha1 (insert c s) X hX hnt
      omega
  -- Part (c1): every subset of a good set is good
  have hc1 : ∀ s s' : Finset H2, IsGood c₀ s → s' ⊆ s → IsGood c₀ s' := by
    intro s s' hs hsub
    refine ⟨Set.Subset.trans (Finset.coe_subset.mpr hsub) hs.1, fun X hX => ?_⟩
    set D := s \ s'
    have hdisj_XD : Disjoint X D := by
      rw [Finset.disjoint_left]
      intro p hpX hpD
      have hp_fix : p ∈ oneVacancy c₀ \ (s' : Set H2) :=
        ⟨hs.1 (Finset.mem_sdiff.mp hpD).1, (Finset.mem_sdiff.mp hpD).2⟩
      exact Set.disjoint_left.mp hX.2.2.1 hp_fix hpX
    have hunion_eq : (oneVacancy c₀ \ (s : Set H2)) ∪ ((X ∪ D : Finset H2) : Set H2) =
        (oneVacancy c₀ \ (s' : Set H2)) ∪ (X : Set H2) := by
      ext p
      simp only [Set.mem_union, Set.mem_sdiff, Finset.coe_union, Finset.mem_coe, D, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | hX_p | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, fun hp => h2 (hsub hp)⟩
        · exact Or.inr hX_p
        · exact Or.inl ⟨hs.1 h1, h2⟩
      · rintro (⟨h1, h2⟩ | hX_p)
        · by_cases hps : p ∈ s
          · exact Or.inr (Or.inr ⟨hps, h2⟩)
          · exact Or.inl ⟨h1, hps⟩
        · exact Or.inr (Or.inl hX_p)
    have hXD_rearr : IsRearrangement r7 (oneVacancy c₀) s (X ∪ D) := by
      refine ⟨hs.1, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj_XD, hX.2.1, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
        have := Finset.card_le_card hsub; omega
      · rw [Set.disjoint_left]
        intro p hp_fix hp_XD
        rcases Finset.mem_union.mp hp_XD with hpX | hpD
        · exact Set.disjoint_left.mp hX.2.2.1 ⟨hp_fix.1, fun h => hp_fix.2 (hsub h)⟩ hpX
        · exact hp_fix.2 (Finset.mem_sdiff.mp hpD).1
      · rw [hunion_eq]; exact hX.2.2.2
    have htr := hs.2 (X ∪ D) hXD_rearr
    have hsub_S := (hTriv s (X ∪ D) hXD_rearr).mp htr
    apply (hTriv s' X hX).mpr
    intro p hp
    exact hsub_S (Finset.mem_union_left D hp)
  -- Part (c2): qualifying sites
  have hc2 : ∀ s : Finset H2, ∀ c q : H2, IsGood c₀ s → c ∈ oneVacancy c₀ → c ∉ s →
      ¬ CanJoin c₀ s c → IsQualifying c₀ s c q →
      ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
        ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X →
        2 ≤ (X.filter (fun p => Overlaps r7 p q)).card ∧ q ∉ X := by
    intro s c q hs hc hcs hncj hqual X hX hnt
    set s' := (insert c s).erase q
    have hq_mem : q ∈ insert c s := hqual.1
    have hs'_good : IsGood c₀ s' := hqual.2
    have hq_vac : q ∈ oneVacancy c₀ := by
      rcases Finset.mem_insert.mp hq_mem with rfl | hqs
      · exact hc
      · exact hs.1 hqs
    have hq_not_s' : q ∉ s' := Finset.notMem_erase q (insert c s)
    have hins_eq : insert q s' = insert c s := Finset.insert_erase hq_mem
    have hncj' : ¬ CanJoin c₀ s' q := by
      unfold CanJoin; rw [hins_eq]; exact hncj
    have hge2 := hb s' q hs'_good hq_vac hq_not_s' hncj' X (by rwa [hins_eq]) (by rwa [hins_eq])
    refine ⟨hge2, ?_⟩
    have hpackX : IsPacking r7 (X : Set H2) := fun a ha b hb hab =>
      hX.2.2.2 a (Or.inr ha) b (Or.inr hb) hab
    obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (X.filter (fun p => Overlaps r7 p q)).card)
    exact lem_2_3_freearc_d_conseq X hpackX q
      ⟨P₁, (Finset.mem_filter.mp hP₁).1, P₂, (Finset.mem_filter.mp hP₂).1, hne,
       (Finset.mem_filter.mp hP₁).2, (Finset.mem_filter.mp hP₂).2⟩
  exact ⟨ha1, ha2, hb, hc1, hc2⟩

/-! ### Helper: At most one circle of a rearrangement overlaps both ends of an edge with a fixed common neighbor -/

lemma unique_overlapper_of_edge_with_fixed_nbr (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X)
    {v v' o : H2} (hvv' : Adj37 v v') (hvo : Adj37 v o) (hv'o : Adj37 v' o)
    (ho_fix : o ∈ sites37 \ UnfixedSites c₀ s)
    {P₁ P₂ : H2} (hP₁ : P₁ ∈ X) (hP₂ : P₂ ∈ X)
    (h1v : Overlaps r7 P₁ v) (h1v' : Overlaps r7 P₁ v')
    (h2v : Overlaps r7 P₂ v) (h2v' : Overlaps r7 P₂ v') :
    P₁ = P₂ := by
  by_contra hne
  have hadm1 := isAdmissible_of_mem_rearrangement c₀ s X hX hP₁ o ho_fix
  have hadm2 := isAdmissible_of_mem_rearrangement c₀ s X hX hP₂ o ho_fix
  have hedge := lem_2_4_edge v v' o hvv' hvo hv'o
  have hs1 := hedge.1 P₁ h1v h1v' hadm1
  have hs2 := hedge.1 P₂ h2v h2v' hadm2
  have hsame : 0 < H2.detH v v' P₁ * H2.detH v v' P₂ := by
    have h0 : H2.detH v v' o ≠ 0 := by intro h0; rw [h0, mul_zero] at hs1; exact lt_irrefl 0 hs1
    have hsq : 0 < H2.detH v v' o ^ 2 := sq_pos_of_ne_zero h0
    have hprod : 0 < (H2.detH v v' P₁ * H2.detH v v' o) * (H2.detH v v' P₂ * H2.detH v v' o) :=
      mul_pos_of_neg_of_neg hs1 hs2
    nlinarith
  have hlt := hedge.2 P₁ P₂ h1v h1v' h2v h2v' hsame
  have hge := hX.2.2.2 P₁ (Or.inr hP₁) P₂ (Or.inr hP₂) hne
  linarith

/-! ### Remark 4.2: `τ₃` Edge-Count -/

/-- **Remark 4.2 (`τ₃` Edge-Count)**, hypothesis-parametrized. -/
theorem rem_4_2_tau3_edge_count (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37))
    (s : Finset H2) (c q : H2) (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hqual : IsQualifying c₀ s c q) (F : SiteFrame sites37 q)
    (hprof : HasProfile sites37 (UnfixedSites c₀ (insert c s)) q 3 F)
    (X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) (insert c s) X)
    (hnt : ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X) :
    ∃ P₁ ∈ X, ∃ P₂ ∈ X, P₁ ≠ P₂ ∧
      (∀ P ∈ X, Overlaps r7 P q ↔ P = P₁ ∨ P = P₂) ∧
      Overlaps r7 P₁ (F.nbr 0) ∧ ¬ Overlaps r7 P₁ (F.nbr 2) ∧
      Overlaps r7 P₂ (F.nbr 2) ∧ ¬ Overlaps r7 P₂ (F.nbr 0) := by
  have hncj : ¬ CanJoin c₀ s c := fun hcj => hnt (hcj.2 X hX)
  have hbridge := lem_4_1_bridge c₀ hc₀ hPack hFrame hCover hTriv
  obtain ⟨hge2, hq_notX⟩ := hbridge.2.2.2.2 s c q hs hc hcs hncj hqual X hX hnt
  -- Uniqueness on edges (q, F.nbr 0) using fixed common neighbor F.nbr 6,
  -- and (q, F.nbr 2) using fixed common neighbor F.nbr 3!
  have huniq0 : ∀ A ∈ X, ∀ B ∈ X, Overlaps r7 A q → Overlaps r7 A (F.nbr 0) →
      Overlaps r7 B q → Overlaps r7 B (F.nbr 0) → A = B := by
    intro A hA B hB hAq hA0 hBq hB0
    let j6 : Fin 7 := ⟨6, by norm_num⟩
    have h6_fix : F.nbr j6 ∈ sites37 \ UnfixedSites c₀ (insert c s) :=
      ⟨F.nbr_mem j6, by rw [hprof j6]; dsimp [j6]; omega⟩
    have hadj06 : Adj37 (F.nbr 0) (F.nbr j6) :=
      (F.adj_nbr_iff ⟨0, by norm_num⟩ j6).mpr (Or.inr (by norm_num))
    exact unique_overlapper_of_edge_with_fixed_nbr c₀ (insert c s) X hX
      (F.adj_self_nbr 0) (F.adj_self_nbr j6) hadj06 h6_fix hA hB hAq hA0 hBq hB0
  have huniq2 : ∀ A ∈ X, ∀ B ∈ X, Overlaps r7 A q → Overlaps r7 A (F.nbr 2) →
      Overlaps r7 B q → Overlaps r7 B (F.nbr 2) → A = B := by
    intro A hA B hB hAq hA2 hBq hB2
    let j3 : Fin 7 := ⟨3, by norm_num⟩
    have h3_fix : F.nbr j3 ∈ sites37 \ UnfixedSites c₀ (insert c s) :=
      ⟨F.nbr_mem j3, by rw [hprof j3]; dsimp [j3]; omega⟩
    have hadj23 : Adj37 (F.nbr 2) (F.nbr j3) :=
      (F.adj_nbr_iff ⟨2, by norm_num⟩ j3).mpr (Or.inl (by norm_num))
    exact unique_overlapper_of_edge_with_fixed_nbr c₀ (insert c s) X hX
      (F.adj_self_nbr 2) (F.adj_self_nbr j3) hadj23 h3_fix hA hB hAq hA2 hBq hB2
  have hor02 : ∀ P ∈ X, Overlaps r7 P q → Overlaps r7 P (F.nbr 0) ∨ Overlaps r7 P (F.nbr 2) := by
    intro P hPX hPq
    have hPne : P ≠ q := fun h => hq_notX (h ▸ hPX)
    have hadm := isAdmissible_of_mem_rearrangement c₀ (insert c s) X hX hPX
    obtain ⟨_, _, _, _, _, _, _, hor, _⟩ :=
      lem_2_3_freearc_b sites37 (UnfixedSites c₀ (insert c s)) q F hprof P hPne hPq hadm
    exact hor
  -- Pick two distinct overlappers A, B of q in X
  obtain ⟨A, hA_f, B, hB_f, hAB_ne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (X.filter (fun p => Overlaps r7 p q)).card)
  obtain ⟨hAX, hAq⟩ := Finset.mem_filter.mp hA_f
  obtain ⟨hBX, hBq⟩ := Finset.mem_filter.mp hB_f
  rcases hor02 A hAX hAq with hA0 | hA2
  · -- A overlaps F.nbr 0; hence B cannot overlap F.nbr 0 (else A = B), so B overlaps F.nbr 2,
    -- and A cannot overlap F.nbr 2 (else A = B)!
    have hBn0 : ¬ Overlaps r7 B (F.nbr 0) := fun hB0 => hAB_ne (huniq0 A hAX B hBX hAq hA0 hBq hB0)
    have hB2 : Overlaps r7 B (F.nbr 2) := (hor02 B hBX hBq).resolve_left hBn0
    have hAn2 : ¬ Overlaps r7 A (F.nbr 2) := fun hA2 => hAB_ne (huniq2 A hAX B hBX hAq hA2 hBq hB2)
    refine ⟨A, hAX, B, hBX, hAB_ne, ?_, hA0, hAn2, hB2, hBn0⟩
    intro P hPX
    constructor
    · intro hPq
      rcases hor02 P hPX hPq with hP0 | hP2
      · exact Or.inl (huniq0 P hPX A hAX hPq hP0 hAq hA0)
      · exact Or.inr (huniq2 P hPX B hBX hPq hP2 hBq hB2)
    · rintro (rfl | rfl) <;> assumption
  · -- A overlaps F.nbr 2; hence B cannot overlap F.nbr 2, so B overlaps F.nbr 0, and A doesn't overlap F.nbr 0!
    have hBn2 : ¬ Overlaps r7 B (F.nbr 2) := fun hB2 => hAB_ne (huniq2 A hAX B hBX hAq hA2 hBq hB2)
    have hB0 : Overlaps r7 B (F.nbr 0) := (hor02 B hBX hBq).resolve_right hBn2
    have hAn0 : ¬ Overlaps r7 A (F.nbr 0) := fun hA0 => hAB_ne (huniq0 A hAX B hBX hAq hA0 hBq hB0)
    refine ⟨B, hBX, A, hAX, hAB_ne.symm, ?_, hB0, hBn2, hA2, hAn0⟩
    intro P hPX
    constructor
    · intro hPq
      rcases hor02 P hPX hPq with hP0 | hP2
      · exact Or.inl (huniq0 P hPX B hBX hPq hP0 hBq hB0)
      · exact Or.inr (huniq2 P hPX A hAX hPq hP2 hAq hA2)
    · rintro (rfl | rfl) <;> assumption

/-! ### Helper: No site with at most 2 unfixed neighbors can have 2 distinct overlappers in X -/

lemma not_two_overlappers_of_le_two_unfixed (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X)
    {q : H2} (F : SiteFrame sites37 q) (hq_notX : q ∉ X)
    (hle2 : (Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ UnfixedSites c₀ s)).card ≤ 2)
    (hge2 : 2 ≤ (X.filter (fun p => Overlaps r7 p q)).card) :
    False := by
  set U := UnfixedSites c₀ s
  set J := Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ U)
  obtain ⟨P₁, hP₁_f, P₂, hP₂_f, hne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (X.filter (fun p => Overlaps r7 p q)).card)
  obtain ⟨hP₁X, hP₁q⟩ := Finset.mem_filter.mp hP₁_f
  obtain ⟨hP₂X, hP₂q⟩ := Finset.mem_filter.mp hP₂_f
  have hP₁ne : P₁ ≠ q := fun h => hq_notX (h ▸ hP₁X)
  have hP₂ne : P₂ ≠ q := fun h => hq_notX (h ▸ hP₂X)
  have hadm1 := isAdmissible_of_mem_rearrangement c₀ s X hX hP₁X
  have hadm2 := isAdmissible_of_mem_rearrangement c₀ s X hX hP₂X
  have hfa1 := lem_2_3_freearc_a sites37 U q F P₁ hP₁ne hP₁q hadm1
  by_cases hJ0 : J.card = 0
  · apply hfa1.1
    intro j hj
    have : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [Finset.card_eq_zero.mp hJ0] at this; exact Finset.notMem_empty j this
  · by_cases hJ1 : J.card = 1
    · obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hJ1
      apply hfa1.2.1
      refine ⟨j₀, fun j hj => ?_⟩
      have : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [hj₀, Finset.mem_singleton] at this; exact this
    · have hJ2 : J.card = 2 := by omega
      obtain ⟨j₁, j₂, hjne, hJeq⟩ := Finset.card_eq_two.mp hJ2
      by_cases hadj : (j₁.1 + 1) % 7 = j₂.1 ∨ (j₂.1 + 1) % 7 = j₁.1
      · -- Rotate F so the two consecutive unfixed neighbors sit at 0 and 1!
        obtain ⟨s_rot, hprof2⟩ : ∃ s_rot : ℤ, HasProfile sites37 U q 2 (F.rotate s_rot) := by
          rcases hadj with h12 | h21
          · refine ⟨j₁, fun k => ?_⟩
            rw [F.rotate_nbr, F.nbr_mod_seven]
            let idx : Fin 7 := ⟨(((k : ℤ) + j₁) % 7).toNat, by omega⟩
            have hidx : (idx : ℤ) = ((k : ℤ) + j₁) % 7 :=
              Int.toNat_of_nonneg (Int.emod_nonneg ((k : ℤ) + j₁) (by norm_num : (7 : ℤ) ≠ 0))
            rw [← hidx]
            have hmem : F.nbr idx ∈ U ↔ idx ∈ J := by simp [J]
            rw [hmem, hJeq, Finset.mem_insert, Finset.mem_singleton]
            have hk7 := k.2; have hj17 := j₁.2; have hj27 := j₂.2
            constructor
            · rintro (heq | heq)
              · have hval : idx.1 = j₁.1 := congrArg Fin.val heq
                dsimp [idx] at hval; omega
              · have hval : idx.1 = j₂.1 := congrArg Fin.val heq
                dsimp [idx] at hval; omega
            · intro hlt
              have hk01 : k.1 = 0 ∨ k.1 = 1 := by omega
              rcases hk01 with hk0 | hk1
              · left; apply Fin.ext; dsimp [idx]; omega
              · right; apply Fin.ext; dsimp [idx]; omega
          · refine ⟨j₂, fun k => ?_⟩
            rw [F.rotate_nbr, F.nbr_mod_seven]
            let idx : Fin 7 := ⟨(((k : ℤ) + j₂) % 7).toNat, by omega⟩
            have hidx : (idx : ℤ) = ((k : ℤ) + j₂) % 7 :=
              Int.toNat_of_nonneg (Int.emod_nonneg ((k : ℤ) + j₂) (by norm_num : (7 : ℤ) ≠ 0))
            rw [← hidx]
            have hmem : F.nbr idx ∈ U ↔ idx ∈ J := by simp [J]
            rw [hmem, hJeq, Finset.mem_insert, Finset.mem_singleton]
            have hk7 := k.2; have hj17 := j₁.2; have hj27 := j₂.2
            constructor
            · rintro (heq | heq)
              · have hval : idx.1 = j₁.1 := congrArg Fin.val heq
                dsimp [idx] at hval; omega
              · have hval : idx.1 = j₂.1 := congrArg Fin.val heq
                dsimp [idx] at hval; omega
            · intro hlt
              have hk01 : k.1 = 0 ∨ k.1 = 1 := by omega
              rcases hk01 with hk0 | hk1
              · right; apply Fin.ext; dsimp [idx]; omega
              · left; apply Fin.ext; dsimp [idx]; omega
        set Fr := F.rotate s_rot
        have hov0 : ∀ P : H2, P ≠ q → dist P q < 2 * r7 → IsAdmissible r7 (sites37 \ U) P →
            Overlaps r7 P (Fr.nbr 0) := by
          intro P hPne hPq hadm
          obtain ⟨θ, hP_eq, hlo, hhi⟩ :=
            (lem_2_3_freearc_a sites37 U q Fr P hPne hPq hadm).2.2.2 2 (Or.inl rfl) hprof2
          norm_num at hhi
          have hρ0 : 0 < dist P q := dist_pos.mpr hPne
          have hα_lt_β : α7 < β7 (dist P q) := text_2_beta_properties.2.2.2.2.2.1 _ ⟨hρ0, hPq⟩
          have hβ_lt_pi2 : β7 (dist P q) < Real.pi / 2 := beta7_lt_pi_div_two hρ0 hPq.le
          have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; norm_num; ring
          unfold Overlaps; rw [hP_eq]
          apply (lem_2_2_polar Fr.φ (dist P q) θ (((0 : ℤ) : ℝ) * α7) hρ0 hPq.le).1.mpr
          have h0 : θ - ((0 : ℤ) : ℝ) * α7 = θ := by norm_num
          rw [h0, arccos_cos_eq_abs (by linarith) (by linarith), abs_lt]
          constructor <;> linarith
        have hP₁0 := hov0 P₁ hP₁ne hP₁q hadm1
        have hP₂0 := hov0 P₂ hP₂ne hP₂q hadm2
        let j6 : Fin 7 := ⟨6, by norm_num⟩
        have h6_fix : Fr.nbr j6 ∈ sites37 \ U :=
          ⟨Fr.nbr_mem j6, by rw [hprof2 j6]; dsimp [j6]; omega⟩
        have hadj06 : Adj37 (Fr.nbr 0) (Fr.nbr j6) :=
          (Fr.adj_nbr_iff ⟨0, by norm_num⟩ j6).mpr (Or.inr (by norm_num))
        exact hne (unique_overlapper_of_edge_with_fixed_nbr c₀ s X hX
          (Fr.adj_self_nbr 0) (Fr.adj_self_nbr j6) hadj06 h6_fix hP₁X hP₂X hP₁q hP₁0 hP₂q hP₂0)
      · push Not at hadj
        apply hfa1.2.2.1
        refine ⟨j₁, j₂, fun j hj => ?_, hadj.1, hadj.2⟩
        have : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        rw [hJeq, Finset.mem_insert, Finset.mem_singleton] at this; exact this

/-! ### Lemma 4.3: Joining with at most two unfixed neighbors -/

/-- **Lemma 4.3 (Joining with at most two unfixed neighbors)**, hypothesis-parametrized. -/
theorem lem_4_3_join_le_two (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37))
    (s : Finset H2) (c : H2) (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (F : SiteFrame sites37 c)
    (hle2 : (Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ UnfixedSites c₀ (insert c s))).card ≤ 2) :
    CanJoin c₀ s c := by
  by_contra hncj
  have hsub : ((insert c s : Finset H2) : Set H2) ⊆ oneVacancy c₀ := by
    rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨hc, hs.1⟩
  have hnot_all : ¬ ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
      IsTrivialRearrangement (oneVacancy c₀) (insert c s) X := fun hall => hncj ⟨hsub, hall⟩
  push Not at hnot_all
  obtain ⟨X, hX, hnt⟩ := hnot_all
  have hbridge := lem_4_1_bridge c₀ hc₀ hPack hFrame hCover hTriv
  have hge2 := hbridge.2.2.1 s c hs hc hcs hncj X hX hnt
  have hc_notX : c ∉ X := by
    have hpackX : IsPacking r7 (X : Set H2) := fun a ha b hb hab =>
      hX.2.2.2 a (Or.inr ha) b (Or.inr hb) hab
    obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (X.filter (fun p => Overlaps r7 p c)).card)
    exact lem_2_3_freearc_d_conseq X hpackX c
      ⟨P₁, (Finset.mem_filter.mp hP₁).1, P₂, (Finset.mem_filter.mp hP₂).1, hne,
       (Finset.mem_filter.mp hP₁).2, (Finset.mem_filter.mp hP₂).2⟩
  exact not_two_overlappers_of_le_two_unfixed c₀ (insert c s) X hX F hc_notX hle2 hge2

/-! ### Helper: From `τ₃` frame at `v` with `Z` on `(v, nbr 2) \ nbr 0`, `Z ∈ K2` (and mirror for `(v, nbr 0) \ nbr 2`) -/

lemma mem_K2_of_tau3_overlap_nbr2 {V U : Set H2} {v P : H2} (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F) (hadm : IsAdmissible r7 (V \ U) P)
    (hPv : Overlaps r7 P v) (hPne : P ≠ v)
    (_hP2 : Overlaps r7 P (F.nbr 2)) (hPn0 : ¬ Overlaps r7 P (F.nbr 0)) :
    P ∈ F.K2 := by
  obtain ⟨θ, hP_eq, _, hhi, _, hov0, _, _, _⟩ :=
    lem_2_3_freearc_b V U v F hprof P hPne hPv hadm
  have hθ_ge : β7 (dist P v) ≤ θ := by
    by_contra hlt; push Not at hlt; exact hPn0 (hov0.mpr hlt)
  exact ⟨dist P v, θ, dist_pos.mpr hPne, hPv, hθ_ge, hhi, hP_eq⟩

lemma mem_K2Mirror_of_tau3_overlap_nbr0 {V U : Set H2} {v P : H2} (F : SiteFrame V v)
    (hprof : HasProfile V U v 3 F) (hadm : IsAdmissible r7 (V \ U) P)
    (hPv : Overlaps r7 P v) (hPne : P ≠ v)
    (_hP0 : Overlaps r7 P (F.nbr 0)) (hPn2 : ¬ Overlaps r7 P (F.nbr 2)) :
    P ∈ F.K2Mirror := by
  obtain ⟨θ, hP_eq, hlo, _, _, _, hov2, _, _⟩ :=
    lem_2_3_freearc_b V U v F hprof P hPne hPv hadm
  have hθ_le : θ ≤ 2 * α7 - β7 (dist P v) := by
    by_contra hgt; push Not at hgt; exact hPn2 (hov2.mpr hgt)
  exact ⟨dist P v, θ, dist_pos.mpr hPne, hPv, hlo, hθ_le, hP_eq⟩

/-! ### Helper: A `τ₃` site `q` whose unfixed neighbors lie in `{F.nbr 0, F.nbr 1, F.nbr 2}` with `F.nbr 1, F.nbr 2` unfixed
    and `q` having ≥ 2 overlappers in `X` MUST have `F.nbr 0` unfixed (hence full profile `τ₃`)! -/

lemma hasProfile3_of_subset_three_and_two_overlappers (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X)
    {q : H2} (F : SiteFrame sites37 q) (hq_notX : q ∉ X)
    (hge2 : 2 ≤ (X.filter (fun p => Overlaps r7 p q)).card)
    (hsub : ∀ j : Fin 7, F.nbr j ∈ UnfixedSites c₀ s → j.1 < 3)
    (h1u : F.nbr 1 ∈ UnfixedSites c₀ s) (h2u : F.nbr 2 ∈ UnfixedSites c₀ s) :
    HasProfile sites37 (UnfixedSites c₀ s) q 3 F := by
  have h0u : F.nbr 0 ∈ UnfixedSites c₀ s := by
    by_contra hnot0
    apply not_two_overlappers_of_le_two_unfixed c₀ s X hX F hq_notX _ hge2
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ UnfixedSites c₀ s) ⊆
        ({⟨1, by norm_num⟩, ⟨2, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      have hlt := hsub j hjU
      have hj0 : j ≠ ⟨0, by norm_num⟩ := fun heq => hnot0 (by simpa [heq] using hjU)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have : j.1 = 1 ∨ j.1 = 2 := by
        have : j.1 ≠ 0 := fun h => hj0 (Fin.ext h)
        omega
      rcases this with h1 | h2
      · left; exact Fin.ext h1
      · right; exact Fin.ext h2
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  intro j
  constructor
  · exact hsub j
  · intro hlt
    have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ := by
      have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
      rcases this with h | h | h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; exact Fin.ext h
    rcases this with rfl | rfl | rfl
    · exact h0u
    · exact h1u
    · exact h2u

/-! ### Lemma 4.4: Profile-`τ₃` joining lemma -/

/-- **Lemma 4.4 (Profile-`τ₃` joining lemma)**, hypothesis-parametrized. -/
theorem lem_4_4_join_tau3 (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37))
    (s : Finset H2) (c c₁ c₂ c₃ c₄ c₅ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (Fc : SiteFrame sites37 c)
    (hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc)
    (hc1_eq : Fc.nbr 0 = c₁) (hc2_eq : Fc.nbr 1 = c₂) (hc3_eq : Fc.nbr 2 = c₃)
    (hc1_s : c₁ ∈ s) (hc3_s : c₃ ∈ s)
    (_hc4_adj1 : Adj37 c₄ c₁) (hc4_adj2 : Adj37 c₄ c₂) (hc4_ne : c₄ ≠ c)
    (hc5_adj2 : Adj37 c₅ c₂) (_hc5_adj3 : Adj37 c₅ c₃) (hc5_ne : c₅ ≠ c)
    (hu1 : ∀ w ∈ sites37, Adj37 c₁ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₄ ∨ w = c₂ ∨ w = c)
    (hu3 : ∀ w ∈ sites37, Adj37 c₃ w → w ∈ UnfixedSites c₀ (insert c s) → w = c ∨ w = c₂ ∨ w = c₅) :
    CanJoin c₀ s c := by
  by_contra hncj
  have hsub : ((insert c s : Finset H2) : Set H2) ⊆ oneVacancy c₀ := by
    rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨hc, hs.1⟩
  have hnot_all : ¬ ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
      IsTrivialRearrangement (oneVacancy c₀) (insert c s) X := fun hall => hncj ⟨hsub, hall⟩
  push Not at hnot_all
  obtain ⟨X, hX, hnt⟩ := hnot_all
  have hbridge := lem_4_1_bridge c₀ hc₀ hPack hFrame hCover hTriv
  -- Both c₁ and c₃ qualify (by Lemma 4.3 on s.erase c₁ and s.erase c₃)
  have hqual_c : IsQualifying c₀ s c c := ⟨Finset.mem_insert_self c s, by
    rwa [Finset.erase_insert hcs]⟩
  have hqual_c1 : IsQualifying c₀ s c c₁ := by
    refine ⟨Finset.mem_insert_of_mem hc1_s, ?_⟩
    have hc_ne_c1 : c ≠ c₁ := fun h => hcs (h ▸ hc1_s)
    have herase_eq : (insert c s).erase c₁ = insert c (s.erase c₁) := Finset.erase_insert_of_ne hc_ne_c1
    rw [herase_eq]
    have hs1_good : IsGood c₀ (s.erase c₁) := hbridge.2.2.2.1 s (s.erase c₁) hs (Finset.erase_subset c₁ s)
    apply lem_4_3_join_le_two c₀ hc₀ hPack hFrame hCover hTriv (s.erase c₁) c hs1_good hc
      (fun h => hcs (Finset.mem_of_mem_erase h)) Fc
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc.nbr j ∈ UnfixedSites c₀ (insert c (s.erase c₁))) ⊆
        ({⟨1, by norm_num⟩, ⟨2, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      have hjU_big : Fc.nbr j ∈ UnfixedSites c₀ (insert c s) := by
        rcases hjU with h | h
        · left; rw [← herase_eq] at h; exact Finset.mem_of_mem_erase h
        · exact Or.inr h
      have hlt := (hprof_c j).mp hjU_big
      have hj0 : j ≠ ⟨0, by norm_num⟩ := by
        intro heq; subst heq
        change Fc.nbr 0 ∈ UnfixedSites c₀ (insert c (s.erase c₁)) at hjU
        rw [hc1_eq] at hjU
        rcases hjU with h | h
        · rw [← herase_eq] at h; exact Finset.notMem_erase c₁ (insert c s) h
        · exact (hs.1 hc1_s).2 h
      have : j.1 = 1 ∨ j.1 = 2 := by
        have : j.1 ≠ 0 := fun h => hj0 (Fin.ext h)
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h1 | h2
      · left; exact Fin.ext h1
      · right; exact Fin.ext h2
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  have hqual_c3 : IsQualifying c₀ s c c₃ := by
    refine ⟨Finset.mem_insert_of_mem hc3_s, ?_⟩
    have hc_ne_c3 : c ≠ c₃ := fun h => hcs (h ▸ hc3_s)
    have herase_eq : (insert c s).erase c₃ = insert c (s.erase c₃) := Finset.erase_insert_of_ne hc_ne_c3
    rw [herase_eq]
    have hs3_good : IsGood c₀ (s.erase c₃) := hbridge.2.2.2.1 s (s.erase c₃) hs (Finset.erase_subset c₃ s)
    apply lem_4_3_join_le_two c₀ hc₀ hPack hFrame hCover hTriv (s.erase c₃) c hs3_good hc
      (fun h => hcs (Finset.mem_of_mem_erase h)) Fc
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc.nbr j ∈ UnfixedSites c₀ (insert c (s.erase c₃))) ⊆
        ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      have hjU_big : Fc.nbr j ∈ UnfixedSites c₀ (insert c s) := by
        rcases hjU with h | h
        · left; rw [← herase_eq] at h; exact Finset.mem_of_mem_erase h
        · exact Or.inr h
      have hlt := (hprof_c j).mp hjU_big
      have hj2 : j ≠ ⟨2, by norm_num⟩ := by
        intro heq; subst heq
        change Fc.nbr 2 ∈ UnfixedSites c₀ (insert c (s.erase c₃)) at hjU
        rw [hc3_eq] at hjU
        rcases hjU with h | h
        · rw [← herase_eq] at h; exact Finset.notMem_erase c₃ (insert c s) h
        · exact (hs.1 hc3_s).2 h
      have : j.1 = 0 ∨ j.1 = 1 := by
        have : j.1 ≠ 2 := fun h => hj2 (Fin.ext h)
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h0 | h1
      · left; exact Fin.ext h0
      · right; exact Fin.ext h1
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  -- Align frames Fc1 at c₁ (0 ↦ c₄, 1 ↦ c₂, 2 ↦ c) and Fc3 at c₃ (0 ↦ c, 1 ↦ c₂, 2 ↦ c₅)
  have hc1_S : c₁ ∈ sites37 := (hs.1 hc1_s).1
  have hc2_S : c₂ ∈ sites37 := hc2_eq ▸ Fc.nbr_mem 1
  have hc3_S : c₃ ∈ sites37 := (hs.1 hc3_s).1
  have hc_S : c ∈ sites37 := hc.1
  have hadj_c1c2 : Adj37 c₁ c₂ := hc1_eq ▸ hc2_eq ▸ Fc.adj_nbr_consec 0
  have hadj_c2c3 : Adj37 c₂ c₃ := hc2_eq ▸ hc3_eq ▸ Fc.adj_nbr_consec 1
  have hadj_cc1 : Adj37 c c₁ := hc1_eq ▸ Fc.adj_self_nbr 0
  have hadj_cc2 : Adj37 c c₂ := hc2_eq ▸ Fc.adj_self_nbr 1
  have hadj_cc3 : Adj37 c c₃ := hc3_eq ▸ Fc.adj_self_nbr 2
  have hadj_c1c : Adj37 c₁ c := by unfold Adj37 at *; rwa [dist_comm]
  have hadj_c3c : Adj37 c₃ c := by unfold Adj37 at *; rwa [dist_comm]
  have hadj_c3c2 : Adj37 c₃ c₂ := by unfold Adj37 at *; rwa [dist_comm]
  -- Align Fc1 so nbr 1 = c₂, nbr 2 = c (start with nbr 0 = c₂, nbr 1 = c, then rotate by -1!)
  obtain ⟨Fc1_raw⟩ := hFrame c₁ hc1_S
  obtain ⟨Fc1_0, h10_0, h10_1⟩ := Fc1_raw.align hc2_S hc_S hadj_c1c2 hadj_c1c (by unfold Adj37 at *; rwa [dist_comm])
  set Fc1 := Fc1_0.rotate (-1)
  have hFc1_1 : Fc1.nbr 1 = c₂ := by rw [Fc1_0.rotate_nbr]; simpa using h10_0
  have hFc1_2 : Fc1.nbr 2 = c := by rw [Fc1_0.rotate_nbr]; simpa using h10_1
  -- Show Fc1.nbr 0 = c₄? Wait: we don't even know c₄ ∈ sites37 from the signature,
  -- wait: check if c₄ ∈ sites37 is needed! If c₄ ∉ sites37, then hu1 only says w ∈ sites37 → w = c₄ ∨ c₂ ∨ c,
  -- so if Fc1.nbr 0 ≠ c₄ then Fc1.nbr 0 ∉ UnfixedSites!
  -- Actually, ANY site w ∈ sites37 adjacent to c₁ and c₂ with w ≠ c MUST equal Fc1.nbr 0!
  -- And if c₄ ∈ sites37 then Fc1.nbr 0 = c₄; if c₄ ∉ sites37 then c₁ has ≤ 2 unfixed neighbors (impossible!).
  -- Let's prove directly: for all j : Fin 7, Fc1.nbr j ∈ U → j.1 < 3!
  have hc1_U : ∀ j : Fin 7, Fc1.nbr j ∈ UnfixedSites c₀ (insert c s) → j.1 < 3 := by
    intro j hjU
    have hj_eq := hu1 (Fc1.nbr j) (Fc1.nbr_mem j) (Fc1.adj_self_nbr j) hjU
    rcases hj_eq with h4 | h2 | hcc
    · have hj0 : Fc1.nbr j = Fc1.nbr ((⟨1, by norm_num⟩ : Fin 7).1 - 1 : ℤ) := by
        apply Fc1.nbr_prev_of_common_nbr ⟨1, by norm_num⟩ (Fc1.nbr_mem j) (Fc1.adj_self_nbr j)
        · change Adj37 (Fc1.nbr 1) (Fc1.nbr j)
          rw [hFc1_1, h4]; unfold Adj37 at *; rwa [dist_comm]
        · change Fc1.nbr j ≠ Fc1.nbr 2
          rw [hFc1_2, h4]; exact hc4_ne
      have hj_eq0 : j = ⟨0, by norm_num⟩ := Fc1.nbr_injective (by simpa using hj0)
      rw [hj_eq0]; norm_num
    · have : j = ⟨1, by norm_num⟩ := Fc1.nbr_injective (h2.trans hFc1_1.symm)
      rw [this]; norm_num
    · have : j = ⟨2, by norm_num⟩ := Fc1.nbr_injective (hcc.trans hFc1_2.symm)
      rw [this]; norm_num
  have hprof_c1 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₁ 3 Fc1 := by
    obtain ⟨hge2_1, hnotX_1⟩ := hbridge.2.2.2.2 s c c₁ hs hc hcs hncj hqual_c1 X hX hnt
    have hc2_u : c₂ ∈ UnfixedSites c₀ (insert c s) := hc2_eq ▸ (hprof_c ⟨1, by norm_num⟩).mpr (by norm_num)
    have hc_u : c ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_self c s)
    exact hasProfile3_of_subset_three_and_two_overlappers c₀ (insert c s) X hX Fc1 hnotX_1 hge2_1
      hc1_U (hFc1_1.symm ▸ hc2_u) (hFc1_2.symm ▸ hc_u)
  -- Symmetrically align Fc3 at c₃ so nbr 0 = c, nbr 1 = c₂!
  obtain ⟨Fc3_raw⟩ := hFrame c₃ hc3_S
  obtain ⟨Fc3, hFc3_0, hFc3_1⟩ := Fc3_raw.align hc_S hc2_S hadj_c3c hadj_c3c2 hadj_cc2
  have hc3_U : ∀ j : Fin 7, Fc3.nbr j ∈ UnfixedSites c₀ (insert c s) → j.1 < 3 := by
    intro j hjU
    have hj_eq := hu3 (Fc3.nbr j) (Fc3.nbr_mem j) (Fc3.adj_self_nbr j) hjU
    rcases hj_eq with hcc | h2 | h5
    · have : j = ⟨0, by norm_num⟩ := Fc3.nbr_injective (hcc.trans hFc3_0.symm)
      rw [this]; norm_num
    · have : j = ⟨1, by norm_num⟩ := Fc3.nbr_injective (h2.trans hFc3_1.symm)
      rw [this]; norm_num
    · have hj2 : Fc3.nbr j = Fc3.nbr ((⟨1, by norm_num⟩ : Fin 7).1 + 1 : ℤ) := by
        apply Fc3.nbr_next_of_common_nbr ⟨1, by norm_num⟩ (Fc3.nbr_mem j) (Fc3.adj_self_nbr j)
        · change Adj37 (Fc3.nbr 1) (Fc3.nbr j)
          rw [hFc3_1, h5]; unfold Adj37 at *; rwa [dist_comm]
        · change Fc3.nbr j ≠ Fc3.nbr 0
          rw [hFc3_0, h5]; exact hc5_ne
      have hj_eq2 : j = ⟨2, by norm_num⟩ := Fc3.nbr_injective (by simpa using hj2)
      rw [hj_eq2]; norm_num
  have hprof_c3 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₃ 3 Fc3 := by
    obtain ⟨hge2_3, hnotX_3⟩ := hbridge.2.2.2.2 s c c₃ hs hc hcs hncj hqual_c3 X hX hnt
    -- Mirror hasProfile3_of_subset_three_and_two_overlappers via Fc3.reflect or directly:
    have hc2_u : c₂ ∈ UnfixedSites c₀ (insert c s) := hc2_eq ▸ (hprof_c ⟨1, by norm_num⟩).mpr (by norm_num)
    have hc_u : c ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_self c s)
    have h2u : Fc3.nbr 2 ∈ UnfixedSites c₀ (insert c s) := by
      by_contra hnot2
      apply not_two_overlappers_of_le_two_unfixed c₀ (insert c s) X hX Fc3 hnotX_3 _ hge2_3
      have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc3.nbr j ∈ UnfixedSites c₀ (insert c s)) ⊆
          ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset (Fin 7)) := by
        intro j hj
        have hjU := (Finset.mem_filter.mp hj).2
        have hlt := hc3_U j hjU
        have hj2 : j ≠ ⟨2, by norm_num⟩ := fun heq => hnot2 (by simpa [heq] using hjU)
        have : j.1 = 0 ∨ j.1 = 1 := by
          have : j.1 ≠ 2 := fun h => hj2 (Fin.ext h)
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases this with h0 | h1
        · left; exact Fin.ext h0
        · right; exact Fin.ext h1
      exact le_trans (Finset.card_le_card hsub2) (by decide)
    intro j
    constructor
    · exact hc3_U j
    · intro hlt
      have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ := by
        have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
        rcases this with h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
      rcases this with rfl | rfl | rfl
      · exact hFc3_0.symm ▸ hc_u
      · exact hFc3_1.symm ▸ hc2_u
      · exact h2u
  -- Apply Remark 4.2 at c, c₁, c₃!
  obtain ⟨Z, hZX, W, hWX, hZW_ne, hc_ov, hZ_c1, hZ_nc3, hW_c3, hW_nc1⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c hs hc hcs hqual_c Fc hprof_c X hX hnt
  rw [hc1_eq] at hZ_c1 hW_nc1
  rw [hc3_eq] at hZ_nc3 hW_c3
  have hZ_c : Overlaps r7 Z c := (hc_ov Z hZX).mpr (Or.inl rfl)
  have hW_c : Overlaps r7 W c := (hc_ov W hWX).mpr (Or.inr rfl)
  obtain ⟨Y₁, hY1X, Z', hZ'X, hY1Z'_ne, hc1_ov, hY1_n0, hY1_nc, hZ'_c, hZ'_nn0⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c₁ hs hc hcs hqual_c1 Fc1 hprof_c1 X hX hnt
  rw [hFc1_2] at hY1_nc hZ'_c
  have hZ_eq_Z' : Z = Z' := by
    have hZ_in : Z = Y₁ ∨ Z = Z' := (hc1_ov Z hZX).mp hZ_c1
    rcases hZ_in with rfl | rfl
    · exact absurd hZ_c hY1_nc
    · rfl
  subst hZ_eq_Z'
  obtain ⟨W', hW'X, Y₂, hY2X, hW'Y2_ne, hc3_ov, hW'_c, hW'_nn2, hY2_n2, hY2_nc⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c₃ hs hc hcs hqual_c3 Fc3 hprof_c3 X hX hnt
  rw [hFc3_0] at hW'_c hY2_nc
  have hW_eq_W' : W = W' := by
    have hW_in : W = W' ∨ W = Y₂ := (hc3_ov W hWX).mp hW_c3
    rcases hW_in with rfl | rfl
    · rfl
    · exact absurd hW_c hY2_nc
  subst hW_eq_W'
  -- Now Z ∈ Fc1.K2 and W ∈ Fc3.K2Mirror!
  have hc1_notX : c₁ ∉ X := (hbridge.2.2.2.2 s c c₁ hs hc hcs hncj hqual_c1 X hX hnt).2
  have hc3_notX : c₃ ∉ X := (hbridge.2.2.2.2 s c c₃ hs hc hcs hncj hqual_c3 X hX hnt).2
  have hZ_K2 : Z ∈ Fc1.K2 :=
    mem_K2_of_tau3_overlap_nbr2 Fc1 hprof_c1
      (isAdmissible_of_mem_rearrangement c₀ (insert c s) X hX hZX)
      hZ_c1 (fun h => hc1_notX (h ▸ hZX)) (hFc1_2.symm ▸ hZ_c) hZ'_nn0
  have hW_K2M : W ∈ Fc3.K2Mirror :=
    mem_K2Mirror_of_tau3_overlap_nbr0 Fc3 hprof_c3
      (isAdmissible_of_mem_rearrangement c₀ (insert c s) X hX hWX)
      hW_c3 (fun h => hc3_notX (h ▸ hWX)) (hFc3_0.symm ▸ hW_c) hW'_nn2
  obtain ⟨hZM_le, hZM_eq⟩ := (lem_3_2_tip_disc sites37 c₁ Fc1).1 Z hZ_K2
  obtain ⟨hWM_le, _⟩ := (lem_3_2_tip_disc sites37 c₃ Fc3).2 W hW_K2M
  rw [hFc1_1, hFc1_2] at hZM_le hZM_eq
  rw [hFc3_0, hFc3_1, mid_comm c c₂] at hWM_le
  -- 2*r7 ≤ dist Z W ≤ dist Z M + dist M W ≤ 2*r7 forces Z = Fc1.tip12!
  have hZW_ge : 2 * r7 ≤ dist Z W := hX.2.2.2 Z (Or.inr hZX) W (Or.inr hWX) hZW_ne
  have htri : dist Z W ≤ dist Z (H2.mid c₂ c) + dist (H2.mid c₂ c) W := dist_triangle _ _ _
  rw [dist_comm (H2.mid c₂ c) W] at htri
  have hZM_r : dist Z (H2.mid c₂ c) = r7 := by linarith
  have hZ_tip : Z = Fc1.tip12 := hZM_eq.mp hZM_r
  -- Lemma 3.3 at c₁ gives dist Y₁ Z = dist Y₁ Fc1.tip12 < 2*r7, contradicting Y₁ ≠ Z in packing X!
  have hY1_c1 : Overlaps r7 Y₁ c₁ := (hc1_ov Y₁ hY1X).mpr (Or.inl rfl)
  have hY1Z_lt : dist Y₁ Z < 2 * r7 := by
    rw [hZ_tip]
    exact lem_3_3_half_lens sites37 (UnfixedSites c₀ (insert c s)) c₁ Fc1 hprof_c1 Y₁
      (isAdmissible_of_mem_rearrangement c₀ (insert c s) X hX hY1X) hY1_n0 hY1_c1
  have hY1Z_ge : 2 * r7 ≤ dist Y₁ Z := hX.2.2.2 Y₁ (Or.inr hY1X) Z (Or.inr hZX) hY1Z'_ne
  linarith

/-! ### Lemma 4.5 named proof steps (Steps 1–5) and the Nine-site closing lemma -/

/-- **Lemma 4.5, Step 1 (Edge counts)**: From `τ₃` profiles at the four qualifying sites
    `c, c₁, c₆, c₇` in a non-trivial rearrangement `X` of `insert c s`, there exist overlappers
    `Y₁` on `(c₄, c₁)` only, `Z` on `(c₁, c)` only, `W` on `(c, c₃)` only, `E` on `(c₃, c₆)` only,
    `V₁` on `(c₆, c₇)` only, and `V₂` on `(c₇, c₈)` only. -/
theorem lem_4_5_step1_edge_counts (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37))
    (s : Finset H2) (c c₁ c₃ c₄ c₆ c₇ c₈ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hqual_c : IsQualifying c₀ s c c) (hqual_c1 : IsQualifying c₀ s c c₁)
    (hqual_c6 : IsQualifying c₀ s c c₆) (hqual_c7 : IsQualifying c₀ s c c₇)
    (Fc : SiteFrame sites37 c) (hFc_0 : Fc.nbr 0 = c₁) (hFc_2 : Fc.nbr 2 = c₃)
    (hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc)
    (Fc1 : SiteFrame sites37 c₁) (hFc1_0 : Fc1.nbr 0 = c₄) (hFc1_2 : Fc1.nbr 2 = c)
    (hprof_c1 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₁ 3 Fc1)
    (Fc6 : SiteFrame sites37 c₆) (hFc6_0 : Fc6.nbr 0 = c₃) (hFc6_2 : Fc6.nbr 2 = c₇)
    (hprof_c6 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₆ 3 Fc6)
    (Fc7 : SiteFrame sites37 c₇) (hFc7_0 : Fc7.nbr 0 = c₈) (hFc7_2 : Fc7.nbr 2 = c₆)
    (hprof_c7 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₇ 3 Fc7)
    (X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) (insert c s) X)
    (hnt : ¬ IsTrivialRearrangement (oneVacancy c₀) (insert c s) X) :
    ∃ Y₁ ∈ X, ∃ Z ∈ X, ∃ W ∈ X, ∃ E ∈ X, ∃ V₁ ∈ X, ∃ V₂ ∈ X,
      Z ≠ W ∧ Y₁ ≠ Z ∧ E ≠ V₁ ∧ V₂ ≠ V₁ ∧
      (∀ P ∈ X, Overlaps r7 P c ↔ P = Z ∨ P = W) ∧
      (∀ P ∈ X, Overlaps r7 P c₁ ↔ P = Y₁ ∨ P = Z) ∧
      (∀ P ∈ X, Overlaps r7 P c₆ ↔ P = E ∨ P = V₁) ∧
      (∀ P ∈ X, Overlaps r7 P c₇ ↔ P = V₂ ∨ P = V₁) ∧
      Overlaps r7 Y₁ c₄ ∧ ¬ Overlaps r7 Y₁ c ∧
      Overlaps r7 Z c₁ ∧ ¬ Overlaps r7 Z c₃ ∧ ¬ Overlaps r7 Z c₄ ∧
      Overlaps r7 W c₃ ∧ ¬ Overlaps r7 W c₁ ∧
      Overlaps r7 E c₃ ∧ ¬ Overlaps r7 E c₇ ∧
      Overlaps r7 V₁ c₇ ∧ ¬ Overlaps r7 V₁ c₃ ∧ ¬ Overlaps r7 V₁ c₈ ∧
      Overlaps r7 V₂ c₈ ∧ ¬ Overlaps r7 V₂ c₆ := by
  obtain ⟨Z, hZX, W, hWX, hZW_ne, hc_ov, hZ_c1, hZ_nc3, hW_c3, hW_nc1⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c hs hc hcs hqual_c Fc hprof_c X hX hnt
  rw [hFc_0] at hZ_c1 hW_nc1
  rw [hFc_2] at hZ_nc3 hW_c3
  have hZ_c : Overlaps r7 Z c := (hc_ov Z hZX).mpr (Or.inl rfl)
  obtain ⟨Y₁, hY1X, Z', hZ'X, hY1Z'_ne, hc1_ov, hY1_c4, hY1_nc, hZ'_c, hZ'_nc4⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c₁ hs hc hcs hqual_c1 Fc1 hprof_c1 X hX hnt
  rw [hFc1_0] at hY1_c4 hZ'_nc4
  rw [hFc1_2] at hY1_nc hZ'_c
  have hZ_eq : Z = Z' := by
    rcases (hc1_ov Z hZX).mp hZ_c1 with rfl | rfl
    · exact absurd hZ_c hY1_nc
    · rfl
  subst hZ_eq
  obtain ⟨E, hEX, V₁, hV1X, hEV1_ne, hc6_ov, hE_c3, hE_nc7, hV1_c7, hV1_nc3⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c₆ hs hc hcs hqual_c6 Fc6 hprof_c6 X hX hnt
  rw [hFc6_0] at hE_c3 hV1_nc3
  rw [hFc6_2] at hE_nc7 hV1_c7
  have hV1_c6 : Overlaps r7 V₁ c₆ := (hc6_ov V₁ hV1X).mpr (Or.inr rfl)
  obtain ⟨V₂, hV2X, V₁', hV1'X, hV2V1'_ne, hc7_ov, hV2_c8, hV2_nc6, hV1'_c6, hV1'_nc8⟩ :=
    rem_4_2_tau3_edge_count c₀ hc₀ hPack hFrame hCover hTriv s c c₇ hs hc hcs hqual_c7 Fc7 hprof_c7 X hX hnt
  rw [hFc7_0] at hV2_c8 hV1'_nc8
  rw [hFc7_2] at hV2_nc6 hV1'_c6
  have hV1_eq : V₁ = V₁' := by
    rcases (hc7_ov V₁ hV1X).mp hV1_c7 with rfl | rfl
    · exact absurd hV1_c6 hV2_nc6
    · rfl
  subst hV1_eq
  exact ⟨Y₁, hY1X, Z, hZX, W, hWX, E, hEX, V₁, hV1X, V₂, hV2X,
    hZW_ne, hY1Z'_ne, hEV1_ne, hV2V1'_ne, hc_ov, hc1_ov, hc6_ov, hc7_ov,
    hY1_c4, hY1_nc, hZ_c1, hZ_nc3, hZ'_nc4, hW_c3, hW_nc1,
    hE_c3, hE_nc7, hV1_c7, hV1_nc3, hV1'_nc8, hV2_c8, hV2_nc6⟩

/-- **Lemma 4.5, Step 2 (`W` overlaps `c₅`)**: In any packing `X` of points admissible against
    `sites37 \ U`, given `τ₃` at `c₁` (`c₄, c₂, c`), `τ₄` at `c₃` (`c, c₂, c₅, c₆`), and distinct
    `Y₁, Z, W ∈ X` with `Y₁` on `(c₄, c₁)`, `Z` on `(c₁, c) \ c₄`, and `W` on `c₃`,
    `W` must overlap `c₅`. -/
theorem lem_4_5_step2_W_overlaps_c5 (U : Set H2) (c c₁ c₂ c₃ c₄ c₅ c₆ : H2)
    (Fc1 : SiteFrame sites37 c₁)
    (hFc1_0 : Fc1.nbr 0 = c₄) (hFc1_1 : Fc1.nbr 1 = c₂) (hFc1_2 : Fc1.nbr 2 = c)
    (hprof_c1 : HasProfile sites37 U c₁ 3 Fc1)
    (Fc3 : SiteFrame sites37 c₃)
    (hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (_hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc1_notX : c₁ ∉ X) (hc3_notX : c₃ ∉ X)
    (Y₁ Z W : H2) (hY1X : Y₁ ∈ X) (hZX : Z ∈ X) (hWX : W ∈ X)
    (hZW_ne : Z ≠ W) (hY1Z_ne : Y₁ ≠ Z)
    (hY1_c1 : Overlaps r7 Y₁ c₁) (hY1_c4 : Overlaps r7 Y₁ c₄)
    (hZ_c1 : Overlaps r7 Z c₁) (hZ_c : Overlaps r7 Z c) (hZ_nc4 : ¬ Overlaps r7 Z c₄)
    (hW_c3 : Overlaps r7 W c₃) :
    Overlaps r7 W c₅ := by
  by_contra hWn5
  obtain ⟨θW, hW_eq, hWlo, _, _, _, hW_ov2, _, _⟩ :=
    lem_2_3_freearc_c sites37 U c₃ Fc3 hprof_c3 W
      (fun h => hc3_notX (h ▸ hWX)) hW_c3 (hadmX W hWX)
  rw [hFc3_2] at hW_ov2
  have hθW_le : θW ≤ 2 * α7 - β7 (dist W c₃) := by
    by_contra hgt; push Not at hgt; exact hWn5 (hW_ov2.mpr hgt)
  have hW_K2M : W ∈ Fc3.K2Mirror :=
    ⟨dist W c₃, θW, dist_pos.mpr (fun h => hc3_notX (h ▸ hWX)), hW_c3, hWlo, hθW_le, hW_eq⟩
  have hWM_le := ((lem_3_2_tip_disc sites37 c₃ Fc3).2 W hW_K2M).1
  rw [hFc3_0, hFc3_1, mid_comm c c₂] at hWM_le
  have hZ_K2 : Z ∈ Fc1.K2 :=
    mem_K2_of_tau3_overlap_nbr2 Fc1 hprof_c1 (hadmX Z hZX)
      hZ_c1 (fun h => hc1_notX (h ▸ hZX)) (hFc1_2.symm ▸ hZ_c) (hFc1_0.symm ▸ hZ_nc4)
  obtain ⟨hZM_le, hZM_eq⟩ := (lem_3_2_tip_disc sites37 c₁ Fc1).1 Z hZ_K2
  rw [hFc1_1, hFc1_2] at hZM_le hZM_eq
  have hZW_ge : 2 * r7 ≤ dist Z W := hpackX Z hZX W hWX hZW_ne
  have htri : dist Z W ≤ dist Z (H2.mid c₂ c) + dist (H2.mid c₂ c) W := dist_triangle _ _ _
  rw [dist_comm (H2.mid c₂ c) W] at htri
  have hZ_tip : Z = Fc1.tip12 := hZM_eq.mp (by linarith)
  have hY1Z_lt : dist Y₁ Z < 2 * r7 := by
    rw [hZ_tip]
    exact lem_3_3_half_lens sites37 U c₁ Fc1 hprof_c1 Y₁ (hadmX Y₁ hY1X)
      (hFc1_0.symm ▸ hY1_c4) hY1_c1
  have hY1Z_ge : 2 * r7 ≤ dist Y₁ Z := hpackX Y₁ hY1X Z hZX hY1Z_ne
  linarith

/-- **Lemma 4.5, Step 3 (`E` overlaps `c₂`)**: Symmetrically, given `τ₄` at `c₃` (`c, c₂, c₅, c₆`),
    `τ₃` at `c₇` (`c₈, c₅, c₆`), and distinct `E, V₁, V₂ ∈ X` with `E` on `c₃`, `V₁` on `(c₆, c₇) \ c₈`,
    and `V₂` on `(c₇, c₈)`, `E` must overlap `c₂`. -/
theorem lem_4_5_step3_E_overlaps_c2 (U : Set H2) (c c₂ c₃ c₅ c₆ c₇ c₈ : H2)
    (Fc3 : SiteFrame sites37 c₃)
    (_hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (Fc7 : SiteFrame sites37 c₇)
    (hFc7_0 : Fc7.nbr 0 = c₈) (hFc7_1 : Fc7.nbr 1 = c₅) (hFc7_2 : Fc7.nbr 2 = c₆)
    (hprof_c7 : HasProfile sites37 U c₇ 3 Fc7)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc3_notX : c₃ ∉ X) (hc7_notX : c₇ ∉ X)
    (E V₁ V₂ : H2) (hEX : E ∈ X) (hV1X : V₁ ∈ X) (hV2X : V₂ ∈ X)
    (hEV1_ne : E ≠ V₁) (hV2V1_ne : V₂ ≠ V₁)
    (hE_c3 : Overlaps r7 E c₃)
    (hV1_c7 : Overlaps r7 V₁ c₇) (hV1_c6 : Overlaps r7 V₁ c₆) (hV1_nc8 : ¬ Overlaps r7 V₁ c₈)
    (hV2_c7 : Overlaps r7 V₂ c₇) (hV2_c8 : Overlaps r7 V₂ c₈) :
    Overlaps r7 E c₂ := by
  by_contra hEn2
  obtain ⟨θE, hE_eq, _, hEhi, _, hE_ov1, _, _, _⟩ :=
    lem_2_3_freearc_c sites37 U c₃ Fc3 hprof_c3 E
      (fun h => hc3_notX (h ▸ hEX)) hE_c3 (hadmX E hEX)
  rw [hFc3_1] at hE_ov1
  have hθE_ge : α7 + β7 (dist E c₃) ≤ θE := by
    by_contra hlt; push Not at hlt; exact hEn2 (hE_ov1.mpr hlt)
  set Fc3' := Fc3.rotate 1
  have hFc3'_1 : Fc3'.nbr 1 = c₅ := by rw [Fc3.rotate_nbr]; exact hFc3_2
  have hFc3'_2 : Fc3'.nbr 2 = c₆ := by rw [Fc3.rotate_nbr]; exact hFc3_3
  have hE_K2' : E ∈ Fc3'.K2 := by
    refine ⟨dist E c₃, θE - α7, dist_pos.mpr (fun h => hc3_notX (h ▸ hEX)), hE_c3,
      by linarith, by linarith, ?_⟩
    conv_lhs => rw [hE_eq]
    change Fc3.φ (H2.polarOrigin (dist E c₃) θE) =
      Fc3.φ (H2.rotOrigin (((1 : ℤ) : ℝ) * α7) (H2.polarOrigin (dist E c₃) (θE - α7)))
    congr 1
    have h1 : (((1 : ℤ) : ℝ) * α7) = α7 := by norm_num
    have hth : θE = (θE - α7) + α7 := by ring
    rw [h1]
    ext
    · simp only [rotOrigin_x, H2.polarOrigin]; (conv_lhs => rw [hth, Real.cos_add]); ring
    · simp only [rotOrigin_y, H2.polarOrigin]; (conv_lhs => rw [hth, Real.sin_add]); ring
    · simp only [rotOrigin_z, H2.polarOrigin]
  have hEM_le := ((lem_3_2_tip_disc sites37 c₃ Fc3').1 E hE_K2').1
  rw [hFc3'_1, hFc3'_2] at hEM_le
  have hV1_K2 : V₁ ∈ Fc7.K2 :=
    mem_K2_of_tau3_overlap_nbr2 Fc7 hprof_c7 (hadmX V₁ hV1X)
      hV1_c7 (fun h => hc7_notX (h ▸ hV1X)) (hFc7_2.symm ▸ hV1_c6) (hFc7_0.symm ▸ hV1_nc8)
  obtain ⟨hV1M_le, hV1M_eq⟩ := (lem_3_2_tip_disc sites37 c₇ Fc7).1 V₁ hV1_K2
  rw [hFc7_1, hFc7_2] at hV1M_le hV1M_eq
  have hV1E_ge : 2 * r7 ≤ dist V₁ E := hpackX V₁ hV1X E hEX hEV1_ne.symm
  have htri : dist V₁ E ≤ dist V₁ (H2.mid c₅ c₆) + dist (H2.mid c₅ c₆) E := dist_triangle _ _ _
  rw [dist_comm (H2.mid c₅ c₆) E] at htri
  have hV1_tip : V₁ = Fc7.tip12 := hV1M_eq.mp (by linarith)
  have hV2V1_lt : dist V₂ V₁ < 2 * r7 := by
    rw [hV1_tip]
    exact lem_3_3_half_lens sites37 U c₇ Fc7 hprof_c7 V₂ (hadmX V₂ hV2X)
      (hFc7_0.symm ▸ hV2_c8) hV2_c7
  have hV2V1_ge : 2 * r7 ≤ dist V₂ V₁ := hpackX V₂ hV2X V₁ hV1X hV2V1_ne
  linarith

/-- **Lemma 4.5, Step 4 (`W = E`)**: Since `W` overlaps `c₂, c₃, c₅` (via `τ₃` at `c` + Step 2)
    and `E` overlaps `c₂, c₃, c₅` (via `τ₃` at `c₆` + Step 3), the Reuleaux-Triangle Lemma
    forces `W = E` (and `W` overlaps `c₂`). -/
theorem lem_4_5_step4_W_eq_E (U : Set H2) (c c₂ c₃ c₅ c₆ : H2)
    (hadj_c2c3 : Adj37 c₂ c₃) (hadj_c3c5 : Adj37 c₃ c₅) (hadj_c5c2 : Adj37 c₅ c₂)
    (Fc : SiteFrame sites37 c) (hFc_1 : Fc.nbr 1 = c₂)
    (hprof_c : HasProfile sites37 U c 3 Fc)
    (Fc6 : SiteFrame sites37 c₆) (hFc6_1 : Fc6.nbr 1 = c₅)
    (hprof_c6 : HasProfile sites37 U c₆ 3 Fc6)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc_notX : c ∉ X) (hc6_notX : c₆ ∉ X)
    (W E : H2) (hWX : W ∈ X) (hEX : E ∈ X)
    (hW_c : Overlaps r7 W c) (hW_c3 : Overlaps r7 W c₃) (hW_c5 : Overlaps r7 W c₅)
    (hE_c6 : Overlaps r7 E c₆) (hE_c3 : Overlaps r7 E c₃) (hE_c2 : Overlaps r7 E c₂) :
    W = E ∧ Overlaps r7 W c₂ := by
  have hW_c2 : Overlaps r7 W c₂ := by
    obtain ⟨_, _, _, _, h, _⟩ := lem_2_3_freearc_b sites37 U c Fc hprof_c W
      (fun h => hc_notX (h ▸ hWX)) hW_c (hadmX W hWX)
    rwa [hFc_1] at h
  have hE_c5 : Overlaps r7 E c₅ := by
    obtain ⟨_, _, _, _, h, _⟩ := lem_2_3_freearc_b sites37 U c₆ Fc6 hprof_c6 E
      (fun h => hc6_notX (h ▸ hEX)) hE_c6 (hadmX E hEX)
    rwa [hFc6_1] at h
  refine ⟨?_, hW_c2⟩
  by_contra hne
  have hlt := lem_2_5_reuleaux c₂ c₃ c₅ W E hadj_c2c3 hadj_c3c5 hadj_c5c2
    hW_c2 hW_c3 hW_c5 hE_c2 hE_c3 hE_c5
  have hge := hpackX W hWX E hEX hne
  linarith

/-- **Lemma 4.5, Step 5 (Contradiction at `c₃`)**: At the `τ₄` site `c₃` (`c, c₂, c₅, c₆`),
    if `W ∈ X` overlaps `c₂, c₃, c₅` and a second overlapper `G ∈ X` (`G ≠ W`) of `c₃`
    overlaps neither `c` nor `c₆`, then `G` also overlaps `c₂, c₅`, contradicting Lemma 2.5. -/
theorem lem_4_5_step5_contradiction_at_c3 (U : Set H2) (c c₂ c₃ c₅ c₆ : H2)
    (hadj_c2c3 : Adj37 c₂ c₃) (hadj_c3c5 : Adj37 c₃ c₅) (hadj_c5c2 : Adj37 c₅ c₂)
    (Fc3 : SiteFrame sites37 c₃)
    (hFc3_0 : Fc3.nbr 0 = c) (hFc3_1 : Fc3.nbr 1 = c₂) (hFc3_2 : Fc3.nbr 2 = c₅)
    (hFc3_3 : Fc3.nbr 3 = c₆)
    (hprof_c3 : HasProfile sites37 U c₃ 4 Fc3)
    (X : Finset H2) (hpackX : IsPacking r7 (X : Set H2))
    (hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ U) P)
    (hc3_notX : c₃ ∉ X)
    (W G : H2) (hWX : W ∈ X) (hGX : G ∈ X) (hGW_ne : G ≠ W)
    (hW_c2 : Overlaps r7 W c₂) (hW_c3 : Overlaps r7 W c₃) (hW_c5 : Overlaps r7 W c₅)
    (hG_c3 : Overlaps r7 G c₃) (hGn_c : ¬ Overlaps r7 G c) (hGn_c6 : ¬ Overlaps r7 G c₆) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, hG_fa⟩ :=
    lem_2_3_freearc_c sites37 U c₃ Fc3 hprof_c3 G
      (fun h => hc3_notX (h ▸ hGX)) hG_c3 (hadmX G hGX)
  rw [hFc3_0, hFc3_1, hFc3_2, hFc3_3] at hG_fa
  obtain ⟨_, _, hG_c2, hG_c5⟩ := hG_fa hGn_c hGn_c6
  have hGW_lt := lem_2_5_reuleaux c₂ c₃ c₅ G W hadj_c2c3 hadj_c3c5 hadj_c5c2
    hG_c2 hG_c3 hG_c5 hW_c2 hW_c3 hW_c5
  have hGW_ge := hpackX G hGX W hWX hGW_ne
  linarith

/-- **Lemma 4.5 (Nine-site closing lemma)**, hypothesis-parametrized. -/
theorem lem_4_5_nine_site (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (hPack : IsPacking r7 sites37)
    (hFrame : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v))
    (hCover : ∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7)
    (hTriv : ∀ s X : Finset H2, IsRearrangement r7 (oneVacancy c₀) s X →
      (IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37))
    (s : Finset H2) (c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (hdistinct : [c, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈].Nodup)
    (Fc2 : SiteFrame sites37 c₂)
    (h2_0 : Fc2.nbr 0 = c₄) (h2_1 : Fc2.nbr 1 = c₁) (h2_2 : Fc2.nbr 2 = c)
    (h2_3 : Fc2.nbr 3 = c₃) (h2_4 : Fc2.nbr 4 = c₅)
    (Fc5 : SiteFrame sites37 c₅)
    (h5_0 : Fc5.nbr 0 = c₂) (h5_1 : Fc5.nbr 1 = c₃) (h5_2 : Fc5.nbr 2 = c₆)
    (h5_3 : Fc5.nbr 3 = c₇) (h5_4 : Fc5.nbr 4 = c₈)
    (hc1_s : c₁ ∈ s) (hc3_s : c₃ ∈ s) (hc6_s : c₆ ∈ s) (hc7_s : c₇ ∈ s)
    (hc2_u : c₂ ∈ UnfixedSites c₀ (insert c s)) (hc5_u : c₅ ∈ UnfixedSites c₀ (insert c s))
    (huc : ∀ w ∈ sites37, Adj37 c w → w ∈ UnfixedSites c₀ (insert c s) → w = c₁ ∨ w = c₂ ∨ w = c₃)
    (hu1 : ∀ w ∈ sites37, Adj37 c₁ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₄ ∨ w = c₂ ∨ w = c)
    (hu3 : ∀ w ∈ sites37, Adj37 c₃ w → w ∈ UnfixedSites c₀ (insert c s) →
      w = c ∨ w = c₂ ∨ w = c₅ ∨ w = c₆)
    (hu6 : ∀ w ∈ sites37, Adj37 c₆ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₃ ∨ w = c₅ ∨ w = c₇)
    (hu7 : ∀ w ∈ sites37, Adj37 c₇ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₆ ∨ w = c₅ ∨ w = c₈) :
    CanJoin c₀ s c := by
  by_contra hncj
  have hsub : ((insert c s : Finset H2) : Set H2) ⊆ oneVacancy c₀ := by
    rw [Finset.coe_insert, Set.insert_subset_iff]; exact ⟨hc, hs.1⟩
  have hnot_all : ¬ ∀ X : Finset H2, IsRearrangement r7 (oneVacancy c₀) (insert c s) X →
      IsTrivialRearrangement (oneVacancy c₀) (insert c s) X := fun hall => hncj ⟨hsub, hall⟩
  push Not at hnot_all
  obtain ⟨X, hX, hnt⟩ := hnot_all
  have hbridge := lem_4_1_bridge c₀ hc₀ hPack hFrame hCover hTriv
  -- Extract pairwise distinctness facts from hdistinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hdistinct
  -- Site memberships and adjacencies from Fc2 and Fc5
  have hc4_S : c₄ ∈ sites37 := h2_0 ▸ Fc2.nbr_mem 0
  have hc1_S : c₁ ∈ sites37 := h2_1 ▸ Fc2.nbr_mem 1
  have hc_S : c ∈ sites37 := h2_2 ▸ Fc2.nbr_mem 2
  have hc3_S : c₃ ∈ sites37 := h2_3 ▸ Fc2.nbr_mem 3
  have hc5_S : c₅ ∈ sites37 := h2_4 ▸ Fc2.nbr_mem 4
  have hc2_S : c₂ ∈ sites37 := h5_0 ▸ Fc5.nbr_mem 0
  have hc6_S : c₆ ∈ sites37 := h5_2 ▸ Fc5.nbr_mem 2
  have hc7_S : c₇ ∈ sites37 := h5_3 ▸ Fc5.nbr_mem 3
  have hc8_S : c₈ ∈ sites37 := h5_4 ▸ Fc5.nbr_mem 4
  have hadj_symm : ∀ a b : H2, Adj37 a b → Adj37 b a := fun a b h => by unfold Adj37 at *; rwa [dist_comm]
  have hadj_c2c4 : Adj37 c₂ c₄ := h2_0 ▸ Fc2.adj_self_nbr 0
  have hadj_c2c1 : Adj37 c₂ c₁ := h2_1 ▸ Fc2.adj_self_nbr 1
  have hadj_c2c : Adj37 c₂ c := h2_2 ▸ Fc2.adj_self_nbr 2
  have hadj_c2c3 : Adj37 c₂ c₃ := h2_3 ▸ Fc2.adj_self_nbr 3
  have hadj_c2c5 : Adj37 c₂ c₅ := h2_4 ▸ Fc2.adj_self_nbr 4
  have hadj_c4c1 : Adj37 c₄ c₁ := h2_0 ▸ h2_1 ▸ Fc2.adj_nbr_consec 0
  have hadj_c1c : Adj37 c₁ c := h2_1 ▸ h2_2 ▸ Fc2.adj_nbr_consec 1
  have hadj_cc3 : Adj37 c c₃ := h2_2 ▸ h2_3 ▸ Fc2.adj_nbr_consec 2
  have hadj_c3c5 : Adj37 c₃ c₅ := h2_3 ▸ h2_4 ▸ Fc2.adj_nbr_consec 3
  have hadj_c5c6 : Adj37 c₅ c₆ := h5_2 ▸ Fc5.adj_self_nbr 2
  have hadj_c5c7 : Adj37 c₅ c₇ := h5_3 ▸ Fc5.adj_self_nbr 3
  have hadj_c5c8 : Adj37 c₅ c₈ := h5_4 ▸ Fc5.adj_self_nbr 4
  have hadj_c3c6 : Adj37 c₃ c₆ := h5_1 ▸ h5_2 ▸ Fc5.adj_nbr_consec 1
  have hadj_c6c7 : Adj37 c₆ c₇ := h5_2 ▸ h5_3 ▸ Fc5.adj_nbr_consec 2
  have hadj_c7c8 : Adj37 c₇ c₈ := h5_3 ▸ h5_4 ▸ Fc5.adj_nbr_consec 3
  -- Align frames at c, c₁, c₃, c₆, c₇!
  -- Fc at c: nbr 0 = c₁, nbr 1 = c₂, nbr 2 = c₃
  obtain ⟨Fc_raw⟩ := hFrame c hc_S
  obtain ⟨Fc, hFc_0, hFc_1⟩ := Fc_raw.align hc1_S hc2_S (hadj_symm _ _ hadj_c1c) (hadj_symm _ _ hadj_c2c) (hadj_symm _ _ hadj_c2c1)
  have hFc_2 : Fc.nbr 2 = c₃ := (Fc.nbr_next_of_common_nbr ⟨1, by norm_num⟩ hc3_S hadj_cc3
    (hFc_1.symm ▸ hadj_c2c3) (by rw [show ((⟨1, by norm_num⟩ : Fin 7) : ℤ) - 1 = 0 by norm_num, hFc_0]; exact Ne.symm hdistinct.2.1.2.1)).symm
  -- Fc1 at c₁: nbr 0 = c₄, nbr 1 = c₂, nbr 2 = c
  obtain ⟨Fc1_raw⟩ := hFrame c₁ hc1_S
  obtain ⟨Fc1_0, h10_0, h10_1⟩ := Fc1_raw.align hc2_S hc_S (hadj_symm _ _ hadj_c2c1) hadj_c1c hadj_c2c
  set Fc1 := Fc1_0.rotate (-1)
  have hFc1_1 : Fc1.nbr 1 = c₂ := by rw [Fc1_0.rotate_nbr]; simpa using h10_0
  have hFc1_2 : Fc1.nbr 2 = c := by rw [Fc1_0.rotate_nbr]; simpa using h10_1
  have hFc1_0 : Fc1.nbr 0 = c₄ := (Fc1.nbr_prev_of_common_nbr ⟨1, by norm_num⟩ hc4_S (hadj_symm _ _ hadj_c4c1)
    (hFc1_1.symm ▸ hadj_c2c4) (by rw [show ((⟨1, by norm_num⟩ : Fin 7) : ℤ) + 1 = 2 by norm_num, hFc1_2]; exact Ne.symm hdistinct.1.2.2.2.1)).symm
  -- Fc3 at c₃: nbr 0 = c, nbr 1 = c₂, nbr 2 = c₅, nbr 3 = c₆
  obtain ⟨Fc3_raw⟩ := hFrame c₃ hc3_S
  obtain ⟨Fc3, hFc3_0, hFc3_1⟩ := Fc3_raw.align hc_S hc2_S (hadj_symm _ _ hadj_cc3) (hadj_symm _ _ hadj_c2c3) (hadj_symm _ _ hadj_c2c)
  have hFc3_2 : Fc3.nbr 2 = c₅ := (Fc3.nbr_next_of_common_nbr ⟨1, by norm_num⟩ hc5_S hadj_c3c5
    (hFc3_1.symm ▸ hadj_c2c5) (by rw [show ((⟨1, by norm_num⟩ : Fin 7) : ℤ) - 1 = 0 by norm_num, hFc3_0]; exact Ne.symm hdistinct.1.2.2.2.2.1)).symm
  have hFc3_3 : Fc3.nbr 3 = c₆ := (Fc3.nbr_next_of_common_nbr ⟨2, by norm_num⟩ hc6_S hadj_c3c6
    (hFc3_2.symm ▸ hadj_c5c6) (by rw [show ((⟨2, by norm_num⟩ : Fin 7) : ℤ) - 1 = 1 by norm_num, hFc3_1]; exact Ne.symm hdistinct.2.2.1.2.2.2.1)).symm
  -- Fc6 at c₆: nbr 0 = c₃, nbr 1 = c₅, nbr 2 = c₇
  obtain ⟨Fc6_raw⟩ := hFrame c₆ hc6_S
  obtain ⟨Fc6, hFc6_0, hFc6_1⟩ := Fc6_raw.align hc3_S hc5_S (hadj_symm _ _ hadj_c3c6) (hadj_symm _ _ hadj_c5c6) hadj_c3c5
  have hFc6_2 : Fc6.nbr 2 = c₇ := (Fc6.nbr_next_of_common_nbr ⟨1, by norm_num⟩ hc7_S hadj_c6c7
    (hFc6_1.symm ▸ hadj_c5c7) (by rw [show ((⟨1, by norm_num⟩ : Fin 7) : ℤ) - 1 = 0 by norm_num, hFc6_0]; exact Ne.symm hdistinct.2.2.2.1.2.2.2.1)).symm
  -- Fc7 at c₇: nbr 0 = c₈, nbr 1 = c₅, nbr 2 = c₆
  obtain ⟨Fc7_raw⟩ := hFrame c₇ hc7_S
  obtain ⟨Fc7_0, h70_0, h70_1⟩ := Fc7_raw.align hc5_S hc6_S (hadj_symm _ _ hadj_c5c7) (hadj_symm _ _ hadj_c6c7) hadj_c5c6
  set Fc7 := Fc7_0.rotate (-1)
  have hFc7_1 : Fc7.nbr 1 = c₅ := by rw [Fc7_0.rotate_nbr]; simpa using h70_0
  have hFc7_2 : Fc7.nbr 2 = c₆ := by rw [Fc7_0.rotate_nbr]; simpa using h70_1
  have hFc7_0 : Fc7.nbr 0 = c₈ := (Fc7.nbr_prev_of_common_nbr ⟨1, by norm_num⟩ hc8_S hadj_c7c8
    (hFc7_1.symm ▸ hadj_c5c8) (by rw [show ((⟨1, by norm_num⟩ : Fin 7) : ℤ) + 1 = 2 by norm_num, hFc7_2]; exact Ne.symm hdistinct.2.2.2.2.2.2.1.2)).symm
  -- Unfixed memberships
  have hc_u : c ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_self c s)
  have hc1_u : c₁ ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_of_mem hc1_s)
  have hc3_u : c₃ ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_of_mem hc3_s)
  have hc6_u : c₆ ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_of_mem hc6_s)
  have hc7_u : c₇ ∈ UnfixedSites c₀ (insert c s) := Or.inl (Finset.mem_insert_of_mem hc7_s)
  -- Profile τ₃ at c
  have hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc := by
    intro j
    constructor
    · intro hjU
      rcases huc (Fc.nbr j) (Fc.nbr_mem j) (Fc.adj_self_nbr j) hjU with h | h | h
      · have : j = ⟨0, by norm_num⟩ := Fc.nbr_injective (h.trans hFc_0.symm); rw [this]; norm_num
      · have : j = ⟨1, by norm_num⟩ := Fc.nbr_injective (h.trans hFc_1.symm); rw [this]; norm_num
      · have : j = ⟨2, by norm_num⟩ := Fc.nbr_injective (h.trans hFc_2.symm); rw [this]; norm_num
    · intro hlt
      have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ := by
        have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
        rcases this with h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
      rcases this with rfl | rfl | rfl
      · exact hFc_0.symm ▸ hc1_u
      · exact hFc_1.symm ▸ hc2_u
      · exact hFc_2.symm ▸ hc3_u
  -- Qualifying sites: c, c₁, c₃, c₆, c₇!
  have hqual_c : IsQualifying c₀ s c c := ⟨Finset.mem_insert_self c s, by rwa [Finset.erase_insert hcs]⟩
  have hqual_c1 : IsQualifying c₀ s c c₁ := by
    refine ⟨Finset.mem_insert_of_mem hc1_s, ?_⟩
    have herase : (insert c s).erase c₁ = insert c (s.erase c₁) := Finset.erase_insert_of_ne hdistinct.1.1
    rw [herase]
    apply lem_4_3_join_le_two c₀ hc₀ hPack hFrame hCover hTriv (s.erase c₁) c
      (hbridge.2.2.2.1 s _ hs (Finset.erase_subset _ _)) hc (fun h => hcs (Finset.mem_of_mem_erase h)) Fc
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc.nbr j ∈ UnfixedSites c₀ (insert c (s.erase c₁))) ⊆
        ({⟨1, by norm_num⟩, ⟨2, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      have hjU_big : Fc.nbr j ∈ UnfixedSites c₀ (insert c s) := by
        rcases hjU with h | h
        · left; rw [← herase] at h; exact Finset.mem_of_mem_erase h
        · exact Or.inr h
      have hlt := (hprof_c j).mp hjU_big
      have hj0 : j ≠ ⟨0, by norm_num⟩ := by
        intro heq; subst heq; change Fc.nbr 0 ∈ _ at hjU; rw [hFc_0] at hjU
        rcases hjU with h | h
        · rw [← herase] at h; exact Finset.notMem_erase c₁ _ h
        · exact (hs.1 hc1_s).2 h
      have : j.1 = 1 ∨ j.1 = 2 := by have : j.1 ≠ 0 := fun h => hj0 (Fin.ext h); omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h | h <;> [left; right] <;> exact Fin.ext h
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  have hqual_c3 : IsQualifying c₀ s c c₃ := by
    refine ⟨Finset.mem_insert_of_mem hc3_s, ?_⟩
    have herase : (insert c s).erase c₃ = insert c (s.erase c₃) := Finset.erase_insert_of_ne hdistinct.1.2.2.1
    rw [herase]
    apply lem_4_3_join_le_two c₀ hc₀ hPack hFrame hCover hTriv (s.erase c₃) c
      (hbridge.2.2.2.1 s _ hs (Finset.erase_subset _ _)) hc (fun h => hcs (Finset.mem_of_mem_erase h)) Fc
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc.nbr j ∈ UnfixedSites c₀ (insert c (s.erase c₃))) ⊆
        ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      have hjU_big : Fc.nbr j ∈ UnfixedSites c₀ (insert c s) := by
        rcases hjU with h | h
        · left; rw [← herase] at h; exact Finset.mem_of_mem_erase h
        · exact Or.inr h
      have hlt := (hprof_c j).mp hjU_big
      have hj2 : j ≠ ⟨2, by norm_num⟩ := by
        intro heq; subst heq; change Fc.nbr 2 ∈ _ at hjU; rw [hFc_2] at hjU
        rcases hjU with h | h
        · rw [← herase] at h; exact Finset.notMem_erase c₃ _ h
        · exact (hs.1 hc3_s).2 h
      have : j.1 = 0 ∨ j.1 = 1 := by have : j.1 ≠ 2 := fun h => hj2 (Fin.ext h); omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h | h <;> [left; right] <;> exact Fin.ext h
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  -- Helper: joining c to any subset t ⊆ s containing c₁, c₃ with c₆ ∉ t and c₂ unfixed succeeds by Lemma 4.4!
  have hjoin_without_c6 : ∀ t : Finset H2, t ⊆ s → c₁ ∈ t → c₃ ∈ t → c₆ ∉ t →
      c₂ ∈ UnfixedSites c₀ (insert c t) → CanJoin c₀ t c := by
    intro t ht hc1t hc3t hc6nt hc2_ut
    have ht_good : IsGood c₀ t := hbridge.2.2.2.1 s t hs ht
    have hcnt : c ∉ t := fun h => hcs (ht h)
    have hsub_u : UnfixedSites c₀ (insert c t) ⊆ UnfixedSites c₀ (insert c s) := by
      intro x hx
      rcases hx with h | h
      · left; rcases Finset.mem_insert.mp h with rfl | hxt
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ht hxt)
      · exact Or.inr h
    have hprof_ct : HasProfile sites37 (UnfixedSites c₀ (insert c t)) c 3 Fc := by
      intro j
      constructor
      · intro hj; exact (hprof_c j).mp (hsub_u hj)
      · intro hlt
        have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ := by
          have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
          rcases this with h | h | h <;> [left; (right; left); (right; right)] <;> exact Fin.ext h
        rcases this with rfl | rfl | rfl
        · exact hFc_0.symm ▸ Or.inl (Finset.mem_insert_of_mem hc1t)
        · exact hFc_1.symm ▸ hc2_ut
        · exact hFc_2.symm ▸ Or.inl (Finset.mem_insert_of_mem hc3t)
    apply lem_4_4_join_tau3 c₀ hc₀ hPack hFrame hCover hTriv t c c₁ c₂ c₃ c₄ c₅
      ht_good hc hcnt Fc hprof_ct hFc_0 hFc_1 hFc_2 hc1t hc3t
      hadj_c4c1 (hadj_symm _ _ hadj_c2c4) (Ne.symm hdistinct.1.2.2.2.1)
      (hadj_symm _ _ hadj_c2c5) (hadj_symm _ _ hadj_c3c5) (Ne.symm hdistinct.1.2.2.2.2.1)
    · intro w hw hadj hwU; exact hu1 w hw hadj (hsub_u hwU)
    · intro w hw hadj hwU
      rcases hu3 w hw hadj (hsub_u hwU) with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exfalso
        rcases hwU with hw_in | hw_c0
        · rcases Finset.mem_insert.mp hw_in with h | h
          · exact hdistinct.1.2.2.2.2.2.1 h.symm
          · exact hc6nt h
        · exact (hs.1 hc6_s).2 hw_c0
  -- c₆ qualifies!
  have hqual_c6 : IsQualifying c₀ s c c₆ := by
    refine ⟨Finset.mem_insert_of_mem hc6_s, ?_⟩
    have herase : (insert c s).erase c₆ = insert c (s.erase c₆) :=
      Finset.erase_insert_of_ne hdistinct.1.2.2.2.2.2.1
    rw [herase]
    apply hjoin_without_c6 (s.erase c₆) (Finset.erase_subset _ _)
      (Finset.mem_erase.mpr ⟨hdistinct.2.1.2.2.2.2.1, hc1_s⟩)
      (Finset.mem_erase.mpr ⟨hdistinct.2.2.2.1.2.2.1, hc3_s⟩)
      (Finset.notMem_erase _ _)
    rcases hc2_u with h | h
    · left; rw [← herase]; exact Finset.mem_erase.mpr ⟨hdistinct.2.2.1.2.2.2.1, h⟩
    · exact Or.inr h
  -- c₇ qualifies: first join c to (s.erase c₆).erase c₇ by Lemma 4.4, then join c₆ by Lemma 4.3!
  have hqual_c7 : IsQualifying c₀ s c c₇ := by
    refine ⟨Finset.mem_insert_of_mem hc7_s, ?_⟩
    set t := (s.erase c₆).erase c₇
    have ht_good : IsGood c₀ (insert c t) := by
      apply hjoin_without_c6 t (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
        (Finset.mem_erase.mpr ⟨hdistinct.2.1.2.2.2.2.2.1, Finset.mem_erase.mpr ⟨hdistinct.2.1.2.2.2.2.1, hc1_s⟩⟩)
        (Finset.mem_erase.mpr ⟨hdistinct.2.2.2.1.2.2.2.1, Finset.mem_erase.mpr ⟨hdistinct.2.2.2.1.2.2.1, hc3_s⟩⟩)
        (fun h => Finset.notMem_erase c₆ s (Finset.mem_of_mem_erase h))
      rcases hc2_u with h | h
      · left; rcases Finset.mem_insert.mp h with hcc2 | hc2s
        · exact absurd hcc2 (Ne.symm hdistinct.1.2.1)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hdistinct.2.2.1.2.2.2.2.1,
            Finset.mem_erase.mpr ⟨hdistinct.2.2.1.2.2.2.1, hc2s⟩⟩)
      · exact Or.inr h
    have heq_set : (insert c s).erase c₇ = insert c₆ (insert c t) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, t]
      constructor
      · rintro ⟨hx7, rfl | hxs⟩
        · exact Or.inr (Or.inl rfl)
        · by_cases hx6 : x = c₆
          · exact Or.inl hx6
          · exact Or.inr (Or.inr ⟨hx7, hx6, hxs⟩)
      · rintro (rfl | rfl | ⟨hx7, _, hxs⟩)
        · exact ⟨hdistinct.2.2.2.2.2.2.1.1, Or.inr hc6_s⟩
        · exact ⟨hdistinct.1.2.2.2.2.2.2.1, Or.inl rfl⟩
        · exact ⟨hx7, Or.inr hxs⟩
    rw [heq_set]
    apply lem_4_3_join_le_two c₀ hc₀ hPack hFrame hCover hTriv (insert c t) c₆ ht_good (hs.1 hc6_s)
      (by simp only [Finset.mem_insert, t, Finset.mem_erase, not_or]; exact ⟨Ne.symm hdistinct.1.2.2.2.2.2.1, fun h => h.2.1 rfl⟩)
      Fc6
    have hsub2 : Finset.univ.filter (fun j : Fin 7 => Fc6.nbr j ∈ UnfixedSites c₀ (insert c₆ (insert c t))) ⊆
        ({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset (Fin 7)) := by
      intro j hj
      have hjU := (Finset.mem_filter.mp hj).2
      rw [← heq_set] at hjU
      have hjU_big : Fc6.nbr j ∈ UnfixedSites c₀ (insert c s) := by
        rcases hjU with h | h
        · left; exact Finset.mem_of_mem_erase h
        · exact Or.inr h
      rcases hu6 (Fc6.nbr j) (Fc6.nbr_mem j) (Fc6.adj_self_nbr j) hjU_big with h3 | h5 | h7
      · have : j = ⟨0, by norm_num⟩ := Fc6.nbr_injective (h3.trans hFc6_0.symm)
        simp [this]
      · have : j = ⟨1, by norm_num⟩ := Fc6.nbr_injective (h5.trans hFc6_1.symm)
        simp [this]
      · exfalso
        rw [h7] at hjU
        rcases hjU with h | h
        · exact Finset.notMem_erase c₇ _ h
        · exact (hs.1 hc7_s).2 h
    exact le_trans (Finset.card_le_card hsub2) (by decide)
  -- Establish full profiles: τ₃ at c₁, c₆, c₇, and τ₄ at c₃!
  have hprof_c1 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₁ 3 Fc1 := by
    obtain ⟨hge2, hnotX⟩ := hbridge.2.2.2.2 s c c₁ hs hc hcs hncj hqual_c1 X hX hnt
    apply hasProfile3_of_subset_three_and_two_overlappers c₀ (insert c s) X hX Fc1 hnotX hge2 _
      (hFc1_1.symm ▸ hc2_u) (hFc1_2.symm ▸ hc_u)
    intro j hjU
    rcases hu1 (Fc1.nbr j) (Fc1.nbr_mem j) (Fc1.adj_self_nbr j) hjU with h | h | h
    · have : j = ⟨0, by norm_num⟩ := Fc1.nbr_injective (h.trans hFc1_0.symm); rw [this]; norm_num
    · have : j = ⟨1, by norm_num⟩ := Fc1.nbr_injective (h.trans hFc1_1.symm); rw [this]; norm_num
    · have : j = ⟨2, by norm_num⟩ := Fc1.nbr_injective (h.trans hFc1_2.symm); rw [this]; norm_num
  have hprof_c6 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₆ 3 Fc6 := by
    intro j
    constructor
    · intro hjU
      rcases hu6 (Fc6.nbr j) (Fc6.nbr_mem j) (Fc6.adj_self_nbr j) hjU with h | h | h
      · have : j = ⟨0, by norm_num⟩ := Fc6.nbr_injective (h.trans hFc6_0.symm); rw [this]; norm_num
      · have : j = ⟨1, by norm_num⟩ := Fc6.nbr_injective (h.trans hFc6_1.symm); rw [this]; norm_num
      · have : j = ⟨2, by norm_num⟩ := Fc6.nbr_injective (h.trans hFc6_2.symm); rw [this]; norm_num
    · intro hlt
      have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ := by
        have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
        rcases this with h | h | h <;> [left; (right; left); (right; right)] <;> exact Fin.ext h
      rcases this with rfl | rfl | rfl
      · exact hFc6_0.symm ▸ hc3_u
      · exact hFc6_1.symm ▸ hc5_u
      · exact hFc6_2.symm ▸ hc7_u
  have hprof_c7 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₇ 3 Fc7 := by
    obtain ⟨hge2, hnotX⟩ := hbridge.2.2.2.2 s c c₇ hs hc hcs hncj hqual_c7 X hX hnt
    apply hasProfile3_of_subset_three_and_two_overlappers c₀ (insert c s) X hX Fc7 hnotX hge2 _
      (hFc7_1.symm ▸ hc5_u) (hFc7_2.symm ▸ hc6_u)
    intro j hjU
    rcases hu7 (Fc7.nbr j) (Fc7.nbr_mem j) (Fc7.adj_self_nbr j) hjU with h | h | h
    · have : j = ⟨2, by norm_num⟩ := Fc7.nbr_injective (h.trans hFc7_2.symm); rw [this]; norm_num
    · have : j = ⟨1, by norm_num⟩ := Fc7.nbr_injective (h.trans hFc7_1.symm); rw [this]; norm_num
    · have : j = ⟨0, by norm_num⟩ := Fc7.nbr_injective (h.trans hFc7_0.symm); rw [this]; norm_num
  have hprof_c3 : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c₃ 4 Fc3 := by
    intro j
    constructor
    · intro hjU
      rcases hu3 (Fc3.nbr j) (Fc3.nbr_mem j) (Fc3.adj_self_nbr j) hjU with h | h | h | h
      · have : j = ⟨0, by norm_num⟩ := Fc3.nbr_injective (h.trans hFc3_0.symm); rw [this]; norm_num
      · have : j = ⟨1, by norm_num⟩ := Fc3.nbr_injective (h.trans hFc3_1.symm); rw [this]; norm_num
      · have : j = ⟨2, by norm_num⟩ := Fc3.nbr_injective (h.trans hFc3_2.symm); rw [this]; norm_num
      · have : j = ⟨3, by norm_num⟩ := Fc3.nbr_injective (h.trans hFc3_3.symm); rw [this]; norm_num
    · intro hlt
      have : j = ⟨0, by norm_num⟩ ∨ j = ⟨1, by norm_num⟩ ∨ j = ⟨2, by norm_num⟩ ∨ j = ⟨3, by norm_num⟩ := by
        have : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3 := by omega
        rcases this with h | h | h | h <;>
          [left; (right; left); (right; right; left); (right; right; right)] <;> exact Fin.ext h
      rcases this with rfl | rfl | rfl | rfl
      · exact hFc3_0.symm ▸ hc_u
      · exact hFc3_1.symm ▸ hc2_u
      · exact hFc3_2.symm ▸ hc5_u
      · exact hFc3_3.symm ▸ hc6_u
  -- Step 1 (Edge counts)
  obtain ⟨Y₁, hY1X, Z, hZX, W, hWX, E, hEX, V₁, hV1X, V₂, hV2X,
      hZW_ne, hY1Z_ne, hEV1_ne, hV2V1_ne, hc_ov, hc1_ov, hc6_ov, hc7_ov,
      hY1_c4, _, hZ_c1, hZ_nc3, hZ_nc4, hW_c3, _,
      hE_c3, _, hV1_c7, hV1_nc3, hV1_nc8, hV2_c8, _⟩ :=
    lem_4_5_step1_edge_counts c₀ hc₀ hPack hFrame hCover hTriv s c c₁ c₃ c₄ c₆ c₇ c₈
      hs hc hcs hqual_c hqual_c1 hqual_c6 hqual_c7
      Fc hFc_0 hFc_2 hprof_c Fc1 hFc1_0 hFc1_2 hprof_c1
      Fc6 hFc6_0 hFc6_2 hprof_c6 Fc7 hFc7_0 hFc7_2 hprof_c7 X hX hnt
  have hZ_c : Overlaps r7 Z c := (hc_ov Z hZX).mpr (Or.inl rfl)
  have hW_c : Overlaps r7 W c := (hc_ov W hWX).mpr (Or.inr rfl)
  have hY1_c1 : Overlaps r7 Y₁ c₁ := (hc1_ov Y₁ hY1X).mpr (Or.inl rfl)
  have hE_c6 : Overlaps r7 E c₆ := (hc6_ov E hEX).mpr (Or.inl rfl)
  have hV1_c6 : Overlaps r7 V₁ c₆ := (hc6_ov V₁ hV1X).mpr (Or.inr rfl)
  have hV2_c7 : Overlaps r7 V₂ c₇ := (hc7_ov V₂ hV2X).mpr (Or.inl rfl)
  -- Local packing / admissibility / non-membership of qualifying sites
  have hpackX : IsPacking r7 (X : Set H2) := fun a ha b hb hab =>
    hX.2.2.2 a (Or.inr ha) b (Or.inr hb) hab
  have hadmX : ∀ P ∈ X, IsAdmissible r7 (sites37 \ UnfixedSites c₀ (insert c s)) P :=
    fun P hP => isAdmissible_of_mem_rearrangement c₀ (insert c s) X hX hP
  have hc_notX : c ∉ X := (hbridge.2.2.2.2 s c c hs hc hcs hncj hqual_c X hX hnt).2
  have hc1_notX : c₁ ∉ X := (hbridge.2.2.2.2 s c c₁ hs hc hcs hncj hqual_c1 X hX hnt).2
  have hc3_notX : c₃ ∉ X := (hbridge.2.2.2.2 s c c₃ hs hc hcs hncj hqual_c3 X hX hnt).2
  have hc6_notX : c₆ ∉ X := (hbridge.2.2.2.2 s c c₆ hs hc hcs hncj hqual_c6 X hX hnt).2
  have hc7_notX : c₇ ∉ X := (hbridge.2.2.2.2 s c c₇ hs hc hcs hncj hqual_c7 X hX hnt).2
  -- Step 2: W overlaps c₅
  have hW_c5 : Overlaps r7 W c₅ :=
    lem_4_5_step2_W_overlaps_c5 (UnfixedSites c₀ (insert c s)) c c₁ c₂ c₃ c₄ c₅ c₆
      Fc1 hFc1_0 hFc1_1 hFc1_2 hprof_c1 Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3
      X hpackX hadmX hc1_notX hc3_notX Y₁ Z W hY1X hZX hWX hZW_ne hY1Z_ne
      hY1_c1 hY1_c4 hZ_c1 hZ_c hZ_nc4 hW_c3
  -- Step 3: E overlaps c₂
  have hE_c2 : Overlaps r7 E c₂ :=
    lem_4_5_step3_E_overlaps_c2 (UnfixedSites c₀ (insert c s)) c c₂ c₃ c₅ c₆ c₇ c₈
      Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3 Fc7 hFc7_0 hFc7_1 hFc7_2 hprof_c7
      X hpackX hadmX hc3_notX hc7_notX E V₁ V₂ hEX hV1X hV2X hEV1_ne hV2V1_ne
      hE_c3 hV1_c7 hV1_c6 hV1_nc8 hV2_c7 hV2_c8
  -- Step 4: W = E
  obtain ⟨hWE_eq, hW_c2⟩ :=
    lem_4_5_step4_W_eq_E (UnfixedSites c₀ (insert c s)) c c₂ c₃ c₅ c₆
      hadj_c2c3 hadj_c3c5 (hadj_symm _ _ hadj_c2c5)
      Fc hFc_1 hprof_c Fc6 hFc6_1 hprof_c6
      X hpackX hadmX hc_notX hc6_notX W E hWX hEX hW_c hW_c3 hW_c5 hE_c6 hE_c3 hE_c2
  subst hWE_eq
  -- Step 5: Contradiction at c₃
  obtain ⟨hge2_3, _⟩ := hbridge.2.2.2.2 s c c₃ hs hc hcs hncj hqual_c3 X hX hnt
  obtain ⟨G, hGX, hGc3, hGW_ne⟩ : ∃ G ∈ X, Overlaps r7 G c₃ ∧ G ≠ W := by
    obtain ⟨A, hAf, B, hBf, hAB⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (X.filter (fun p => Overlaps r7 p c₃)).card)
    by_cases hAW : A = W
    · subst hAW; exact ⟨B, (Finset.mem_filter.mp hBf).1, (Finset.mem_filter.mp hBf).2, hAB.symm⟩
    · exact ⟨A, (Finset.mem_filter.mp hAf).1, (Finset.mem_filter.mp hAf).2, hAW⟩
  have hGn_c : ¬ Overlaps r7 G c := by
    intro hGc
    rcases (hc_ov G hGX).mp hGc with rfl | rfl
    · exact hZ_nc3 hGc3
    · exact hGW_ne rfl
  have hGn_c6 : ¬ Overlaps r7 G c₆ := by
    intro hGc6
    rcases (hc6_ov G hGX).mp hGc6 with rfl | rfl
    · exact hGW_ne rfl
    · exact hV1_nc3 hGc3
  exact lem_4_5_step5_contradiction_at_c3 (UnfixedSites c₀ (insert c s)) c c₂ c₃ c₅ c₆
    hadj_c2c3 hadj_c3c5 (hadj_symm _ _ hadj_c2c5)
    Fc3 hFc3_0 hFc3_1 hFc3_2 hFc3_3 hprof_c3
    X hpackX hadmX hc3_notX W G hWX hGX hGW_ne hW_c2 hW_c3 hW_c5 hGc3 hGn_c hGn_c6

end FejesTothP7.Proofs
