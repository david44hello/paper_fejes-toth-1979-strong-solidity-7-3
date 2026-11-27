module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Proofs.TilingMain
public import FejesTothP7.Proofs.Joining
public import FejesTothP7.Proofs.CorollaryOrder

@[expose] public section

/-!
# Proof of Theorem 1.1 (Strong Solidity of `{7, 3}`) and Corollary 1.2

Assembles the global `{3, 7}` tiling certification (`TilingMain`), the local joining lemmas
(`Joining`), and the zone substitution word invariants (`ZoneWords`) to prove:
1. `thm_1_1_step_zone1`: `U₁ = Z₁` is finite and good.
2. `thm_1_1_step_zone2`: `U₂ = Z₁ ∪ Z₂` is finite and good.
3. `thm_1_1_step_zone_m`: `U_m` is finite and good for every `m ≥ 1`.
4. `thm_1_1_strong_solidity`: `IsStronglySolid r7 sites37`.
5. `cor_1_2_grade_and_order`: `HasGradeOfSaturatedness r7 sites37 3 ∧ HasOrderOfSolidity r7 sites37 1`.
-/

noncomputable section
open Classical

namespace FejesTothP7.Proofs

open FejesTothP7.H2

lemma adj37_symm {u v : H2} (h : Adj37 u v) : Adj37 v u := by
  unfold Adj37 at *; rwa [dist_comm]

/-! ### Section 1: Global-instantiated joining wrappers -/

private lemma hFrame_sites37 : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v) :=
  fun _ hv => ⟨(exists_direct_siteFrame_sites37 hv).choose⟩

lemma j_singleton (c₀ : H2) (hc₀ : c₀ ∈ sites37) {c : H2} (hc : c ∈ oneVacancy c₀) :
    IsGood c₀ {c} :=
  (lem_4_1_bridge c₀ hc₀ isPacking_sites37 hFrame_sites37 covering_radius_Rc7
    (lem_2_1_trivial_rearrangement c₀ hc₀)).2.1 c hc

lemma j_subset (c₀ : H2) (hc₀ : c₀ ∈ sites37) {s s' : Finset H2}
    (hs : IsGood c₀ s) (hsub : s' ⊆ s) : IsGood c₀ s' :=
  (lem_4_1_bridge c₀ hc₀ isPacking_sites37 hFrame_sites37 covering_radius_Rc7
    (lem_2_1_trivial_rearrangement c₀ hc₀)).2.2.2.1 s s' hs hsub

lemma j_le_two (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c : H2) (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (F : SiteFrame sites37 c)
    (hle2 : (Finset.univ.filter (fun j : Fin 7 => F.nbr j ∈ UnfixedSites c₀ (insert c s))).card ≤ 2) :
    CanJoin c₀ s c :=
  lem_4_3_join_le_two c₀ hc₀ isPacking_sites37 hFrame_sites37 covering_radius_Rc7
    (lem_2_1_trivial_rearrangement c₀ hc₀) s c hs hc hcs F hle2

lemma j_tau3 (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s : Finset H2) (c c₁ c₂ c₃ c₄ c₅ : H2)
    (hs : IsGood c₀ s) (hc : c ∈ oneVacancy c₀) (hcs : c ∉ s)
    (Fc : SiteFrame sites37 c)
    (hprof_c : HasProfile sites37 (UnfixedSites c₀ (insert c s)) c 3 Fc)
    (hc1_eq : Fc.nbr 0 = c₁) (hc2_eq : Fc.nbr 1 = c₂) (hc3_eq : Fc.nbr 2 = c₃)
    (hc1_s : c₁ ∈ s) (hc3_s : c₃ ∈ s)
    (hc4_adj1 : Adj37 c₄ c₁) (hc4_adj2 : Adj37 c₄ c₂) (hc4_ne : c₄ ≠ c)
    (hc5_adj2 : Adj37 c₅ c₂) (hc5_adj3 : Adj37 c₅ c₃) (hc5_ne : c₅ ≠ c)
    (hu1 : ∀ w ∈ sites37, Adj37 c₁ w → w ∈ UnfixedSites c₀ (insert c s) → w = c₄ ∨ w = c₂ ∨ w = c)
    (hu3 : ∀ w ∈ sites37, Adj37 c₃ w → w ∈ UnfixedSites c₀ (insert c s) → w = c ∨ w = c₂ ∨ w = c₅) :
    CanJoin c₀ s c :=
  lem_4_4_join_tau3 c₀ hc₀ isPacking_sites37 hFrame_sites37 covering_radius_Rc7
    (lem_2_1_trivial_rearrangement c₀ hc₀) s c c₁ c₂ c₃ c₄ c₅ hs hc hcs Fc hprof_c
    hc1_eq hc2_eq hc3_eq hc1_s hc3_s hc4_adj1 hc4_adj2 hc4_ne hc5_adj2 hc5_adj3 hc5_ne hu1 hu3

lemma j_nine_site (c₀ : H2) (hc₀ : c₀ ∈ sites37)
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
    CanJoin c₀ s c :=
  lem_4_5_nine_site c₀ hc₀ isPacking_sites37 hFrame_sites37 covering_radius_Rc7
    (lem_2_1_trivial_rearrangement c₀ hc₀) s c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ hs hc hcs hdistinct
    Fc2 h2_0 h2_1 h2_2 h2_3 h2_4 Fc5 h5_0 h5_1 h5_2 h5_3 h5_4
    hc1_s hc3_s hc6_s hc7_s hc2_u hc5_u huc hu1 hu3 hu6 hu7

/-! ### Section 2: Zone-disjointness and 5-neighbor frame builder -/

lemma zone_disjoint {c₀ : sites37} {m n : ℕ} (hmn : m ≠ n) {x : H2}
    (hm : x ∈ Zone c₀ m) (hn : x ∈ Zone c₀ n) : False := by
  rcases hm with ⟨hx, hdm⟩
  rcases hn with ⟨_, hdn⟩
  have heq : (m : ENat) = (n : ENat) := hdm.symm.trans hdn
  exact hmn (Nat.cast_injective heq)

lemma zone_zero_eq (c₀ : sites37) : Zone c₀ 0 = {c₀.1} := by
  ext x
  simp only [Zone, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hed⟩
    have h0 : (⟨x, hx⟩ : sites37) = c₀ := SimpleGraph.edist_eq_zero_iff.mp hed
    exact congrArg Subtype.val h0
  · rintro rfl
    exact ⟨c₀.2, SimpleGraph.edist_self⟩

lemma zone_subset_sites37 {c₀ : sites37} {m : ℕ} {x : H2} (hx : x ∈ Zone c₀ m) : x ∈ sites37 :=
  hx.1

lemma zone_subset_oneVacancy {c₀ : sites37} {m : ℕ} (hm : 1 ≤ m) {x : H2} (hx : x ∈ Zone c₀ m) :
    x ∈ oneVacancy c₀.1 := by
  refine ⟨hx.1, ?_⟩
  intro hxc
  exact zone_disjoint (show m ≠ 0 by omega) hx (by rw [zone_zero_eq]; exact hxc)

lemma zone_not_mem_zoneUnion_of_gt {c₀ : sites37} {m n : ℕ} (hgt : n < m) {x : H2}
    (hx : x ∈ Zone c₀ m) : x ∉ ZoneUnion c₀ n := by
  intro hu
  simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hu
  rcases hu with ⟨k, ⟨_, hkn⟩, hxk⟩
  exact zone_disjoint (show m ≠ k by omega) hx hxk

lemma zone_subset_zoneUnion {c₀ : sites37} {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    Zone c₀ k ⊆ ZoneUnion c₀ m := by
  intro x hx
  simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc]
  exact ⟨k, ⟨hk, hkm⟩, hx⟩

/-- Build a `SiteFrame sites37 u` sending `0, 1, 2, 3, 4` to five consecutive neighbors `a₀..a₄`. -/
lemma build_five_nbr_frame {u a₀ a₁ a₂ a₃ a₄ : H2}
    (hu : u ∈ sites37) (ha₀ : a₀ ∈ sites37) (ha₁ : a₁ ∈ sites37) (ha₂ : a₂ ∈ sites37)
    (ha₃ : a₃ ∈ sites37) (ha₄ : a₄ ∈ sites37)
    (hu0 : Adj37 u a₀) (hu1 : Adj37 u a₁) (hu2 : Adj37 u a₂) (hu3 : Adj37 u a₃) (hu4 : Adj37 u a₄)
    (h01 : Adj37 a₀ a₁) (h12 : Adj37 a₁ a₂) (h23 : Adj37 a₂ a₃) (h34 : Adj37 a₃ a₄)
    (h20 : a₂ ≠ a₀) (h31 : a₃ ≠ a₁) (h42 : a₄ ≠ a₂) :
    ∃ F : SiteFrame sites37 u,
      F.nbr 0 = a₀ ∧ F.nbr 1 = a₁ ∧ F.nbr 2 = a₂ ∧ F.nbr 3 = a₃ ∧ F.nbr 4 = a₄ := by
  rcases exists_direct_siteFrame_sites37 hu with ⟨F0, _, _⟩
  rcases F0.align ha₀ ha₁ hu0 hu1 h01 with ⟨F, hF0, hF1⟩
  have hF2 : F.nbr 2 = a₂ := by
    have h := F.nbr_next_of_common_nbr (⟨1, by omega⟩ : Fin 7) ha₂ hu2
      (by simpa [hF1] using h12) (by simpa [hF0] using h20)
    simpa using h.symm
  have hF3 : F.nbr 3 = a₃ := by
    have h := F.nbr_next_of_common_nbr (⟨2, by omega⟩ : Fin 7) ha₃ hu3
      (by simpa [hF2] using h23) (by simpa [hF1] using h31)
    simpa using h.symm
  have hF4 : F.nbr 4 = a₄ := by
    have h := F.nbr_next_of_common_nbr (⟨3, by omega⟩ : Fin 7) ha₄ hu4
      (by simpa [hF3] using h34) (by simpa [hF2] using h42)
    simpa using h.symm
  exact ⟨F, hF0, hF1, hF2, hF3, hF4⟩

/-! ### Section 3: Pure word-combinatorics for `m ≥ 3` (`isSDS`, `isSDDS`, and arc cover) -/

/-- Periodic accessor for `zoneWord m` (`m ≥ 1`). -/
def zty (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : ZoneType :=
  (zoneWord m).get ⟨k % (zoneWord m).length, Nat.mod_lt _ (zoneWord_length_pos m hm)⟩

lemma zty_mod (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    zty m hm (k % (zoneWord m).length) = zty m hm k := by
  simp [zty]

lemma zty_add_len (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    zty m hm (k + (zoneWord m).length) = zty m hm k := by
  simp [zty]

lemma zty_no_adj_t2 {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (h : zty m (by omega) k = .t2) :
    zty m (by omega) (k + 1) = .t1 := by
  have hpa := zoneWord_part_a m hm ⟨k % (zoneWord m).length, Nat.mod_lt _ (zoneWord_length_pos m (by omega))⟩
  have h1 := hpa.1 h
  simpa [zty, Nat.mod_add_mod] using h1

lemma zty_prev_t1_of_t2 {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (h : zty m (by omega) k = .t2) :
    zty m (by omega) (k + (zoneWord m).length - 1) = .t1 := by
  cases ht : zty m (by omega) (k + (zoneWord m).length - 1)
  · rfl
  · have h1 := zty_no_adj_t2 hm (k + (zoneWord m).length - 1) ht
    have hpos := zoneWord_length_pos m (by omega)
    have heq : k + (zoneWord m).length - 1 + 1 = k + (zoneWord m).length := by omega
    rw [heq, zty_add_len] at h1
    rw [h] at h1; cases h1

lemma zty_no_triple_t1 {m : ℕ} (hm : 2 ≤ m) (k : ℕ)
    (h0 : zty m (by omega) k = .t1) (h1 : zty m (by omega) (k + 1) = .t1) :
    zty m (by omega) (k + 2) = .t2 := by
  have hpa := zoneWord_part_a m hm ⟨k % (zoneWord m).length, Nat.mod_lt _ (zoneWord_length_pos m (by omega))⟩
  have h2 := hpa.2 h0 (by simpa [zty, Nat.mod_add_mod] using h1)
  simpa [zty, Nat.mod_add_mod] using h2

lemma zoneWord_length_ge_56 (m : ℕ) (hm : 3 ≤ m) : 56 ≤ (zoneWord m).length := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [zoneWord_succ k (by omega), sigmaWord, List.length_flatMap]
    have hsum : ∀ l : List ZoneType, l.length ≤ (l.map (fun t => (sigmaStep t).length)).sum := by
      intro l; induction l with
      | nil => simp
      | cons a tl iht =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := sigmaStep_length a; omega
    exact le_trans ih (hsum _)

/-- `isSDS m hm k`: `k` is the left single `S₁` of an `S-D-S` arc (`t2 [S₁] t2 d₁ d₂ t2 S₂ t2`). -/
def isSDS (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : Bool :=
  let N := (zoneWord m).length
  (zty m hm (k + N - 1) == .t2) && (zty m hm k == .t1) &&
  (zty m hm (k + 1) == .t2) && (zty m hm (k + 2) == .t1) &&
  (zty m hm (k + 3) == .t1) && (zty m hm (k + 4) == .t2) &&
  (zty m hm (k + 5) == .t1) && (zty m hm (k + 6) == .t2)

/-- `isSDDS m hm k`: `k` is the left single `S₁` of an `S-D-D-S` arc (`t2 [S₁] t2 d₁ d₂ t2 d₃ d₄ t2 S₂ t2`). -/
def isSDDS (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : Bool :=
  let N := (zoneWord m).length
  (zty m hm (k + N - 1) == .t2) && (zty m hm k == .t1) &&
  (zty m hm (k + 1) == .t2) && (zty m hm (k + 2) == .t1) &&
  (zty m hm (k + 3) == .t1) && (zty m hm (k + 4) == .t2) &&
  (zty m hm (k + 5) == .t1) && (zty m hm (k + 6) == .t1) &&
  (zty m hm (k + 7) == .t2) && (zty m hm (k + 8) == .t1) &&
  (zty m hm (k + 9) == .t2)

lemma isSDS_mod (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    isSDS m hm (k % (zoneWord m).length) = isSDS m hm k := by
  unfold isSDS; dsimp only
  have hpos := zoneWord_length_pos m hm
  have hN : (k % (zoneWord m).length + (zoneWord m).length - 1) % (zoneWord m).length =
      (k + (zoneWord m).length - 1) % (zoneWord m).length := by
    have hlt := Nat.mod_lt k hpos
    have h1 : k % (zoneWord m).length + (zoneWord m).length - 1 =
        (k % (zoneWord m).length) + ((zoneWord m).length - 1) := by omega
    have h2 : k + (zoneWord m).length - 1 = k + ((zoneWord m).length - 1) := by omega
    rw [h1, h2, Nat.mod_add_mod]
  have hzty_sub : zty m hm (k % (zoneWord m).length + (zoneWord m).length - 1) =
      zty m hm (k + (zoneWord m).length - 1) := by
    unfold zty; congr 1; exact Fin.ext hN
  have hzty_add : ∀ d, zty m hm (k % (zoneWord m).length + d) = zty m hm (k + d) := by
    intro d; unfold zty; simp [Nat.mod_add_mod]
  rw [hzty_sub, zty_mod, hzty_add 1, hzty_add 2, hzty_add 3, hzty_add 4, hzty_add 5, hzty_add 6]

lemma isSDDS_mod (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    isSDDS m hm (k % (zoneWord m).length) = isSDDS m hm k := by
  unfold isSDDS; dsimp only
  have hpos := zoneWord_length_pos m hm
  have hN : (k % (zoneWord m).length + (zoneWord m).length - 1) % (zoneWord m).length =
      (k + (zoneWord m).length - 1) % (zoneWord m).length := by
    have hlt := Nat.mod_lt k hpos
    have h1 : k % (zoneWord m).length + (zoneWord m).length - 1 =
        (k % (zoneWord m).length) + ((zoneWord m).length - 1) := by omega
    have h2 : k + (zoneWord m).length - 1 = k + ((zoneWord m).length - 1) := by omega
    rw [h1, h2, Nat.mod_add_mod]
  have hzty_sub : zty m hm (k % (zoneWord m).length + (zoneWord m).length - 1) =
      zty m hm (k + (zoneWord m).length - 1) := by
    unfold zty; congr 1; exact Fin.ext hN
  have hzty_add : ∀ d, zty m hm (k % (zoneWord m).length + d) = zty m hm (k + d) := by
    intro d; unfold zty; simp [Nat.mod_add_mod]
  rw [hzty_sub, zty_mod, hzty_add 1, hzty_add 2, hzty_add 3, hzty_add 4, hzty_add 5, hzty_add 6,
    hzty_add 7, hzty_add 8, hzty_add 9]

lemma isSDS_three_false (k : ℕ) : isSDS 3 (by omega) k = false := by
  rw [← isSDS_mod]
  have hfin : ∀ i : Fin (zoneWord 3).length, isSDS 3 (by omega) i.1 = false := by decide
  exact hfin ⟨k % (zoneWord 3).length, Nat.mod_lt _ (zoneWord_length_pos 3 (by omega))⟩

lemma isSDS_spec {m : ℕ} {hm : 1 ≤ m} {k : ℕ} (h : isSDS m hm k = true) :
    zty m hm (k + (zoneWord m).length - 1) = .t2 ∧
    zty m hm k = .t1 ∧ zty m hm (k + 1) = .t2 ∧ zty m hm (k + 2) = .t1 ∧
    zty m hm (k + 3) = .t1 ∧ zty m hm (k + 4) = .t2 ∧ zty m hm (k + 5) = .t1 ∧
    zty m hm (k + 6) = .t2 := by
  unfold isSDS at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma isSDDS_spec {m : ℕ} {hm : 1 ≤ m} {k : ℕ} (h : isSDDS m hm k = true) :
    zty m hm (k + (zoneWord m).length - 1) = .t2 ∧
    zty m hm k = .t1 ∧ zty m hm (k + 1) = .t2 ∧ zty m hm (k + 2) = .t1 ∧
    zty m hm (k + 3) = .t1 ∧ zty m hm (k + 4) = .t2 ∧ zty m hm (k + 5) = .t1 ∧
    zty m hm (k + 6) = .t1 ∧ zty m hm (k + 7) = .t2 ∧ zty m hm (k + 8) = .t1 ∧
    zty m hm (k + 9) = .t2 := by
  unfold isSDDS at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    h.1.1.2, h.1.2, h.2⟩

lemma isSDS_next_six {m : ℕ} (hm : 3 ≤ m) {k : ℕ} (h : isSDS m (by omega) k = true) :
    zty m (by omega) (k + 7) = .t1 ∧ zty m (by omega) (k + 8) = .t1 ∧
    zty m (by omega) (k + 9) = .t2 ∧ zty m (by omega) (k + 10) = .t1 ∧
    zty m (by omega) (k + 11) = .t1 ∧ zty m (by omega) (k + 12) = .t2 := by
  by_cases hm3 : m = 3
  · subst hm3; rw [isSDS_three_false] at h; cases h
  · have hm4 : 4 ≤ m := by omega
    have hs := isSDS_spec h
    have hpos := zoneWord_length_pos m (by omega)
    let kf : Fin (zoneWord m).length := ⟨k % (zoneWord m).length, Nat.mod_lt _ hpos⟩
    have hsub : (kf.1 + (zoneWord m).length - 1) % (zoneWord m).length =
        (k + (zoneWord m).length - 1) % (zoneWord m).length := by
      have hlt := Nat.mod_lt k hpos
      have h1 : k % (zoneWord m).length + (zoneWord m).length - 1 =
          k % (zoneWord m).length + ((zoneWord m).length - 1) := by omega
      have h2 : k + (zoneWord m).length - 1 = k + ((zoneWord m).length - 1) := by omega
      dsimp only [kf]; rw [h1, h2, Nat.mod_add_mod]
    have hfin_sub : (⟨(kf.1 + (zoneWord m).length - 1) % (zoneWord m).length, Nat.mod_lt _ hpos⟩ :
        Fin (zoneWord m).length) =
        ⟨(k + (zoneWord m).length - 1) % (zoneWord m).length, Nat.mod_lt _ hpos⟩ := Fin.ext hsub
    have hpc := zoneWord_part_c m hm4 kf
      (by convert hs.1 using 1; exact congrArg (zoneWord m).get hfin_sub)
      (by simpa [zty, kf] using hs.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.2.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.2.2.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.2.2.2.2.1)
      (by simpa [zty, kf, Nat.mod_add_mod] using hs.2.2.2.2.2.2.2)
    simpa [zty, kf, Nat.mod_add_mod] using hpc

/-- Helper: cyclic equality `a % N = b % N` implies `zty (a + d) = zty (b + d)`. -/
lemma zty_congr_add {m : ℕ} {hm : 1 ≤ m} {a b : ℕ} (hab : a % (zoneWord m).length = b % (zoneWord m).length)
    (d : ℕ) : zty m hm (a + d) = zty m hm (b + d) := by
  unfold zty
  congr 1; apply Fin.ext; dsimp only; rw [Nat.add_mod, hab, ← Nat.add_mod]

/-- For `m ≥ 3`, NO `SDS` arc's interior/endpoint `{a, a+2, a+3, a+5}` can hit `k+7`, `k-2`, or
    overlap another distinct `SDS` arc's `{k, k+2, k+3, k+5}`! -/
lemma isSDS_disjointness {m : ℕ} (hm : 3 ≤ m) {k a : ℕ}
    (hk : isSDS m (by omega) k = true) (ha : isSDS m (by omega) a = true) :
    let N := (zoneWord m).length
    ((k + 7) % N ≠ a % N ∧ (k + 7) % N ≠ (a + 2) % N ∧ (k + 7) % N ≠ (a + 3) % N ∧ (k + 7) % N ≠ (a + 5) % N) ∧
    ((k + N - 2) % N ≠ a % N ∧ (k + N - 2) % N ≠ (a + 2) % N ∧ (k + N - 2) % N ≠ (a + 3) % N ∧ (k + N - 2) % N ≠ (a + 5) % N) ∧
    (k % N ≠ a % N →
      k % N ≠ (a + 2) % N ∧ k % N ≠ (a + 3) % N ∧ k % N ≠ (a + 5) % N ∧
      (k + 2) % N ≠ a % N ∧ (k + 2) % N ≠ (a + 2) % N ∧ (k + 2) % N ≠ (a + 3) % N ∧ (k + 2) % N ≠ (a + 5) % N ∧
      (k + 3) % N ≠ a % N ∧ (k + 3) % N ≠ (a + 2) % N ∧ (k + 3) % N ≠ (a + 3) % N ∧ (k + 3) % N ≠ (a + 5) % N ∧
      (k + 5) % N ≠ a % N ∧ (k + 5) % N ≠ (a + 2) % N ∧ (k + 5) % N ≠ (a + 3) % N ∧ (k + 5) % N ≠ (a + 5) % N) := by
  have hsk := isSDS_spec hk
  have hsa := isSDS_spec ha
  have hnk := isSDS_next_six hm hk
  have hna := isSDS_next_six hm ha
  have hN := zoneWord_length_ge_56 m hm
  set N := (zoneWord m).length
  have hkm1 : (k + N - 2 + 1) % N = (k + N - 1) % N := by congr 1; omega
  have hkm0 : (k + N - 2 + 2) % N = k % N := by
    have : k + N - 2 + 2 = k + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm3 : (k + N - 2 + 3) % N = (k + 1) % N := by
    have : k + N - 2 + 3 = (k + 1) + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm4 : (k + N - 2 + 4) % N = (k + 2) % N := by
    have : k + N - 2 + 4 = (k + 2) + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm5 : (k + N - 2 + 5) % N = (k + 3) % N := by
    have : k + N - 2 + 5 = (k + 3) + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm6 : (k + N - 2 + 6) % N = (k + 4) % N := by
    have : k + N - 2 + 6 = (k + 4) + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm7 : (k + N - 2 + 7) % N = (k + 5) % N := by
    have : k + N - 2 + 7 = (k + 5) + N := by omega
    rw [this, Nat.add_mod_right]
  have hkm8 : (k + N - 2 + 8) % N = (k + 6) % N := by
    have : k + N - 2 + 8 = (k + 6) + N := by omega
    rw [this, Nat.add_mod_right]
  have hEq : ∀ {x y : ℕ}, x % N = y % N → ∀ d, zty m (by omega) (x + d) = zty m (by omega) (y + d) :=
    fun hxy d => zty_congr_add hxy d
  have hsub_eq : ∀ {x y d : ℕ}, (x + d) % N = (y + d) % N → x % N = y % N := by
    intro x y d h
    have h1 := congrArg (fun t => (t + (N - d % N)) % N) h
    have hlt : d % N < N := Nat.mod_lt d (by omega)
    have hsimp : ∀ z, ((z + d) % N + (N - d % N)) % N = z % N := by
      intro z
      rw [Nat.mod_add_mod, show z + d + (N - d % N) = z + (d / N * N + d % N) + (N - d % N) by
        have := Nat.div_add_mod' d N; omega]
      have : z + (d / N * N + d % N) + (N - d % N) = z + (d / N + 1) * N := by
        rw [add_mul, one_mul]; omega
      rw [this, Nat.add_mul_mod_self_right]
    simpa [hsimp] using h1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- k+7 ≠ a: at +1, k+8 is t1, a+1 is t2
    intro h; have := hEq h 1; rw [hnk.2.1, hsa.2.2.1] at this; cases this
  · -- k+7 ≠ a+2: at +3, k+10 is t1, a+5 is t1; at +4, k+11 is t1, a+6 is t2!
    intro h; have := hEq h 4; rw [show k + 7 + 4 = k + 11 by omega, show a + 2 + 4 = a + 6 by omega,
      hnk.2.2.2.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
  · -- k+7 ≠ a+3: at +1, k+8 is t1, a+4 is t2
    intro h; have := hEq h 1; rw [show k + 7 + 1 = k + 8 by omega, show a + 3 + 1 = a + 4 by omega,
      hnk.2.1, hsa.2.2.2.2.2.1] at this; cases this
  · -- k+7 ≠ a+5: at +1, k+8 is t1, a+6 is t2
    intro h; have := hEq h 1; rw [show k + 7 + 1 = k + 8 by omega, show a + 5 + 1 = a + 6 by omega,
      hnk.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
  · -- k-2 ≠ a: at +3, k+1 is t2, a+3 is t1
    intro h; have := hEq h 3; rw [← zty_mod, hkm3, zty_mod, hsk.2.2.1, hsa.2.2.2.2.1] at this; cases this
  · -- k-2 ≠ a+2: at +1, k-1 is t2, a+3 is t1
    intro h; have := hEq h 1; rw [← zty_mod, hkm1, zty_mod, hsk.1, show a + 2 + 1 = a + 3 by omega,
      hsa.2.2.2.2.1] at this; cases this
  · -- k-2 ≠ a+3: at +8, k+6 is t2, a+11 is t1!
    intro h; have := hEq h 8; rw [← zty_mod, hkm8, zty_mod, hsk.2.2.2.2.2.2.2,
      show a + 3 + 8 = a + 11 by omega, hna.2.2.2.2.1] at this; cases this
  · -- k-2 ≠ a+5: at +3, k+1 is t2, a+8 is t1!
    intro h; have := hEq h 3; rw [← zty_mod, hkm3, zty_mod, hsk.2.2.1,
      show a + 5 + 3 = a + 8 by omega, hna.2.1] at this; cases this
  · intro hne
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- k ≠ a+2: at +1, k+1 is t2, a+3 is t1
      intro h; have := hEq h 1; rw [hsk.2.2.1, show a + 2 + 1 = a + 3 by omega, hsa.2.2.2.2.1] at this; cases this
    · -- k ≠ a+3: at +3, k+3 is t1, a+6 is t2
      intro h; have := hEq h 3; rw [hsk.2.2.2.2.1, show a + 3 + 3 = a + 6 by omega, hsa.2.2.2.2.2.2.2] at this; cases this
    · -- k ≠ a+5: at +3, k+3 is t1, a+8 is t1; at +6, k+6 is t2, a+11 is t1!
      intro h; have := hEq h 6; rw [hsk.2.2.2.2.2.2.2, show a + 5 + 6 = a + 11 by omega, hna.2.2.2.2.1] at this; cases this
    · -- k+2 ≠ a: at +1, k+3 is t1, a+1 is t2
      intro h; have := hEq h 1; rw [show k + 2 + 1 = k + 3 by omega, hsk.2.2.2.2.1, hsa.2.2.1] at this; cases this
    · -- k+2 ≠ a+2
      intro h; exact hne (hsub_eq h)
    · -- k+2 ≠ a+3: at +1, k+3 is t1, a+4 is t2
      intro h; have := hEq h 1; rw [show k + 2 + 1 = k + 3 by omega, show a + 3 + 1 = a + 4 by omega,
        hsk.2.2.2.2.1, hsa.2.2.2.2.2.1] at this; cases this
    · -- k+2 ≠ a+5: at +1, k+3 is t1, a+6 is t2
      intro h; have := hEq h 1; rw [show k + 2 + 1 = k + 3 by omega, show a + 5 + 1 = a + 6 by omega,
        hsk.2.2.2.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
    · -- k+3 ≠ a: at +3, k+6 is t2, a+3 is t1
      intro h; have := hEq h 3; rw [show k + 3 + 3 = k + 6 by omega, hsk.2.2.2.2.2.2.2, hsa.2.2.2.2.1] at this; cases this
    · -- k+3 ≠ a+2: at +1, k+4 is t2, a+3 is t1
      intro h; have := hEq h 1; rw [show k + 3 + 1 = k + 4 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.1, hsa.2.2.2.2.1] at this; cases this
    · -- k+3 ≠ a+3
      intro h; exact hne (hsub_eq h)
    · -- k+3 ≠ a+5: at +2, k+5 is t1, a+7 is t1; at +3, k+6 is t2, a+8 is t1!
      intro h; have := hEq h 3; rw [show k + 3 + 3 = k + 6 by omega, show a + 5 + 3 = a + 8 by omega,
        hsk.2.2.2.2.2.2.2, hna.2.1] at this; cases this
    · -- k+5 ≠ a: at +6, k+11 is t1, a+6 is t2!
      intro h; have := hEq h 6; rw [show k + 5 + 6 = k + 11 by omega, hnk.2.2.2.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
    · -- k+5 ≠ a+2: at +1, k+6 is t2, a+3 is t1
      intro h; have := hEq h 1; rw [show k + 5 + 1 = k + 6 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.2.2, hsa.2.2.2.2.1] at this; cases this
    · -- k+5 ≠ a+3: at +3, k+8 is t1, a+6 is t2
      intro h; have := hEq h 3; rw [show k + 5 + 3 = k + 8 by omega, show a + 3 + 3 = a + 6 by omega,
        hnk.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
    · -- k+5 ≠ a+5
      intro h; exact hne (hsub_eq h)

/-- Helper for `isSDDS`: an `SDDS` arc's double vertices `{k+2, k+3, k+5, k+6}` cannot coincide with
    ANY `SDS` arc's `{a, a+2, a+3, a+5}` or ANY other `SDDS` arc's `{a, a+2, a+3, a+5, a+6, a+8}`,
    and if `k` (resp. `k+8`) is a single NOT yet in `s`, then `k-2` (resp. `k+10`) is NOT in `s`! -/
lemma isSDDS_disjoint_doubles {m : ℕ} (hm : 3 ≤ m) {k a : ℕ}
    (hk : isSDDS m (by omega) k = true) :
    let N := (zoneWord m).length
    (isSDS m (by omega) a = true →
      ∀ x ∈ ({k + 2, k + 3, k + 5, k + 6} : Finset ℕ),
        ∀ y ∈ ({a, a + 2, a + 3, a + 5} : Finset ℕ), x % N ≠ y % N) ∧
    (isSDDS m (by omega) a = true → k % N ≠ a % N →
      ∀ x ∈ ({k + 2, k + 3, k + 5, k + 6} : Finset ℕ),
        ∀ y ∈ ({a, a + 2, a + 3, a + 5, a + 6, a + 8} : Finset ℕ), x % N ≠ y % N) := by
  have hsk := isSDDS_spec hk
  have hN := zoneWord_length_ge_56 m hm
  set N := (zoneWord m).length
  have hEq : ∀ {x y : ℕ}, x % N = y % N → ∀ d, zty m (by omega) (x + d) = zty m (by omega) (y + d) :=
    fun hxy d => zty_congr_add hxy d
  have hsub_eq : ∀ {x y d : ℕ}, (x + d) % N = (y + d) % N → x % N = y % N := by
    intro x y d h
    have h1 := congrArg (fun t => (t + (N - d % N)) % N) h
    have hlt : d % N < N := Nat.mod_lt d (by omega)
    have hsimp : ∀ z, ((z + d) % N + (N - d % N)) % N = z % N := by
      intro z
      rw [Nat.mod_add_mod, show z + d + (N - d % N) = z + (d / N * N + d % N) + (N - d % N) by
        have := Nat.div_add_mod' d N; omega]
      have : z + (d / N * N + d % N) + (N - d % N) = z + (d / N + 1) * N := by
        rw [add_mul, one_mul]; omega
      rw [this, Nat.add_mul_mod_self_right]
    simpa [hsimp] using h1
  -- Quick helper: a single S (t2, S, t2) can never equal a double vertex (which has an adjacent t1)!
  have hsingle_ne_dbl : ∀ {x y : ℕ},
      zty m (by omega) (x + N - 1) = .t2 → zty m (by omega) (x + 1) = .t2 →
      (zty m (by omega) (y + 1) = .t1 ∨ zty m (by omega) (y + N - 1) = .t1) →
      x % N ≠ y % N := by
    intro x y hxm hxp hy hxy
    rcases hy with hyp | hym
    · have := hEq hxy 1; rw [hxp, hyp] at this; cases this
    · have hxy' : (x + N - 1) % N = (y + N - 1) % N := by
        have h1 : x + N - 1 = x + (N - 1) := by omega
        have h2 : y + N - 1 = y + (N - 1) := by omega
        rw [h1, h2, Nat.add_mod, hxy, ← Nat.add_mod]
      have := hEq hxy' 0; simp only [add_zero] at this; rw [hxm, hym] at this; cases this
  constructor
  · intro ha
    have hsa := isSDS_spec ha
    have hna := isSDS_next_six hm ha
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · exact hsingle_ne_dbl hsa.1 hsa.2.2.1 (Or.inl (by rw [show k + 2 + 1 = k + 3 by omega]; exact hsk.2.2.2.2.1)) hxy.symm
    · have := hEq hxy 3; rw [show k + 2 + 3 = k + 5 by omega, show a + 2 + 3 = a + 5 by omega] at this
      have h4 := hEq hxy 4; rw [show k + 2 + 4 = k + 6 by omega, show a + 2 + 4 = a + 6 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2] at h4; cases h4
    · have := hEq hxy 1; rw [show k + 2 + 1 = k + 3 by omega, show a + 3 + 1 = a + 4 by omega,
        hsk.2.2.2.2.1, hsa.2.2.2.2.2.1] at this; cases this
    · exact hsingle_ne_dbl (by rw [show a + 5 + N - 1 = (a + 4) + N by omega, zty_add_len]; exact hsa.2.2.2.2.2.1)
        (by rw [show a + 5 + 1 = a + 6 by omega]; exact hsa.2.2.2.2.2.2.2)
        (Or.inl (by rw [show k + 2 + 1 = k + 3 by omega]; exact hsk.2.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hsa.1 hsa.2.2.1
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) hxy.symm
    · have := hEq hxy 1; rw [show k + 3 + 1 = k + 4 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.1, hsa.2.2.2.2.1] at this; cases this
    · have := hEq hxy 3; rw [show k + 3 + 3 = k + 6 by omega, show a + 3 + 3 = a + 6 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2] at this; cases this
    · exact hsingle_ne_dbl (by rw [show a + 5 + N - 1 = (a + 4) + N by omega, zty_add_len]; exact hsa.2.2.2.2.2.1)
        (by rw [show a + 5 + 1 = a + 6 by omega]; exact hsa.2.2.2.2.2.2.2)
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hsa.1 hsa.2.2.1
        (Or.inl (by rw [show k + 5 + 1 = k + 6 by omega]; exact hsk.2.2.2.2.2.2.2.1)) hxy.symm
    · -- k+5 = a+2 ⇒ k+4 = a+1, k+3 = a: impossible since k+3 has prev t1 (k+2), a has prev t2!
      have h3 : (k + 3) % N = a % N := by
        have h1 : (k + 3 + 2) % N = (a + 2) % N := by simpa using hxy
        exact hsub_eq h1
      exact hsingle_ne_dbl hsa.1 hsa.2.2.1
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) h3.symm
    · have := hEq hxy 1; rw [show k + 5 + 1 = k + 6 by omega, show a + 3 + 1 = a + 4 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.1] at this; cases this
    · exact hsingle_ne_dbl (by rw [show a + 5 + N - 1 = (a + 4) + N by omega, zty_add_len]; exact hsa.2.2.2.2.2.1)
        (by rw [show a + 5 + 1 = a + 6 by omega]; exact hsa.2.2.2.2.2.2.2)
        (Or.inl (by rw [show k + 5 + 1 = k + 6 by omega]; exact hsk.2.2.2.2.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hsa.1 hsa.2.2.1
        (Or.inr (by rw [show k + 6 + N - 1 = (k + 5) + N by omega, zty_add_len]; exact hsk.2.2.2.2.2.2.1)) hxy.symm
    · have := hEq hxy 1; rw [show k + 6 + 1 = k + 7 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.2.2.2.1, hsa.2.2.2.2.1] at this; cases this
    · have h3 : (k + 3) % N = a % N := by
        have h1 : (k + 3 + 3) % N = (a + 3) % N := by simpa using hxy
        exact hsub_eq h1
      exact hsingle_ne_dbl hsa.1 hsa.2.2.1
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) h3.symm
    · exact hsingle_ne_dbl (by rw [show a + 5 + N - 1 = (a + 4) + N by omega, zty_add_len]; exact hsa.2.2.2.2.2.1)
        (by rw [show a + 5 + 1 = a + 6 by omega]; exact hsa.2.2.2.2.2.2.2)
        (Or.inr (by rw [show k + 6 + N - 1 = (k + 5) + N by omega, zty_add_len]; exact hsk.2.2.2.2.2.2.1)) hxy.symm
  · intro ha hne
    have hsa := isSDDS_spec ha
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hS0_a : zty m (by omega) (a + N - 1) = .t2 ∧ zty m (by omega) (a + 1) = .t2 := ⟨hsa.1, hsa.2.2.1⟩
    have hS8_a : zty m (by omega) (a + 8 + N - 1) = .t2 ∧ zty m (by omega) (a + 8 + 1) = .t2 :=
      ⟨by rw [show a + 8 + N - 1 = (a + 7) + N by omega, zty_add_len]; exact hsa.2.2.2.2.2.2.2.2.1,
       by rw [show a + 8 + 1 = a + 9 by omega]; exact hsa.2.2.2.2.2.2.2.2.2.2⟩
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsingle_ne_dbl hS0_a.1 hS0_a.2 (Or.inl (by rw [show k + 2 + 1 = k + 3 by omega]; exact hsk.2.2.2.2.1)) hxy.symm
    · exact hne (hsub_eq hxy)
    · have := hEq hxy 1; rw [show k + 2 + 1 = k + 3 by omega, show a + 3 + 1 = a + 4 by omega,
        hsk.2.2.2.2.1, hsa.2.2.2.2.2.1] at this; cases this
    · have := hEq hxy 4; rw [show k + 2 + 4 = k + 6 by omega, show a + 5 + 4 = a + 9 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2.2.2.2] at this; cases this
    · have := hEq hxy 1; rw [show k + 2 + 1 = k + 3 by omega, show a + 6 + 1 = a + 7 by omega,
        hsk.2.2.2.2.1, hsa.2.2.2.2.2.2.2.2.1] at this; cases this
    · exact hsingle_ne_dbl hS8_a.1 hS8_a.2 (Or.inl (by rw [show k + 2 + 1 = k + 3 by omega]; exact hsk.2.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hS0_a.1 hS0_a.2
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) hxy.symm
    · have := hEq hxy 1; rw [show k + 3 + 1 = k + 4 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.1, hsa.2.2.2.2.1] at this; cases this
    · exact hne (hsub_eq hxy)
    · have := hEq hxy 1; rw [show k + 3 + 1 = k + 4 by omega, show a + 5 + 1 = a + 6 by omega,
        hsk.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2.1] at this; cases this
    · have := hEq hxy 3; rw [show k + 3 + 3 = k + 6 by omega, show a + 6 + 3 = a + 9 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2.2.2.2] at this; cases this
    · exact hsingle_ne_dbl hS8_a.1 hS8_a.2
        (Or.inr (by rw [show k + 3 + N - 1 = (k + 2) + N by omega, zty_add_len]; exact hsk.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hS0_a.1 hS0_a.2 (Or.inl (by rw [show k + 5 + 1 = k + 6 by omega]; exact hsk.2.2.2.2.2.2.2.1)) hxy.symm
    · have := hEq hxy 4; rw [show k + 5 + 4 = k + 9 by omega, show a + 2 + 4 = a + 6 by omega,
        hsk.2.2.2.2.2.2.2.2.2.2, hsa.2.2.2.2.2.2.2.1] at this; cases this
    · have := hEq hxy 1; rw [show k + 5 + 1 = k + 6 by omega, show a + 3 + 1 = a + 4 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.1] at this; cases this
    · exact hne (hsub_eq hxy)
    · have := hEq hxy 1; rw [show k + 5 + 1 = k + 6 by omega, show a + 6 + 1 = a + 7 by omega,
        hsk.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2.2.1] at this; cases this
    · exact hsingle_ne_dbl hS8_a.1 hS8_a.2 (Or.inl (by rw [show k + 5 + 1 = k + 6 by omega]; exact hsk.2.2.2.2.2.2.2.1)) hxy.symm
    · exact hsingle_ne_dbl hS0_a.1 hS0_a.2
        (Or.inr (by rw [show k + 6 + N - 1 = (k + 5) + N by omega, zty_add_len]; exact hsk.2.2.2.2.2.2.1)) hxy.symm
    · have := hEq hxy 1; rw [show k + 6 + 1 = k + 7 by omega, show a + 2 + 1 = a + 3 by omega,
        hsk.2.2.2.2.2.2.2.2.1, hsa.2.2.2.2.1] at this; cases this
    · have := hEq hxy 3; rw [show k + 6 + 3 = k + 9 by omega, show a + 3 + 3 = a + 6 by omega,
        hsk.2.2.2.2.2.2.2.2.2.2, hsa.2.2.2.2.2.2.2.1] at this; cases this
    · have := hEq hxy 1; rw [show k + 6 + 1 = k + 7 by omega, show a + 5 + 1 = a + 6 by omega,
        hsk.2.2.2.2.2.2.2.2.1, hsa.2.2.2.2.2.2.2.1] at this; cases this
    · exact hne (hsub_eq hxy)
    · exact hsingle_ne_dbl hS8_a.1 hS8_a.2
        (Or.inr (by rw [show k + 6 + N - 1 = (k + 5) + N by omega, zty_add_len]; exact hsk.2.2.2.2.2.2.1)) hxy.symm

/-- For `m ≥ 3`, `zoneWord m` has no cyclic factor `t2, t1, t2, t1, t2` (two adjacent singles). -/
lemma zoneWord_no_21212 {m : ℕ} (hm : 3 ≤ m) (q : ℕ)
    (e0 : zty m (by omega) q = .t2)
    (e1 : zty m (by omega) (q + 1) = .t1)
    (e2 : zty m (by omega) (q + 2) = .t2)
    (e3 : zty m (by omega) (q + 3) = .t1)
    (e4 : zty m (by omega) (q + 4) = .t2) : False := by
  have hN := zoneWord_length_ge_56 m hm
  set N := (zoneWord m).length
  have hm1 : 2 ≤ m - 1 := by omega
  have hw : zoneWord m = sigmaWord (zoneWord (m - 1)) := by
    have h1 := zoneWord_succ (m - 1) (by omega); rw [show m - 1 + 1 = m by omega] at h1; exact h1
  have hlin : ∀ u : List ZoneType,
      (∀ j : ℕ, (hj : j + 1 < u.length) → u[j]'(by omega) = .t2 → u[j + 1]'hj = .t1) →
      ∀ i : ℕ, (hi : i + 4 < (sigmaWord u).length) →
        (sigmaWord u)[i]'(by omega) = .t2 → (sigmaWord u)[i + 1]'(by omega) = .t1 →
        (sigmaWord u)[i + 2]'(by omega) = .t2 → (sigmaWord u)[i + 3]'(by omega) = .t1 →
        (sigmaWord u)[i + 4]'hi = .t2 → False := by
    intro u; induction u with
    | nil => intro _ i hi; simp [sigmaWord] at hi
    | cons b tl ih =>
      intro hno i hi f0 f1 f2 f3 f4
      have hno_tl : ∀ j : ℕ, (hj : j + 1 < tl.length) → tl[j]'(by omega) = .t2 → tl[j + 1]'hj = .t1 :=
        fun j hj htj => hno (j + 1) (by simp; omega) (by simpa using htj)
      simp only [sigmaWord_cons] at hi f0 f1 f2 f3 f4
      cases b with
      | t1 =>
        simp only [sigmaStep] at hi f0 f1 f2 f3 f4
        rcases i with _ | _ | _ | r
        · simp at f0
        · simp at f0
        · cases tl with
          | nil => simp [sigmaWord] at hi
          | cons c tl' =>
            cases c with
            | t1 => simp [sigmaWord_cons, sigmaStep] at f2
            | t2 =>
              cases tl' with
              | nil => simp [sigmaWord, sigmaStep] at hi
              | cons d tl'' =>
                have hd : d = .t1 := hno_tl 0 (by simp) rfl
                subst hd; simp [sigmaWord_cons, sigmaStep] at f4
        · exact ih hno_tl r (by simp at hi; omega)
            (by simpa using f0) (by simpa using f1) (by simpa using f2) (by simpa using f3) (by simpa using f4)
      | t2 =>
        simp only [sigmaStep] at hi f0 f1 f2 f3 f4
        rcases i with _ | _ | r
        · simp at f0
        · cases tl with
          | nil => simp [sigmaWord] at hi
          | cons c tl' =>
            have hc : c = .t1 := hno 0 (by simp) rfl
            subst hc; simp [sigmaWord_cons, sigmaStep] at f2
        · exact ih hno_tl r (by simp at hi; omega)
            (by simpa using f0) (by simpa using f1) (by simpa using f2) (by simpa using f3) (by simpa using f4)
  let u := zoneWord (m - 1)
  have hu_pos : 0 < u.length := zoneWord_length_pos (m - 1) (by omega)
  have hu_no22 : ∀ j : ℕ, (hj : j + 1 < (u ++ u).length) →
      (u ++ u)[j]'(by omega) = .t2 → (u ++ u)[j + 1]'hj = .t1 := by
    intro j hj h2
    have hpa_u := zoneWord_part_a (m - 1) hm1
    by_cases hlt : j < u.length
    · have g0 : (u ++ u)[j]'(by omega) = u.get ⟨j, hlt⟩ := by rw [List.getElem_append_left hlt]; rfl
      have g1 : (u ++ u)[j + 1]'hj = u.get ⟨(j + 1) % u.length, Nat.mod_lt _ hu_pos⟩ := by
        simpa [List.get_eq_getElem] using getElem_append_self u hu_pos j 1 hlt (by omega)
      rw [g1]; exact (hpa_u ⟨j, hlt⟩).1 (g0.symm.trans h2)
    · have hj' : j - u.length < u.length := by simp at hj; omega
      have g0 : (u ++ u)[j]'(by omega) = u.get ⟨j - u.length, hj'⟩ := by
        rw [List.getElem_append_right (by omega)]; rfl
      have g1 : (u ++ u)[j + 1]'hj = u.get ⟨(j - u.length + 1) % u.length, Nat.mod_lt _ hu_pos⟩ := by
        rw [List.getElem_append_right (by omega)]
        simp only [List.get_eq_getElem]
        congr 1; rw [show j + 1 - u.length = j - u.length + 1 by omega, Nat.mod_eq_of_lt (by simp at hj; omega)]
      rw [g1]; exact (hpa_u ⟨j - u.length, hj'⟩).1 (g0.symm.trans h2)
  have hww : zoneWord m ++ zoneWord m = sigmaWord (u ++ u) := by rw [hw, sigmaWord_append]
  have hlen : (sigmaWord (u ++ u)).length = N + N := by rw [← hww, List.length_append]
  set i0 := q % N
  have hi0 : i0 < N := Nat.mod_lt _ (by omega)
  have hget : ∀ d : ℕ, (hd : d ≤ 4) →
      (sigmaWord (u ++ u))[i0 + d]'(by omega) = zty m (by omega) (q + d) := by
    intro d hd
    have h1 : (zoneWord m ++ zoneWord m)[i0 + d]'(by rw [List.length_append]; omega) =
        (zoneWord m)[(i0 + d) % N]'(Nat.mod_lt _ (by omega)) :=
      getElem_append_self (zoneWord m) (by omega) i0 d hi0 (by omega)
    simpa [hww, zty, i0, List.get_eq_getElem, Nat.mod_add_mod] using h1
  exact hlin (u ++ u) hu_no22 i0 (by omega)
    (by simpa using (hget 0 (by omega)).trans (by simpa using e0))
    (by rw [hget 1 (by omega)]; exact e1)
    (by rw [hget 2 (by omega)]; exact e2)
    (by rw [hget 3 (by omega)]; exact e3)
    (by rw [hget 4 (by omega)]; exact e4)

/-- Key single-endpoint helper: if `p` is a single (`t2, p, t2`) and `p - 2` (or `p + 2`) belongs to
    an `SDS` or `SDDS` arc `a`, then `p` ITSELF is an endpoint of that arc `a`! -/
lemma single_nbr2_in_arc_imp_self {m : ℕ} (hm : 3 ≤ m) {p a : ℕ}
    (hpm : zty m (by omega) (p + (zoneWord m).length - 1) = .t2)
    (hp0 : zty m (by omega) p = .t1)
    (hpp : zty m (by omega) (p + 1) = .t2) :
    let N := (zoneWord m).length
    (isSDS m (by omega) a = true →
      ((p + N - 2) % N ∈ ({a % N, (a + 2) % N, (a + 3) % N, (a + 5) % N} : Finset ℕ) ∨
       (p + 2) % N ∈ ({a % N, (a + 2) % N, (a + 3) % N, (a + 5) % N} : Finset ℕ)) →
      p % N = a % N ∨ p % N = (a + 5) % N) ∧
    (isSDDS m (by omega) a = true →
      ((p + N - 2) % N ∈ ({a % N, (a + 2) % N, (a + 3) % N, (a + 5) % N, (a + 6) % N, (a + 8) % N} : Finset ℕ) ∨
       (p + 2) % N ∈ ({a % N, (a + 2) % N, (a + 3) % N, (a + 5) % N, (a + 6) % N, (a + 8) % N} : Finset ℕ)) →
      p % N = a % N ∨ p % N = (a + 8) % N) := by
  have hN := zoneWord_length_ge_56 m hm
  set N := (zoneWord m).length
  have hEq : ∀ {x y : ℕ}, x % N = y % N → ∀ d, zty m (by omega) (x + d) = zty m (by omega) (y + d) :=
    fun hxy d => zty_congr_add hxy d
  have hshift2 : ∀ {x y : ℕ}, (x + N - 2) % N = y % N → x % N = (y + 2) % N := by
    intro x y h
    have h1 := congrArg (fun t => (t + 2) % N) h
    rw [Nat.mod_add_mod, show x + N - 2 + 2 = x + N by omega, Nat.add_mod_right, Nat.mod_add_mod] at h1
    exact h1
  have hsub2 : ∀ {x y : ℕ}, (x + 2) % N = (y + 2) % N → x % N = y % N := by
    intro x y h
    have h1 := congrArg (fun t => (t + (N - 2)) % N) h
    have hs : ∀ z, ((z + 2) % N + (N - 2)) % N = z % N := by
      intro z; rw [Nat.mod_add_mod, show z + 2 + (N - 2) = z + N by omega, Nat.add_mod_right]
    simpa [hs] using h1
  constructor
  · intro ha hmem
    have hsa := isSDS_spec ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with (h | h | h | h) | (h | h | h | h)
    · have hp := hshift2 h; have := hEq hp 1; rw [hpp, show a + 2 + 1 = a + 3 by omega, hsa.2.2.2.2.1] at this; cases this
    · have hp := hshift2 h; have := hEq hp 0; simp only [add_zero] at this; rw [hp0, hsa.2.2.2.2.2.1] at this; cases this
    · right; simpa [Nat.add_assoc] using hshift2 h
    · have hp := hshift2 h; have := hEq hp 0; simp only [add_zero] at this
      have hna := isSDS_next_six hm ha
      have h1 := hEq hp 1; rw [hpp, show a + 5 + 2 + 1 = a + 8 by omega, hna.2.1] at h1; cases h1
    · exfalso
      have hpa : zty m (by omega) (p + 2) = .t1 := by rw [← zty_mod, h, zty_mod]; exact hsa.2.1
      have hpa1 : zty m (by omega) (p + 3) = .t2 := by
        have := hEq h 1; rw [show p + 2 + 1 = p + 3 by omega] at this; rw [this, hsa.2.2.1]
      exact zoneWord_no_21212 hm (p + N - 1) hpm
        (by rw [show p + N - 1 + 1 = p + N by omega, zty_add_len]; exact hp0)
        (by rw [show p + N - 1 + 2 = (p + 1) + N by omega, zty_add_len]; exact hpp)
        (by rw [show p + N - 1 + 3 = (p + 2) + N by omega, zty_add_len]; exact hpa)
        (by rw [show p + N - 1 + 4 = (p + 3) + N by omega, zty_add_len]; exact hpa1)
    · left; exact hsub2 h
    · have h1 : (p + 1) % N = (a + 2) % N := by
        have h2 : (p + 1 + 1) % N = (a + 2 + 1) % N := by simpa using h
        have h3 := congrArg (fun t => (t + (N - 1)) % N) h2
        have hs : ∀ z, ((z + 1) % N + (N - 1)) % N = z % N := by
          intro z; rw [Nat.mod_add_mod, show z + 1 + (N - 1) = z + N by omega, Nat.add_mod_right]
        simpa [hs] using h3
      have := hEq h1 0; simp only [add_zero] at this; rw [hpp, hsa.2.2.2.1] at this; cases this
    · have h1 : (p + 1) % N = (a + 4) % N := by
        have h2 : (p + 1 + 1) % N = (a + 4 + 1) % N := by simpa using h
        have h3 := congrArg (fun t => (t + (N - 1)) % N) h2
        have hs : ∀ z, ((z + 1) % N + (N - 1)) % N = z % N := by
          intro z; rw [Nat.mod_add_mod, show z + 1 + (N - 1) = z + N by omega, Nat.add_mod_right]
        simpa [hs] using h3
      have h0' : p % N = (a + 3) % N := by
        have h2 : (p + 1) % N = (a + 3 + 1) % N := h1
        have h3 := congrArg (fun t => (t + (N - 1)) % N) h2
        have hs : ∀ z, ((z + 1) % N + (N - 1)) % N = z % N := by
          intro z; rw [Nat.mod_add_mod, show z + 1 + (N - 1) = z + N by omega, Nat.add_mod_right]
        simpa [hs] using h3
      have hpm' : (p + N - 1) % N = (a + 2) % N := by
        have h2 := congrArg (fun t => (t + (N - 1)) % N) h0'
        rw [Nat.mod_add_mod, Nat.mod_add_mod, show p + (N - 1) = p + N - 1 by omega,
          show a + 3 + (N - 1) = (a + 2) + N by omega, Nat.add_mod_right] at h2
        exact h2
      have := hEq hpm' 0; simp only [add_zero] at this; rw [hpm, hsa.2.2.2.1] at this; cases this
  · intro ha hmem
    have hsa := isSDDS_spec ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    -- Helper: zty m _ (a + 10) ... wait: we only need p+2 ≠ a (no two adjacent singles, proved in first branch? Let's extract!)
    rcases hmem with (h | h | h | h | h | h) | (h | h | h | h | h | h)
    · have hp := hshift2 h; have := hEq hp 1; rw [hpp, show a + 2 + 1 = a + 3 by omega, hsa.2.2.2.2.1] at this; cases this
    · have hp := hshift2 h; have := hEq hp 0; simp only [add_zero] at this; rw [hp0, hsa.2.2.2.2.2.1] at this; cases this
    · have hp := hshift2 h; have := hEq hp 1; rw [hpp, show a + 3 + 2 + 1 = a + 6 by omega, hsa.2.2.2.2.2.2.2.1] at this; cases this
    · have hp := hshift2 h; have := hEq hp 0; simp only [add_zero] at this; rw [hp0, hsa.2.2.2.2.2.2.2.2.1] at this; cases this
    · right; simpa [Nat.add_assoc] using hshift2 h
    · exfalso
      have hp := hshift2 h
      have ha10 : zty m (by omega) (a + 10) = .t1 := by
        have := hEq hp 0; simp only [add_zero] at this; rw [← this, hp0]
      have ha11 : zty m (by omega) (a + 11) = .t2 := by
        have := hEq hp 1; rw [show a + 8 + 2 + 1 = a + 11 by omega] at this; rw [← this, hpp]
      exact zoneWord_no_21212 hm (a + 7)
        hsa.2.2.2.2.2.2.2.2.1 hsa.2.2.2.2.2.2.2.2.2.1 hsa.2.2.2.2.2.2.2.2.2.2 ha10 ha11
    · exfalso
      have hpa : zty m (by omega) (p + 2) = .t1 := by rw [← zty_mod, h, zty_mod]; exact hsa.2.1
      have hpa1 : zty m (by omega) (p + 3) = .t2 := by
        have := hEq h 1; rw [show p + 2 + 1 = p + 3 by omega] at this; rw [this, hsa.2.2.1]
      exact zoneWord_no_21212 hm (p + N - 1) hpm
        (by rw [show p + N - 1 + 1 = p + N by omega, zty_add_len]; exact hp0)
        (by rw [show p + N - 1 + 2 = (p + 1) + N by omega, zty_add_len]; exact hpp)
        (by rw [show p + N - 1 + 3 = (p + 2) + N by omega, zty_add_len]; exact hpa)
        (by rw [show p + N - 1 + 4 = (p + 3) + N by omega, zty_add_len]; exact hpa1)
    · left; exact hsub2 h
    · have h1 : (p + 1) % N = (a + 2) % N := by
        have h2 : (p + 1 + 1) % N = (a + 2 + 1) % N := by simpa using h
        have h3 := congrArg (fun t => (t + (N - 1)) % N) h2
        have hs : ∀ z, ((z + 1) % N + (N - 1)) % N = z % N := by
          intro z; rw [Nat.mod_add_mod, show z + 1 + (N - 1) = z + N by omega, Nat.add_mod_right]
        simpa [hs] using h3
      have := hEq h1 0; simp only [add_zero] at this; rw [hpp, hsa.2.2.2.1] at this; cases this
    · have h0' : p % N = (a + 3) % N := by
        have h2 : (p + 2) % N = (a + 3 + 2) % N := by simpa using h
        exact hsub2 h2
      have hpm' : (p + N - 1) % N = (a + 2) % N := by
        have h2 := congrArg (fun t => (t + (N - 1)) % N) h0'
        rw [Nat.mod_add_mod, Nat.mod_add_mod, show p + (N - 1) = p + N - 1 by omega,
          show a + 3 + (N - 1) = (a + 2) + N by omega, Nat.add_mod_right] at h2
        exact h2
      have := hEq hpm' 0; simp only [add_zero] at this; rw [hpm, hsa.2.2.2.1] at this; cases this
    · have h1 : (p + 1) % N = (a + 5) % N := by
        have h2 : (p + 1 + 1) % N = (a + 5 + 1) % N := by simpa using h
        have h3 := congrArg (fun t => (t + (N - 1)) % N) h2
        have hs : ∀ z, ((z + 1) % N + (N - 1)) % N = z % N := by
          intro z; rw [Nat.mod_add_mod, show z + 1 + (N - 1) = z + N by omega, Nat.add_mod_right]
        simpa [hs] using h3
      have := hEq h1 0; simp only [add_zero] at this; rw [hpp, hsa.2.2.2.2.2.2.1] at this; cases this
    · have h0' : p % N = (a + 6) % N := by
        have h2 : (p + 2) % N = (a + 6 + 2) % N := by simpa using h
        exact hsub2 h2
      have hpm' : (p + N - 1) % N = (a + 5) % N := by
        have h2 := congrArg (fun t => (t + (N - 1)) % N) h0'
        rw [Nat.mod_add_mod, Nat.mod_add_mod, show p + (N - 1) = p + N - 1 by omega,
          show a + 6 + (N - 1) = (a + 5) + N by omega, Nat.add_mod_right] at h2
        exact h2
      have := hEq hpm' 0; simp only [add_zero] at this; rw [hpm, hsa.2.2.2.2.2.2.1] at this; cases this

/-- **Arc-Cover Theorem for `zoneWord m` (`m ≥ 3`)**: every `.t1` index `j` belongs to either
    an `SDS` arc `{k, k+2, k+3, k+5}` or an `SDDS` arc `{k, k+2, k+3, k+5, k+6, k+8}`! -/
theorem zoneWord_t1_covered {m : ℕ} (hm : 3 ≤ m) (j : ℕ) (ht : zty m (by omega) j = .t1) :
    let N := (zoneWord m).length
    (∃ k < N, isSDS m (by omega) k = true ∧
      j % N ∈ ({k % N, (k + 2) % N, (k + 3) % N, (k + 5) % N} : Finset ℕ)) ∨
    (∃ k < N, isSDDS m (by omega) k = true ∧
      j % N ∈ ({k % N, (k + 2) % N, (k + 3) % N, (k + 5) % N, (k + 6) % N, (k + 8) % N} : Finset ℕ)) := by
  -- Use `zoneWord m = (zoneWord (m - 2)).flatMap sigma2Step`!
  have hw2 : zoneWord m = (zoneWord (m - 2)).flatMap sigma2Step := by
    have h1 := zoneWord_succ (m - 2) (by omega)
    have h2 := zoneWord_succ (m - 1) (by omega)
    rw [show m - 2 + 1 = m - 1 by omega] at h1
    rw [show m - 1 + 1 = m by omega] at h2
    rw [h2, h1, sigmaWord_sigmaWord]
  -- Every block of `sigma2Step` has length 8 (`t1`: `[1,1,2,1,1,2,1,2]`) or 5 (`t2`: `[1,1,2,1,2]`),
  -- and ends in `[2, 1, 2]`. So in `w ++ w = (u ++ u).flatMap sigma2Step`, look at `j' := j % N + N`!
  -- Because `j' ≥ N ≥ 56`, the block containing `j'` is NOT the first block, so its predecessor block ends in `[2, 1, 2]`!
  set u := zoneWord (m - 2)
  set N := (zoneWord m).length
  have hN := zoneWord_length_ge_56 m hm
  have hww : zoneWord m ++ zoneWord m = (u ++ u).flatMap sigma2Step := by
    rw [hw2, List.flatMap_append]
  -- Linear block-cover lemma on ANY list `v`: any index `idx` with `3 ≤ idx < (v.flatMap sigma2Step).length`
  -- either lands in a `t2` block (len 5) preceded by `[2, 1, 2]` (giving `SDS` at `start - 2`) or
  -- a `t1` block (len 8) preceded by `[2, 1, 2]` (giving `SDDS` at `start - 2`)!
  have hlin : ∀ (v : List ZoneType),
      ∀ (prev : List ZoneType) (hpl : prev.length ≥ 3),
        prev[prev.length - 3]'(by omega) = .t2 →
        prev[prev.length - 2]'(by omega) = .t1 →
        prev[prev.length - 1]'(by omega) = .t2 →
      ∀ (idx : ℕ), prev.length ≤ idx → (hi : idx < (prev ++ v.flatMap sigma2Step).length) →
        (prev ++ v.flatMap sigma2Step)[idx]'hi = .t1 →
        ∃ p : ℕ,
          (∃ hp7 : p + 7 < (prev ++ v.flatMap sigma2Step).length,
            (∀ d : ℕ, (hd : d ∈ ([0, 2, 5, 7] : List ℕ)) →
              (prev ++ v.flatMap sigma2Step)[p + d]'(by simp at hd; omega) = .t2) ∧
            (∀ d : ℕ, (hd : d ∈ ([1, 3, 4, 6] : List ℕ)) →
              (prev ++ v.flatMap sigma2Step)[p + d]'(by simp at hd; omega) = .t1) ∧
            idx ∈ ({p + 1, p + 3, p + 4, p + 6} : Finset ℕ)) ∨
          (∃ hp10 : p + 10 < (prev ++ v.flatMap sigma2Step).length,
            (∀ d : ℕ, (hd : d ∈ ([0, 2, 5, 8, 10] : List ℕ)) →
              (prev ++ v.flatMap sigma2Step)[p + d]'(by simp at hd; omega) = .t2) ∧
            (∀ d : ℕ, (hd : d ∈ ([1, 3, 4, 6, 7, 9] : List ℕ)) →
              (prev ++ v.flatMap sigma2Step)[p + d]'(by simp at hd; omega) = .t1) ∧
            idx ∈ ({p + 1, p + 3, p + 4, p + 6, p + 7, p + 9} : Finset ℕ)) := by
    intro v
    induction v with
    | nil => intro prev _ _ _ _ idx hlo hi _; simp at hi; omega
    | cons a tl ih =>
      intro prev hpl hp3 hp2 hp1 idx hlo hi hidx
      have hflat : prev ++ (a :: tl).flatMap sigma2Step = (prev ++ sigma2Step a) ++ tl.flatMap sigma2Step := by
        simp [List.flatMap_cons, List.append_assoc]
      cases a with
      | t1 =>
        by_cases hin : idx < prev.length + 8
        · refine ⟨prev.length - 3, Or.inr ?_⟩
          have hlen_tot : prev.length + 8 ≤ (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step).length := by
            simp [List.flatMap_cons, sigma2Step]
          have hget_prev : ∀ r : ℕ, (hr : r < prev.length) →
              (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[r]'(by omega) = prev[r]'hr := by
            intro r hr; exact List.getElem_append_left hr
          have hget_blk : ∀ r : ℕ, (hr : r < 8) →
              (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + r]'(by omega) =
                ([ZoneType.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2] : List ZoneType)[r]'hr := by
            intro r hr
            rw [List.getElem_append_right (by omega)]
            simp only [List.flatMap_cons, sigma2Step]
            rw [List.getElem_append_left (by simp; omega)]
            congr 1; omega
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl
            · simpa [show prev.length - 3 + 0 = prev.length - 3 by omega] using (hget_prev (prev.length - 3) (by omega)).trans hp3
            · simpa [show prev.length - 3 + 2 = prev.length - 1 by omega] using (hget_prev (prev.length - 1) (by omega)).trans hp1
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 2]'(by omega)).trans (hget_blk 2 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 5]'(by omega)).trans (hget_blk 5 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 7]'(by omega)).trans (hget_blk 7 (by omega))
          · intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
            · simpa [show prev.length - 3 + 1 = prev.length - 2 by omega] using (hget_prev (prev.length - 2) (by omega)).trans hp2
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 0]'(by omega)).trans (hget_blk 0 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 1]'(by omega)).trans (hget_blk 1 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 3]'(by omega)).trans (hget_blk 3 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 4]'(by omega)).trans (hget_blk 4 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[prev.length + 6]'(by omega)).trans (hget_blk 6 (by omega))
          · have hr : idx - prev.length < 8 := by omega
            have hblk : (prev ++ (ZoneType.t1 :: tl).flatMap sigma2Step)[idx]'hi =
                ([ZoneType.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2] : List ZoneType)[idx - prev.length]'hr := by
              convert hget_blk (idx - prev.length) hr using 2; omega
            rw [hidx] at hblk
            have hcases : idx - prev.length = 0 ∨ idx - prev.length = 1 ∨ idx - prev.length = 3 ∨
                idx - prev.length = 4 ∨ idx - prev.length = 6 := by
              generalize idx - prev.length = r at hr hblk
              rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp at hblk <;> omega
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
        · have hrec := ih (prev ++ sigma2Step .t1) (by simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            idx (by simp [sigma2Step]; omega) (by simpa [hflat] using hi) (by simpa [hflat] using hidx)
          simpa [hflat] using hrec
      | t2 =>
        by_cases hin : idx < prev.length + 5
        · refine ⟨prev.length - 3, Or.inl ?_⟩
          have hlen_tot : prev.length + 5 ≤ (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step).length := by
            simp [List.flatMap_cons, sigma2Step]
          have hget_prev : ∀ r : ℕ, (hr : r < prev.length) →
              (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[r]'(by omega) = prev[r]'hr := by
            intro r hr; exact List.getElem_append_left hr
          have hget_blk : ∀ r : ℕ, (hr : r < 5) →
              (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + r]'(by omega) =
                ([ZoneType.t1, .t1, .t2, .t1, .t2] : List ZoneType)[r]'hr := by
            intro r hr
            rw [List.getElem_append_right (by omega)]
            simp only [List.flatMap_cons, sigma2Step]
            rw [List.getElem_append_left (by simp; omega)]
            congr 1; omega
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl
            · simpa [show prev.length - 3 + 0 = prev.length - 3 by omega] using (hget_prev (prev.length - 3) (by omega)).trans hp3
            · simpa [show prev.length - 3 + 2 = prev.length - 1 by omega] using (hget_prev (prev.length - 1) (by omega)).trans hp1
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + 2]'(by omega)).trans (hget_blk 2 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + 4]'(by omega)).trans (hget_blk 4 (by omega))
          · intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl | rfl | rfl
            · simpa [show prev.length - 3 + 1 = prev.length - 2 by omega] using (hget_prev (prev.length - 2) (by omega)).trans hp2
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + 0]'(by omega)).trans (hget_blk 0 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + 1]'(by omega)).trans (hget_blk 1 (by omega))
            · exact (by congr 1; omega : _ = (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[prev.length + 3]'(by omega)).trans (hget_blk 3 (by omega))
          · have hr : idx - prev.length < 5 := by omega
            have hblk : (prev ++ (ZoneType.t2 :: tl).flatMap sigma2Step)[idx]'hi =
                ([ZoneType.t1, .t1, .t2, .t1, .t2] : List ZoneType)[idx - prev.length]'hr := by
              convert hget_blk (idx - prev.length) hr using 2; omega
            rw [hidx] at hblk
            have hcases : idx - prev.length = 0 ∨ idx - prev.length = 1 ∨ idx - prev.length = 3 := by
              generalize idx - prev.length = r at hr hblk
              rcases r with _ | _ | _ | _ | _ | _ <;> simp at hblk <;> omega
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega
        · have hrec := ih (prev ++ sigma2Step .t2) (by simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            (by rw [List.getElem_append_right (by simp [sigma2Step])]; simp [sigma2Step])
            idx (by simp [sigma2Step]; omega) (by simpa [hflat] using hi) (by simpa [hflat] using hidx)
          simpa [hflat] using hrec
  -- Apply `hlin` to `prev := zoneWord m` and `v := u` at `idx := N + j % N`!
  have hends : ∀ l : List ZoneType, l ≠ [] →
      ∃ h3 : (l.flatMap sigma2Step).length ≥ 3,
      (l.flatMap sigma2Step)[(l.flatMap sigma2Step).length - 3]'(by omega) = .t2 ∧
      (l.flatMap sigma2Step)[(l.flatMap sigma2Step).length - 2]'(by omega) = .t1 ∧
      (l.flatMap sigma2Step)[(l.flatMap sigma2Step).length - 1]'(by omega) = .t2 := by
    intro l hl
    induction l with
    | nil => contradiction
    | cons a tl ih =>
      cases tl with
      | nil => cases a <;> exact ⟨by simp [sigma2Step], by simp [sigma2Step], by simp [sigma2Step], by simp [sigma2Step]⟩
      | cons b tl' =>
        rcases ih (by simp) with ⟨hrec3, hrec_e3, hrec_e2, hrec_e1⟩
        have hlen : ((a :: b :: tl').flatMap sigma2Step).length =
            (sigma2Step a).length + ((b :: tl').flatMap sigma2Step).length := by
          rw [List.flatMap_cons, List.length_append]
        have hget : ∀ r : ℕ, (hr3 : r ≤ 3) → (hr1 : r ≥ 1) →
            ((a :: b :: tl').flatMap sigma2Step)[((a :: b :: tl').flatMap sigma2Step).length - r]'(by omega) =
            ((b :: tl').flatMap sigma2Step)[((b :: tl').flatMap sigma2Step).length - r]'(by omega) := by
          intro r hr3 hr1
          have hrec3' : 3 ≤ (sigma2Step b ++ tl'.flatMap sigma2Step).length := by simpa [List.flatMap_cons] using hrec3
          simp only [List.flatMap_cons]
          rw [List.getElem_append_right (by rw [List.length_append]; omega)]
          congr 1; rw [List.length_append]; omega
        refine ⟨by omega, ?_, ?_, ?_⟩
        · rw [hget 3 (by omega) (by omega)]; exact hrec_e3
        · rw [hget 2 (by omega) (by omega)]; exact hrec_e2
        · rw [hget 1 (by omega) (by omega)]; exact hrec_e1
  have hu_ne : u ≠ [] := by
    intro h; have := zoneWord_length_pos (m - 2) (by omega); simp [u, h] at this
  rcases hends u hu_ne with ⟨hprev3_u, hpe3_u, hpe2_u, hpe1_u⟩
  have hprev3 : (zoneWord m).length ≥ 3 := by rw [hw2]; exact hprev3_u
  have hpe3 : (zoneWord m)[(zoneWord m).length - 3]'(by omega) = .t2 := by simp only [hw2]; exact hpe3_u
  have hpe2 : (zoneWord m)[(zoneWord m).length - 2]'(by omega) = .t1 := by simp only [hw2]; exact hpe2_u
  have hpe1 : (zoneWord m)[(zoneWord m).length - 1]'(by omega) = .t2 := by simp only [hw2]; exact hpe1_u
  set idx := N + j % N
  have hidx_lt : idx < (zoneWord m ++ u.flatMap sigma2Step).length := by
    rw [← hw2, List.length_append]; have := Nat.mod_lt j (by omega : 0 < N); omega
  have hidx_val : (zoneWord m ++ u.flatMap sigma2Step)[idx]'hidx_lt = .t1 := by
    have h1 : (zoneWord m ++ zoneWord m)[idx]'(by rw [List.length_append]; have := Nat.mod_lt j (by omega : 0 < N); omega) =
        (zoneWord m)[j % N]'(Nat.mod_lt _ (by omega)) := by
      rw [List.getElem_append_right (by omega)]; congr 1; omega
    have h2 : (zoneWord m)[j % N]'(Nat.mod_lt _ (by omega)) = .t1 := ht
    simpa [hw2] using h1.trans h2
  rcases hlin u (zoneWord m) hprev3 hpe3 hpe2 hpe1
    idx (by omega) hidx_lt hidx_val with ⟨p, hcases⟩
  have hget_ww : ∀ t : ℕ, (ht' : t < (zoneWord m ++ u.flatMap sigma2Step).length) →
      (zoneWord m ++ u.flatMap sigma2Step)[t]'ht' = zty m (by omega) t := by
    intro t ht'
    have ht2 : t < (zoneWord m ++ zoneWord m).length := by simpa [hw2] using ht'
    have h1 : (zoneWord m ++ zoneWord m)[t]'ht2 = zty m (by omega) t := by
      by_cases hlt : t < N
      · rw [List.getElem_append_left hlt]; unfold zty; rw [List.get_eq_getElem]; congr 1; exact (Nat.mod_eq_of_lt hlt).symm
      · rw [List.getElem_append_right (by omega)]
        unfold zty; rw [List.get_eq_getElem]
        have hsub : t - N < N := by rw [List.length_append] at ht2; omega
        have hmod : t % N = t - N := by rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub]
        congr 1; exact hmod.symm
    simpa [hw2] using h1
  rcases hcases with ⟨hp7, h2s, h1s, hidx_in⟩ | ⟨hp10, h2s, h1s, hidx_in⟩
  · left
    refine ⟨(p + 1) % N, Nat.mod_lt _ (by omega), ?_, ?_⟩
    · rw [isSDS_mod]
      unfold isSDS; dsimp only
      simp only [Bool.and_eq_true, beq_iff_eq]
      have hzm1 : zty m (by omega) (p + 1 + N - 1) = zty m (by omega) p := by
        rw [show p + 1 + N - 1 = p + N by omega, zty_add_len]
      have h0 : zty m (by omega) p = .t2 := (hget_ww (p + 0) (by omega)).symm.trans (h2s 0 (by simp))
      have h1 : zty m (by omega) (p + 1) = .t1 := (hget_ww (p + 1) (by omega)).symm.trans (h1s 1 (by simp))
      have h2 : zty m (by omega) (p + 2) = .t2 := (hget_ww (p + 2) (by omega)).symm.trans (h2s 2 (by simp))
      have h3 : zty m (by omega) (p + 3) = .t1 := (hget_ww (p + 3) (by omega)).symm.trans (h1s 3 (by simp))
      have h4 : zty m (by omega) (p + 4) = .t1 := (hget_ww (p + 4) (by omega)).symm.trans (h1s 4 (by simp))
      have h5 : zty m (by omega) (p + 5) = .t2 := (hget_ww (p + 5) (by omega)).symm.trans (h2s 5 (by simp))
      have h6 : zty m (by omega) (p + 6) = .t1 := (hget_ww (p + 6) (by omega)).symm.trans (h1s 6 (by simp))
      have h7 : zty m (by omega) (p + 7) = .t2 := (hget_ww (p + 7) hp7).symm.trans (h2s 7 (by simp))
      refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hzm1.trans h0
      · exact h1
      · simpa [Nat.add_assoc] using h2
      · simpa [Nat.add_assoc] using h3
      · simpa [Nat.add_assoc] using h4
      · simpa [Nat.add_assoc] using h5
      · simpa [Nat.add_assoc] using h6
      · simpa [Nat.add_assoc] using h7
    · have hj_eq : j % N = idx % N := by simp [idx, Nat.add_mod_left]
      rw [hj_eq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hidx_in ⊢
      rcases hidx_in with h | h | h | h <;> rw [h]
      · left; simp
      · right; left; simp [Nat.mod_add_mod, show p + 1 + 2 = p + 3 by omega]
      · right; right; left; simp [Nat.mod_add_mod, show p + 1 + 3 = p + 4 by omega]
      · right; right; right; simp [Nat.mod_add_mod, show p + 1 + 5 = p + 6 by omega]
  · right
    refine ⟨(p + 1) % N, Nat.mod_lt _ (by omega), ?_, ?_⟩
    · rw [isSDDS_mod]
      unfold isSDDS; dsimp only
      simp only [Bool.and_eq_true, beq_iff_eq]
      have hzm1 : zty m (by omega) (p + 1 + N - 1) = zty m (by omega) p := by
        rw [show p + 1 + N - 1 = p + N by omega, zty_add_len]
      have h0 : zty m (by omega) p = .t2 := (hget_ww (p + 0) (by omega)).symm.trans (h2s 0 (by simp))
      have h1 : zty m (by omega) (p + 1) = .t1 := (hget_ww (p + 1) (by omega)).symm.trans (h1s 1 (by simp))
      have h2 : zty m (by omega) (p + 2) = .t2 := (hget_ww (p + 2) (by omega)).symm.trans (h2s 2 (by simp))
      have h3 : zty m (by omega) (p + 3) = .t1 := (hget_ww (p + 3) (by omega)).symm.trans (h1s 3 (by simp))
      have h4 : zty m (by omega) (p + 4) = .t1 := (hget_ww (p + 4) (by omega)).symm.trans (h1s 4 (by simp))
      have h5 : zty m (by omega) (p + 5) = .t2 := (hget_ww (p + 5) (by omega)).symm.trans (h2s 5 (by simp))
      have h6 : zty m (by omega) (p + 6) = .t1 := (hget_ww (p + 6) (by omega)).symm.trans (h1s 6 (by simp))
      have h7 : zty m (by omega) (p + 7) = .t1 := (hget_ww (p + 7) (by omega)).symm.trans (h1s 7 (by simp))
      have h8 : zty m (by omega) (p + 8) = .t2 := (hget_ww (p + 8) (by omega)).symm.trans (h2s 8 (by simp))
      have h9 : zty m (by omega) (p + 9) = .t1 := (hget_ww (p + 9) (by omega)).symm.trans (h1s 9 (by simp))
      have h10 : zty m (by omega) (p + 10) = .t2 := (hget_ww (p + 10) hp10).symm.trans (h2s 10 (by simp))
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hzm1.trans h0
      · exact h1
      · simpa [Nat.add_assoc] using h2
      · simpa [Nat.add_assoc] using h3
      · simpa [Nat.add_assoc] using h4
      · simpa [Nat.add_assoc] using h5
      · simpa [Nat.add_assoc] using h6
      · simpa [Nat.add_assoc] using h7
      · simpa [Nat.add_assoc] using h8
      · simpa [Nat.add_assoc] using h9
      · simpa [Nat.add_assoc] using h10
    · have hj_eq : j % N = idx % N := by simp [idx, Nat.add_mod_left]
      rw [hj_eq]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hidx_in ⊢
      rcases hidx_in with h | h | h | h | h | h <;> rw [h]
      · left; simp
      · right; left; simp [Nat.mod_add_mod, show p + 1 + 2 = p + 3 by omega]
      · right; right; left; simp [Nat.mod_add_mod, show p + 1 + 3 = p + 4 by omega]
      · right; right; right; left; simp [Nat.mod_add_mod, show p + 1 + 5 = p + 6 by omega]
      · right; right; right; right; left; simp [Nat.mod_add_mod, show p + 1 + 6 = p + 7 by omega]
      · right; right; right; right; right; simp [Nat.mod_add_mod, show p + 1 + 8 = p + 9 by omega]

/-! ### Section 4: `ZoneRing` structure and the 5 reusable joining primitives -/

/-- Packaged cyclic structure of `Zone c₀ m` (`m ≥ 1`) from Lemma 5.1. -/
structure ZoneRing (c₀ : sites37) (m : ℕ) (hm : 1 ≤ m) where
  cyc : List H2
  nodup : cyc.Nodup
  len_eq : cyc.length = (zoneWord m).length
  set_eq : ({x | x ∈ cyc} : Set H2) = Zone c₀ m
  frames : ∀ k : Fin cyc.length,
    let vPrev := cyc.get ⟨(k.1 + cyc.length - 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
    let vNext := cyc.get ⟨(k.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
    let i : ℕ := match (zoneWord m).get (k.cast len_eq) with | .t1 => 1 | .t2 => 2
    ∃ F : SiteFrame sites37 (cyc.get k),
      F.nbr 0 = vPrev ∧
      (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ i → F.nbr j ∈ Zone c₀ (m - 1)) ∧
      F.nbr (i + 1 : ℕ) = vNext ∧
      (∀ j : Fin 7, i + 2 ≤ j.1 → F.nbr j ∈ Zone c₀ (m + 1))

def mkZoneRing (c₀ : sites37) (m : ℕ) (hm : 1 ≤ m) : ZoneRing c₀ m hm :=
  let h := lem_5_1_zone_substitution_geom c₀ m hm
  let cyc := Classical.choose h
  let hs := Classical.choose_spec h
  ⟨cyc, hs.1, Classical.choose hs.2, (Classical.choose_spec hs.2).1, (Classical.choose_spec hs.2).2.1⟩

namespace ZoneRing

variable {c₀ : sites37} {m : ℕ} {hm : 1 ≤ m}

def N (R : ZoneRing c₀ m hm) : ℕ := R.cyc.length

lemma N_eq (R : ZoneRing c₀ m hm) : R.N = (zoneWord m).length := R.len_eq

lemma N_pos (R : ZoneRing c₀ m hm) : 0 < R.N := by
  rw [R.N_eq]; exact zoneWord_length_pos m hm

def v (R : ZoneRing c₀ m hm) (k : ℕ) : H2 :=
  R.cyc.get ⟨k % R.N, Nat.mod_lt _ R.N_pos⟩

lemma v_mod (R : ZoneRing c₀ m hm) (k : ℕ) : R.v (k % R.N) = R.v k := by
  simp [v]

lemma v_add_N (R : ZoneRing c₀ m hm) (k : ℕ) : R.v (k + R.N) = R.v k := by
  simp [v]

lemma v_mem_zone (R : ZoneRing c₀ m hm) (k : ℕ) : R.v k ∈ Zone c₀ m := by
  rw [← R.set_eq]; exact List.get_mem _ _

lemma v_mem_sites37 (R : ZoneRing c₀ m hm) (k : ℕ) : R.v k ∈ sites37 :=
  zone_subset_sites37 (R.v_mem_zone k)

lemma v_mem_oneVacancy (R : ZoneRing c₀ m hm) (k : ℕ) : R.v k ∈ oneVacancy c₀.1 :=
  zone_subset_oneVacancy hm (R.v_mem_zone k)

lemma v_ne_of_mod_ne (R : ZoneRing c₀ m hm) {a b : ℕ} (h : a % R.N ≠ b % R.N) :
    R.v a ≠ R.v b := by
  intro heq
  have hinj := List.nodup_iff_injective_get.mp R.nodup
  have := congrArg Fin.val (hinj heq)
  exact h this

lemma v_eq_iff (R : ZoneRing c₀ m hm) {a b : ℕ} :
    R.v a = R.v b ↔ a % R.N = b % R.N := by
  constructor
  · intro heq; by_contra h; exact R.v_ne_of_mod_ne h heq
  · intro h; unfold v; congr 1; exact Fin.ext h

def F_fin (R : ZoneRing c₀ m hm) (i : Fin R.cyc.length) : SiteFrame sites37 (R.cyc.get i) :=
  Classical.choose (R.frames i)

def F (R : ZoneRing c₀ m hm) (k : ℕ) : SiteFrame sites37 (R.v k) :=
  R.F_fin ⟨k % R.N, Nat.mod_lt _ R.N_pos⟩

lemma F_spec (R : ZoneRing c₀ m hm) (k : ℕ) :
    (R.F k).nbr 0 = R.v (k + R.N - 1) ∧
    (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ (zty m hm k).innerCount → (R.F k).nbr j ∈ Zone c₀ (m - 1)) ∧
    (R.F k).nbr ((zty m hm k).innerCount + 1 : ℕ) = R.v (k + 1) ∧
    (∀ j : Fin 7, (zty m hm k).innerCount + 2 ≤ j.1 → (R.F k).nbr j ∈ Zone c₀ (m + 1)) := by
  have hs := Classical.choose_spec (R.frames ⟨k % R.N, Nat.mod_lt _ R.N_pos⟩)
  have hty_eq : (zoneWord m).get ((⟨k % R.N, Nat.mod_lt _ R.N_pos⟩ : Fin R.cyc.length).cast R.len_eq) = zty m hm k := by
    unfold zty; congr 1; apply Fin.ext; dsimp only; simp [N, R.len_eq]
  have hi_eq : (match (zoneWord m).get ((⟨k % R.N, Nat.mod_lt _ R.N_pos⟩ : Fin R.cyc.length).cast R.len_eq) with
      | .t1 => 1 | .t2 => 2) = (zty m hm k).innerCount := by
    rw [hty_eq]; cases zty m hm k <;> rfl
  have hprev_eq : R.cyc.get ⟨(k % R.N + R.cyc.length - 1) % R.cyc.length, Nat.mod_lt _ R.N_pos⟩ = R.v (k + R.N - 1) := by
    unfold v; congr 1; apply Fin.ext; dsimp only [N]
    have hpos : 0 < R.cyc.length := R.N_pos
    have h1 : k % R.cyc.length + R.cyc.length - 1 = k % R.cyc.length + (R.cyc.length - 1) := by omega
    have h2 : k + R.cyc.length - 1 = k + (R.cyc.length - 1) := by omega
    rw [h1, h2, Nat.mod_add_mod]
  have hnext_eq : R.cyc.get ⟨(k % R.N + 1) % R.cyc.length, Nat.mod_lt _ R.N_pos⟩ = R.v (k + 1) := by
    unfold v; congr 1; apply Fin.ext; dsimp only [N]; simp [Nat.mod_add_mod]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Classical.choose (R.frames ⟨k % R.N, Nat.mod_lt _ R.N_pos⟩)).nbr 0 = _
    exact hs.1.trans hprev_eq
  · intro j hj1 hji; rw [← hi_eq] at hji; exact hs.2.1 j hj1 hji
  · rw [← hi_eq]
    change (Classical.choose (R.frames ⟨k % R.N, Nat.mod_lt _ R.N_pos⟩)).nbr _ = _
    exact hs.2.2.1.trans hnext_eq
  · intro j hj; rw [← hi_eq] at hj; exact hs.2.2.2 j hj

def inL (R : ZoneRing c₀ m hm) (k : ℕ) : H2 := (R.F k).nbr 1

def inR (R : ZoneRing c₀ m hm) (k : ℕ) : H2 :=
  if zty m hm k = .t1 then (R.F k).nbr 1 else (R.F k).nbr 2

lemma inL_congr (R : ZoneRing c₀ m hm) {a b : ℕ} (h : a % R.N = b % R.N) :
    R.inL a = R.inL b := by
  unfold inL F
  have hfin : (⟨a % R.N, Nat.mod_lt _ R.N_pos⟩ : Fin R.cyc.length) =
      ⟨b % R.N, Nat.mod_lt _ R.N_pos⟩ := Fin.ext h
  exact congrArg (fun i : Fin R.cyc.length => (R.F_fin i).nbr 1) hfin

lemma inL_mem (R : ZoneRing c₀ m hm) (k : ℕ) : R.inL k ∈ Zone c₀ (m - 1) := by
  have hs := (R.F_spec k).2.1 ⟨1, by omega⟩ le_rfl (by cases zty m hm k <;> simp [ZoneType.innerCount])
  simpa [inL] using hs

lemma inR_mem (R : ZoneRing c₀ m hm) (k : ℕ) : R.inR k ∈ Zone c₀ (m - 1) := by
  unfold inR; split_ifs with ht
  · exact R.inL_mem k
  · have ht2 : zty m hm k = .t2 := by cases h : zty m hm k <;> simp_all
    have hs := (R.F_spec k).2.1 ⟨2, by omega⟩ (by norm_num) (by rw [ht2]; simp [ZoneType.innerCount])
    simpa using hs

lemma inR_eq_nbr_inner (R : ZoneRing c₀ m hm) (k : ℕ) :
    R.inR k = (R.F k).nbr ((zty m hm k).innerCount : ℤ) := by
  unfold inR; cases h : zty m hm k <;> simp [ZoneType.innerCount]

lemma adj_v_succ (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.v k) (R.v (k + 1)) := by
  rw [← (R.F_spec k).2.2.1]
  exact (R.F k).adj_self_nbr _

lemma adj_v_prev (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.v k) (R.v (k + R.N - 1)) := by
  rw [← (R.F_spec k).1]
  exact (R.F k).adj_self_nbr _

lemma adj_v_inL (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.v k) (R.inL k) :=
  (R.F k).adj_self_nbr 1

lemma adj_v_inR (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.v k) (R.inR k) := by
  rw [R.inR_eq_nbr_inner]; exact (R.F k).adj_self_nbr _

lemma adj_inL_prev (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.inL k) (R.v (k + R.N - 1)) := by
  rw [inL, ← (R.F_spec k).1]; exact adj37_symm ((R.F k).adj_nbr_consec 0)

lemma adj_inR_succ (R : ZoneRing c₀ m hm) (k : ℕ) : Adj37 (R.inR k) (R.v (k + 1)) := by
  rw [R.inR_eq_nbr_inner, ← (R.F_spec k).2.2.1]
  simpa using (R.F k).adj_nbr_consec ((zty m hm k).innerCount : ℤ)

lemma adj_inL_inR_of_t2 (R : ZoneRing c₀ m hm) (k : ℕ) (ht : zty m hm k = .t2) :
    Adj37 (R.inL k) (R.inR k) := by
  unfold inL inR; simp only [ht, reduceCtorEq, ite_false]
  exact (R.F k).adj_nbr_consec 1

/-- **Fundamental Shared-Inner-Neighbor Identity**: `inL (k + 1) = inR k` for ALL `k`! -/
lemma inL_succ_eq_inR (R : ZoneRing c₀ m hm) (k : ℕ) : R.inL (k + 1) = R.inR k := by
  have hmem : R.inR k ∈ sites37 := zone_subset_sites37 (R.inR_mem k)
  have hadj_v : Adj37 (R.v (k + 1)) (R.inR k) := adj37_symm (R.adj_inR_succ k)
  have hadj_0 : Adj37 ((R.F (k + 1)).nbr 0) (R.inR k) := by
    rw [(R.F_spec (k + 1)).1]
    have hprev : R.v (k + 1 + R.N - 1) = R.v k := by
      rw [show k + 1 + R.N - 1 = k + R.N by omega, R.v_add_N]
    rw [hprev]; exact R.adj_v_inR k
  rcases ((R.F (k + 1)).nbr_iff (R.inR k) hmem).mp hadj_v with ⟨j, hj⟩
  have hj' : (R.F (k + 1)).nbr j = R.inR k := by simpa [SiteFrame.nbr] using hj.symm
  rw [← hj'] at hadj_0
  rcases ((R.F (k + 1)).adj_nbr_iff 0 j).mp hadj_0 with h1 | h6
  · have hj1 : j.1 = 1 := by omega
    rw [← hj', inL]; simp [hj1]
  · exfalso
    have hj6 : j.1 = 6 := by omega
    have hout : (R.F (k + 1)).nbr j ∈ Zone c₀ (m + 1) :=
      (R.F_spec (k + 1)).2.2.2 j (by cases zty m hm (k + 1) <;> simp [ZoneType.innerCount] <;> omega)
    rw [hj'] at hout
    exact zone_disjoint (by omega) (R.inR_mem k) hout

lemma inL_eq_inR_of_t1 (R : ZoneRing c₀ m hm) (k : ℕ) (ht : zty m hm k = .t1) :
    R.inR k = R.inL k := by
  simp [inR, inL, ht]

/-- All neighbors of `R.v k` in `ZoneUnion c₀ m ∪ {c₀.1}` lie in `{v(k-1), inL k, inR k, v(k+1)}`. -/
lemma unfixed_nbrs_subset (R : ZoneRing c₀ m hm) {s : Finset H2}
    (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m) (k : ℕ) {w : H2}
    (hw : w ∈ sites37) (hadj : Adj37 (R.v k) w) (hu : w ∈ UnfixedSites c₀.1 s) :
    w = R.v (k + R.N - 1) ∨ w = R.inL k ∨ w = R.inR k ∨ w = R.v (k + 1) := by
  rcases ((R.F k).nbr_iff w hw).mp hadj with ⟨j, hj⟩
  have hj' : (R.F k).nbr j = w := by simpa [SiteFrame.nbr] using hj.symm
  have hw_in : w ∈ ZoneUnion c₀ m ∪ {c₀.1} := by
    rcases hu with hws | hwc
    · exact Or.inl (hs_sub hws)
    · exact Or.inr hwc
  have hnot_out : w ∉ Zone c₀ (m + 1) := by
    intro hout
    rcases hw_in with hwu | hwc
    · exact zone_not_mem_zoneUnion_of_gt (by omega) hout hwu
    · rw [Set.mem_singleton_iff] at hwc
      exact zone_disjoint (show m + 1 ≠ 0 by omega) hout (by rw [zone_zero_eq]; exact hwc)
  have hlt : j.1 < (zty m hm k).innerCount + 2 := by
    by_contra hge; push Not at hge
    exact hnot_out (hj' ▸ (R.F_spec k).2.2.2 j hge)
  cases ht : zty m hm k with
  | t1 =>
    rw [ht] at hlt; simp only [ZoneType.innerCount] at hlt
    have hcases : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · left; rw [← hj']; simpa [h0] using (R.F_spec k).1
    · right; left; rw [← hj', inL]; simp [h1]
    · right; right; right; rw [← hj']
      have h3 := (R.F_spec k).2.2.1; rw [ht] at h3; simpa [ZoneType.innerCount, h2] using h3
  | t2 =>
    rw [ht] at hlt; simp only [ZoneType.innerCount] at hlt
    have hcases : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 ∨ j.1 = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · left; rw [← hj']; simpa [h0] using (R.F_spec k).1
    · right; left; rw [← hj', inL]; simp [h1]
    · right; right; left; rw [← hj', inR]; simp [ht, h2]
    · right; right; right; rw [← hj']
      have h4 := (R.F_spec k).2.2.1; rw [ht] at h4; simpa [ZoneType.innerCount, h3] using h4

/-! ### The 5 Reusable Joining Primitives on a `ZoneRing` (`m ≥ 2`) -/

/-- **Primitive 1**: Join a `t2` vertex when neither of its ring neighbors is in `s`. -/
lemma join_t2 (R : ZoneRing c₀ m hm) {s : Finset H2}
    (hs : IsGood c₀.1 s) (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m)
    (k : ℕ) (ht : zty m hm k = .t2) (hnot : R.v k ∉ s)
    (hprev : R.v (k + R.N - 1) ∉ s) (hnext : R.v (k + 1) ∉ s) :
    CanJoin c₀.1 s (R.v k) := by
  have hsub_ins : ((insert (R.v k) s : Finset H2) : Set H2) ⊆ ZoneUnion c₀ m := by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion hm le_rfl (R.v_mem_zone k)
    · exact hs_sub hxs
  apply j_le_two c₀.1 c₀.2 s (R.v k) hs (R.v_mem_oneVacancy k) hnot (R.F k)
  have hfilt_sub : Finset.univ.filter (fun j : Fin 7 => (R.F k).nbr j ∈ UnfixedSites c₀.1 (insert (R.v k) s)) ⊆
      ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin 7)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hmem_s : (R.F k).nbr j ∈ sites37 := by simpa [SiteFrame.nbr] using (R.F k).nbr_mem j
    have hu := R.unfixed_nbrs_subset hsub_ins k hmem_s ((R.F k).adj_self_nbr j) hj.2
    have h0_ne : (R.F k).nbr j ≠ R.v (k + R.N - 1) := by
      intro heq; rw [heq] at hj
      rcases hj.2 with h1 | h2
      · simp only [Finset.mem_coe, Finset.mem_insert] at h1
        rcases h1 with hvk | hvs
        · have hd := R.adj_v_prev k; rw [← hvk] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
        · exact hprev hvs
      · rw [Set.mem_singleton_iff] at h2
        exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + R.N - 1)) (by rw [zone_zero_eq]; exact h2)
    have h3_ne : (R.F k).nbr j ≠ R.v (k + 1) := by
      intro heq; rw [heq] at hj
      rcases hj.2 with h1 | h2
      · simp only [Finset.mem_coe, Finset.mem_insert] at h1
        rcases h1 with hvk | hvs
        · have hd := R.adj_v_succ k; rw [← hvk] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
        · exact hnext hvs
      · rw [Set.mem_singleton_iff] at h2
        exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + 1)) (by rw [zone_zero_eq]; exact h2)
    rcases hu with h0 | h1 | h2 | h3
    · exact absurd h0 h0_ne
    · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inL] using h1
      simp [(R.F k).nbr_injective hjeq]
    · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨2, by omega⟩ : Fin 7) := by simpa [inR, ht] using h2
      simp [(R.F k).nbr_injective hjeq]
    · exact absurd h3 h3_ne
  exact le_trans (Finset.card_le_card hfilt_sub) (le_trans (Finset.card_insert_le _ _) (by simp))

/-- **Primitive 2**: Join a `t1` vertex when at least one of its ring neighbors is NOT in `s`. -/
lemma join_t1_one_ring (R : ZoneRing c₀ m hm) {s : Finset H2}
    (hs : IsGood c₀.1 s) (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m)
    (k : ℕ) (ht : zty m hm k = .t1) (hnot : R.v k ∉ s)
    (hmiss : R.v (k + R.N - 1) ∉ s ∨ R.v (k + 1) ∉ s) :
    CanJoin c₀.1 s (R.v k) := by
  have hsub_ins : ((insert (R.v k) s : Finset H2) : Set H2) ⊆ ZoneUnion c₀ m := by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion hm le_rfl (R.v_mem_zone k)
    · exact hs_sub hxs
  apply j_le_two c₀.1 c₀.2 s (R.v k) hs (R.v_mem_oneVacancy k) hnot (R.F k)
  rcases hmiss with hprev | hnext
  · have hfilt_sub : Finset.univ.filter (fun j : Fin 7 => (R.F k).nbr j ∈ UnfixedSites c₀.1 (insert (R.v k) s)) ⊆
        ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin 7)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hmem_s : (R.F k).nbr j ∈ sites37 := by simpa [SiteFrame.nbr] using (R.F k).nbr_mem j
      have hu := R.unfixed_nbrs_subset hsub_ins k hmem_s ((R.F k).adj_self_nbr j) hj.2
      have h0_ne : (R.F k).nbr j ≠ R.v (k + R.N - 1) := by
        intro heq; rw [heq] at hj
        rcases hj.2 with h1 | h2
        · simp only [Finset.mem_coe, Finset.mem_insert] at h1
          rcases h1 with hvk | hvs
          · have hd := R.adj_v_prev k; rw [← hvk] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
          · exact hprev hvs
        · rw [Set.mem_singleton_iff] at h2
          exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + R.N - 1)) (by rw [zone_zero_eq]; exact h2)
      rcases hu with h0 | h1 | h2 | h3
      · exact absurd h0 h0_ne
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inL] using h1
        simp [(R.F k).nbr_injective hjeq]
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inR, ht] using h2
        simp [(R.F k).nbr_injective hjeq]
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨2, by omega⟩ : Fin 7) := by
          have hspec := (R.F_spec k).2.2.1; rw [ht] at hspec; simpa [ZoneType.innerCount] using h3.trans hspec.symm
        simp [(R.F k).nbr_injective hjeq]
    exact le_trans (Finset.card_le_card hfilt_sub) (le_trans (Finset.card_insert_le _ _) (by simp))
  · have hfilt_sub : Finset.univ.filter (fun j : Fin 7 => (R.F k).nbr j ∈ UnfixedSites c₀.1 (insert (R.v k) s)) ⊆
        ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 7)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hmem_s : (R.F k).nbr j ∈ sites37 := by simpa [SiteFrame.nbr] using (R.F k).nbr_mem j
      have hu := R.unfixed_nbrs_subset hsub_ins k hmem_s ((R.F k).adj_self_nbr j) hj.2
      have h2_ne : (R.F k).nbr j ≠ R.v (k + 1) := by
        intro heq; rw [heq] at hj
        rcases hj.2 with h1 | h2
        · simp only [Finset.mem_coe, Finset.mem_insert] at h1
          rcases h1 with hvk | hvs
          · have hd := R.adj_v_succ k; rw [← hvk] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
          · exact hnext hvs
        · rw [Set.mem_singleton_iff] at h2
          exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + 1)) (by rw [zone_zero_eq]; exact h2)
      rcases hu with h0 | h1 | h2 | h3
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨0, by omega⟩ : Fin 7) := by
          simpa using h0.trans (R.F_spec k).1.symm
        simp [(R.F k).nbr_injective hjeq]
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inL] using h1
        simp [(R.F k).nbr_injective hjeq]
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inR, ht] using h2
        simp [(R.F k).nbr_injective hjeq]
      · exact absurd h3 h2_ne
    exact le_trans (Finset.card_le_card hfilt_sub) (le_trans (Finset.card_insert_le _ _) (by simp))

/-- **Primitive 3**: Join a `t1` vertex `v k` via `lem_4_4_join_tau3` when both `v(k-1), v(k+1) ∈ s`
    and each of `v(k-1)` and `v(k+1)` is either `t1`, or `t2` with its far ring neighbor NOT in `s`! -/
lemma join_t1_tau3 (R : ZoneRing c₀ m hm) {s : Finset H2}
    (hs : IsGood c₀.1 s)
    (hprev_zone : ZoneUnion c₀ (m - 1) ⊆ (s : Set H2))
    (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m)
    (k : ℕ) (ht : zty m hm k = .t1) (hnot : R.v k ∉ s)
    (hprev_s : R.v (k + R.N - 1) ∈ s) (hnext_s : R.v (k + 1) ∈ s)
    (hleft : zty m hm (k + R.N - 1) = .t1 ∨ (zty m hm (k + R.N - 1) = .t2 ∧ R.v (k + R.N - 2) ∉ s))
    (hright : zty m hm (k + 1) = .t1 ∨ (zty m hm (k + 1) = .t2 ∧ R.v (k + 2) ∉ s)) :
    CanJoin c₀.1 s (R.v k) := by
  have hN7 : 7 ≤ R.N := by rw [R.N_eq]; exact zoneWord_length_ge_seven m hm
  have hsub_ins : ((insert (R.v k) s : Finset H2) : Set H2) ⊆ ZoneUnion c₀ m := by
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion hm le_rfl (R.v_mem_zone k)
    · exact hs_sub hxs
  have hc2_unfixed : R.inL k ∈ UnfixedSites c₀.1 (insert (R.v k) s) := by
    by_cases hm1 : m = 1
    · have h0 : R.inL k ∈ Zone c₀ 0 := by convert R.inL_mem k using 2; omega
      rw [zone_zero_eq, Set.mem_singleton_iff] at h0
      exact Or.inr h0
    · left
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_coe.mp (hprev_zone (zone_subset_zoneUnion (by omega) le_rfl (R.inL_mem k)))))
  have hprof : HasProfile sites37 (UnfixedSites c₀.1 (insert (R.v k) s)) (R.v k) 3 (R.F k) := by
    intro j
    constructor
    · intro hj
      have hmem_s : (R.F k).nbr j ∈ sites37 := by simpa [SiteFrame.nbr] using (R.F k).nbr_mem j
      have hu := R.unfixed_nbrs_subset hsub_ins k hmem_s ((R.F k).adj_self_nbr j) hj
      rcases hu with h0 | h1 | h2 | h3
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨0, by omega⟩ : Fin 7) := by simpa using h0.trans (R.F_spec k).1.symm
        have := congrArg Fin.val ((R.F k).nbr_injective hjeq); dsimp only at this; omega
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inL] using h1
        have := congrArg Fin.val ((R.F k).nbr_injective hjeq); dsimp only at this; omega
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨1, by omega⟩ : Fin 7) := by simpa [inR, ht] using h2
        have := congrArg Fin.val ((R.F k).nbr_injective hjeq); dsimp only at this; omega
      · have hjeq : (R.F k).nbr j = (R.F k).nbr (⟨2, by omega⟩ : Fin 7) := by
          have hspec := (R.F_spec k).2.2.1; rw [ht] at hspec; simpa [ZoneType.innerCount] using h3.trans hspec.symm
        have := congrArg Fin.val ((R.F k).nbr_injective hjeq); dsimp only at this; omega
    · intro hj3
      have hcases : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · have : (R.F k).nbr j = R.v (k + R.N - 1) := by simpa [h0] using (R.F_spec k).1
        rw [this]; exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hprev_s))
      · have : (R.F k).nbr j = R.inL k := by simp [inL, h1]
        rw [this]; exact hc2_unfixed
      · have : (R.F k).nbr j = R.v (k + 1) := by
          have hspec := (R.F_spec k).2.2.1; rw [ht] at hspec; simpa [ZoneType.innerCount, h2] using hspec
        rw [this]; exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hnext_s))
  -- Choose c₄ (for v(k-1)) and c₅ (for v(k+1)) depending on their types!
  let c₄ : H2 := if zty m hm (k + R.N - 1) = .t1 then R.v (k + R.N - 2) else R.inL (k + R.N - 1)
  let c₅ : H2 := if zty m hm (k + 1) = .t1 then R.v (k + 2) else R.inR (k + 1)
  have hprev_succ : R.v (k + R.N - 1 + 1) = R.v k := by
    rw [show k + R.N - 1 + 1 = k + R.N by omega, R.v_add_N]
  have hprev_prev : R.v (k + R.N - 1 + R.N - 1) = R.v (k + R.N - 2) := by
    unfold v; congr 1; apply Fin.ext; dsimp only
    rw [show k + R.N - 1 + R.N - 1 = (k + R.N - 2) + R.N by omega, Nat.add_mod_right]
  have hnext_prev : R.v (k + 1 + R.N - 1) = R.v k := by
    rw [show k + 1 + R.N - 1 = k + R.N by omega, R.v_add_N]
  have hinR_prev : R.inR (k + R.N - 1) = R.inL k := by
    have h1 := R.inL_succ_eq_inR (k + R.N - 1)
    have h2 : R.inL (k + R.N - 1 + 1) = R.inL k :=
      R.inL_congr (by rw [show k + R.N - 1 + 1 = k + R.N by omega, Nat.add_mod_right])
    exact h1.symm.trans h2
  have hinL_next : R.inL (k + 1) = R.inL k := by
    rw [R.inL_succ_eq_inR, R.inL_eq_inR_of_t1 k ht]
  have hmod_ne2 : ∀ d₁ d₂ : ℕ, d₁ < 5 → d₂ < 5 → d₁ ≠ d₂ → (k + R.N - 2 + d₁) % R.N ≠ (k + R.N - 2 + d₂) % R.N := by
    intro d₁ d₂ hd1 hd2 hne heq
    have hsub := congrArg (fun t => (t + (R.N - (k + R.N - 2) % R.N)) % R.N) heq
    have hsimp : ∀ d < 5, ((k + R.N - 2 + d) % R.N + (R.N - (k + R.N - 2) % R.N)) % R.N = d := by
      intro d hd
      have hlt := Nat.mod_lt (k + R.N - 2) R.N_pos
      rw [Nat.mod_add_mod]
      have h1 : k + R.N - 2 + d + (R.N - (k + R.N - 2) % R.N) =
          d + ((k + R.N - 2) / R.N + 1) * R.N := by
        have hdiv := Nat.div_add_mod' (k + R.N - 2) R.N
        rw [add_mul, one_mul]; omega
      rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsimp d₁ hd1, hsimp d₂ hd2] at hsub
    exact hne hsub
  have hc4_adj1 : Adj37 c₄ (R.v (k + R.N - 1)) := by
    dsimp only [c₄]; split_ifs
    · rw [← hprev_prev]; exact adj37_symm (R.adj_v_prev (k + R.N - 1))
    · exact adj37_symm (R.adj_v_inL (k + R.N - 1))
  have hc4_adj2 : Adj37 c₄ (R.inL k) := by
    dsimp only [c₄]; split_ifs with h1
    · rw [← hinR_prev, R.inL_eq_inR_of_t1 (k + R.N - 1) h1, ← hprev_prev]
      exact adj37_symm (R.adj_inL_prev (k + R.N - 1))
    · have ht2 : zty m hm (k + R.N - 1) = .t2 := by cases h : zty m hm (k + R.N - 1) <;> simp_all
      rw [← hinR_prev]; exact R.adj_inL_inR_of_t2 (k + R.N - 1) ht2
  have hc4_ne : c₄ ≠ R.v k := by
    dsimp only [c₄]; split_ifs
    · apply R.v_ne_of_mod_ne
      have := hmod_ne2 0 2 (by omega) (by omega) (by omega)
      simpa [show k + R.N - 2 + 2 = k + R.N by omega] using this
    · intro heq
      exact zone_disjoint (show m - 1 ≠ m by omega) (R.inL_mem (k + R.N - 1)) (heq ▸ R.v_mem_zone k)
  have hc5_adj2 : Adj37 c₅ (R.inL k) := by
    dsimp only [c₅]; split_ifs with h1
    · rw [← hinL_next, ← R.inL_eq_inR_of_t1 (k + 1) h1]
      exact adj37_symm (R.adj_inR_succ (k + 1))
    · have ht2 : zty m hm (k + 1) = .t2 := by cases h : zty m hm (k + 1) <;> simp_all
      rw [← hinL_next]; exact adj37_symm (R.adj_inL_inR_of_t2 (k + 1) ht2)
  have hc5_adj3 : Adj37 c₅ (R.v (k + 1)) := by
    dsimp only [c₅]; split_ifs
    · exact adj37_symm (R.adj_v_succ (k + 1))
    · exact adj37_symm (R.adj_v_inR (k + 1))
  have hc5_ne : c₅ ≠ R.v k := by
    dsimp only [c₅]; split_ifs
    · apply R.v_ne_of_mod_ne
      have := hmod_ne2 4 2 (by omega) (by omega) (by omega)
      simpa [show k + R.N - 2 + 4 = (k + 2) + R.N by omega, show k + R.N - 2 + 2 = k + R.N by omega] using this
    · intro heq
      exact zone_disjoint (show m - 1 ≠ m by omega) (R.inR_mem (k + 1)) (heq ▸ R.v_mem_zone k)
  have hu1 : ∀ w ∈ sites37, Adj37 (R.v (k + R.N - 1)) w → w ∈ UnfixedSites c₀.1 (insert (R.v k) s) →
      w = c₄ ∨ w = R.inL k ∨ w = R.v k := by
    intro w hw hadj hu
    have h4 := R.unfixed_nbrs_subset hsub_ins (k + R.N - 1) hw hadj hu
    rw [hprev_prev, hprev_succ, hinR_prev] at h4
    rcases hleft with ht1 | ⟨ht2, hfar_not⟩
    · simp only [c₄, ht1, ite_true]
      have hinL_eq : R.inL (k + R.N - 1) = R.inL k := by rw [← hinR_prev, R.inL_eq_inR_of_t1 _ ht1]
      rw [hinL_eq] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · simp only [c₄, ht2, reduceCtorEq, ite_false]
      rcases h4 with h | h | h | h
      · exfalso
        rw [h] at hu
        rcases hu with h1 | h2
        · simp only [Finset.mem_coe, Finset.mem_insert] at h1
          rcases h1 with hvk | hvs
          · have hne' : R.v (k + R.N - 2) ≠ R.v k := by
              apply R.v_ne_of_mod_ne
              have := hmod_ne2 0 2 (by omega) (by omega) (by omega)
              simpa [show k + R.N - 2 + 2 = k + R.N by omega] using this
            exact hne' hvk
          · exact hfar_not hvs
        · rw [Set.mem_singleton_iff] at h2
          exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + R.N - 2)) (by rw [zone_zero_eq]; exact h2)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hu3 : ∀ w ∈ sites37, Adj37 (R.v (k + 1)) w → w ∈ UnfixedSites c₀.1 (insert (R.v k) s) →
      w = R.v k ∨ w = R.inL k ∨ w = c₅ := by
    intro w hw hadj hu
    have h4 := R.unfixed_nbrs_subset hsub_ins (k + 1) hw hadj hu
    rw [hnext_prev, hinL_next] at h4
    rcases hright with ht1 | ⟨ht2, hfar_not⟩
    · simp only [c₅, ht1, ite_true]
      have hinR_eq : R.inR (k + 1) = R.inL k := by rw [R.inL_eq_inR_of_t1 _ ht1, hinL_next]
      rw [hinR_eq] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · simp only [c₅, ht2, reduceCtorEq, ite_false]
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso
        rw [h] at hu
        rcases hu with h1 | h2
        · simp only [Finset.mem_coe, Finset.mem_insert] at h1
          rcases h1 with hvk | hvs
          · have hne' : R.v (k + 2) ≠ R.v k := by
              apply R.v_ne_of_mod_ne
              have := hmod_ne2 4 2 (by omega) (by omega) (by omega)
              simpa [show k + R.N - 2 + 4 = (k + 2) + R.N by omega, show k + R.N - 2 + 2 = k + R.N by omega] using this
            exact hne' hvk
          · exact hfar_not hvs
        · rw [Set.mem_singleton_iff] at h2
          exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + 2)) (by rw [zone_zero_eq]; exact h2)
  exact j_tau3 c₀.1 c₀.2 s (R.v k) (R.v (k + R.N - 1)) (R.inL k) (R.v (k + 1)) c₄ c₅
    hs (R.v_mem_oneVacancy k) hnot (R.F k) hprof (R.F_spec k).1 rfl
    (by have h := (R.F_spec k).2.2.1; rw [ht] at h; simpa [ZoneType.innerCount] using h)
    hprev_s hnext_s hc4_adj1 hc4_adj2 hc4_ne hc5_adj2 hc5_adj3 hc5_ne hu1 hu3

/-- **Primitive 4**: Close `c = v k` in a `D-D` configuration (`t2, t1, [t1], t2, t1, t1, t2` at `k-2..k+4`, `m ≥ 2`)
    via `lem_4_5_nine_site`! Handles BOTH the 7th double of `Z_2` AND every `S-D-D-S` arc of `Z_m` (`m ≥ 3`)! -/
lemma close_DD (R : ZoneRing c₀ m hm) (hm2 : 2 ≤ m) {s : Finset H2}
    (hs : IsGood c₀.1 s)
    (hprev_zone : ZoneUnion c₀ (m - 1) ⊆ (s : Set H2))
    (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m)
    (k : ℕ)
    (_ht_m2 : zty m hm (k + R.N - 2) = .t2) (ht_m1 : zty m hm (k + R.N - 1) = .t1)
    (ht_0 : zty m hm k = .t1) (ht_1 : zty m hm (k + 1) = .t2)
    (ht_2 : zty m hm (k + 2) = .t1) (ht_3 : zty m hm (k + 3) = .t1)
    (_ht_4 : zty m hm (k + 4) = .t2)
    (hnot : R.v k ∉ s)
    (hc1_s : R.v (k + R.N - 1) ∈ s) (hc3_s : R.v (k + 1) ∈ s)
    (hc6_s : R.v (k + 2) ∈ s) (hc7_s : R.v (k + 3) ∈ s) :
    CanJoin c₀.1 s (R.v k) := by
  have hN21 : 21 ≤ R.N := by rw [R.N_eq]; exact zoneWord_length_ge_21 m hm2
  have hsub_ins : ((insert (R.v k) s : Finset H2) : Set H2) ⊆ ZoneUnion c₀ m := by
    intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion hm le_rfl (R.v_mem_zone k)
    · exact hs_sub hxs
  set c := R.v k
  set c₁ := R.v (k + R.N - 1)
  set c₂ := R.inL k
  set c₃ := R.v (k + 1)
  set c₄ := R.v (k + R.N - 2)
  set c₅ := R.inR (k + 1)
  set c₆ := R.v (k + 2)
  set c₇ := R.v (k + 3)
  set c₈ := R.v (k + 4)
  -- Helper: distinctness of 7 consecutive vertices in Z_m (since N ≥ 21)!
  have hmod7 : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → (k + R.N - 2 + a) % R.N ≠ (k + R.N - 2 + b) % R.N := by
    intro a b ha hb hab heq
    have hsub := congrArg (fun t => (t + (R.N - (k + R.N - 2) % R.N)) % R.N) heq
    have hsimp : ∀ d < 7, ((k + R.N - 2 + d) % R.N + (R.N - (k + R.N - 2) % R.N)) % R.N = d := by
      intro d hd
      have hlt := Nat.mod_lt (k + R.N - 2) R.N_pos
      rw [Nat.mod_add_mod]
      have h1 : k + R.N - 2 + d + (R.N - (k + R.N - 2) % R.N) =
          d + ((k + R.N - 2) / R.N + 1) * R.N := by
        have hdiv := Nat.div_add_mod' (k + R.N - 2) R.N
        rw [add_mul, one_mul]; omega
      rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsimp a ha, hsimp b hb] at hsub; exact hab hsub
  have hv_shift : ∀ d : ℕ, R.v (k + R.N - 2 + d) = match d with
      | 0 => c₄ | 1 => c₁ | 2 => c | 3 => c₃ | 4 => c₆ | 5 => c₇ | 6 => c₈ | _ => R.v (k + R.N - 2 + d) := by
    intro d
    rcases d with _ | _ | _ | _ | _ | _ | _ | _
    · rfl
    · simp only [c₁]; unfold v; congr 1; apply Fin.ext; dsimp only; congr 1; omega
    · simp only [c]; rw [show k + R.N - 2 + 2 = k + R.N by omega, R.v_add_N]
    · simp only [c₃]; rw [show k + R.N - 2 + 3 = (k + 1) + R.N by omega, R.v_add_N]
    · simp only [c₆]; rw [show k + R.N - 2 + 4 = (k + 2) + R.N by omega, R.v_add_N]
    · simp only [c₇]; rw [show k + R.N - 2 + 5 = (k + 3) + R.N by omega, R.v_add_N]
    · simp only [c₈]; rw [show k + R.N - 2 + 6 = (k + 4) + R.N by omega, R.v_add_N]
    · rfl
  have hring_ne : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → R.v (k + R.N - 2 + a) ≠ R.v (k + R.N - 2 + b) :=
    fun a b ha hb hab => R.v_ne_of_mod_ne (hmod7 a b ha hb hab)
  -- Shared inner-neighbor equalities!
  have hc2_eq_m1 : R.inL (k + R.N - 1) = c₂ := by
    have h1 := R.inL_succ_eq_inR (k + R.N - 1)
    have h2 : R.inL (k + R.N - 1 + 1) = c₂ :=
      R.inL_congr (by rw [show k + R.N - 1 + 1 = k + R.N by omega, Nat.add_mod_right])
    rw [← R.inL_eq_inR_of_t1 _ ht_m1]; exact h1.symm.trans h2
  have hc2_eq_1L : R.inL (k + 1) = c₂ := by
    rw [R.inL_succ_eq_inR, R.inL_eq_inR_of_t1 _ ht_0]
  have hc5_eq_2L : R.inL (k + 2) = c₅ := R.inL_succ_eq_inR (k + 1)
  have hc5_eq_2R : R.inR (k + 2) = c₅ := by rw [R.inL_eq_inR_of_t1 _ ht_2, hc5_eq_2L]
  have hc5_eq_3L : R.inL (k + 3) = c₅ := by rw [R.inL_succ_eq_inR, hc5_eq_2R]
  have hc5_eq_3R : R.inR (k + 3) = c₅ := by rw [R.inL_eq_inR_of_t1 _ ht_3, hc5_eq_3L]
  have hc5_eq_4L : R.inL (k + 4) = c₅ := by rw [R.inL_succ_eq_inR, hc5_eq_3R]
  have hc2_c5_adj : Adj37 c₂ c₅ := by rw [← hc2_eq_1L]; exact R.adj_inL_inR_of_t2 (k + 1) ht_1
  have hc2_ne_c5 : c₂ ≠ c₅ := by
    intro h; have hd := hc2_c5_adj; rw [h] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
  have hz_ne : ∀ {x y : H2}, x ∈ Zone c₀ m → y ∈ Zone c₀ (m - 1) → x ≠ y :=
    fun hx hy h => zone_disjoint (show m ≠ m - 1 by omega) hx (h ▸ hy)
  have hc2_mem : c₂ ∈ Zone c₀ (m - 1) := R.inL_mem k
  have hc5_mem : c₅ ∈ Zone c₀ (m - 1) := R.inR_mem (k + 1)
  have hdistinct : [c, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    have hm_c : c ∈ Zone c₀ m := R.v_mem_zone k
    have hm_c1 : c₁ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c3 : c₃ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c4 : c₄ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c6 : c₆ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c7 : c₇ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c8 : c₈ ∈ Zone c₀ m := R.v_mem_zone _
    refine ⟨⟨?_, hz_ne hm_c hc2_mem, ?_, ?_, hz_ne hm_c hc5_mem, ?_, ?_, ?_⟩,
      ⟨hz_ne hm_c1 hc2_mem, ?_, ?_, hz_ne hm_c1 hc5_mem, ?_, ?_, ?_⟩,
      ⟨(hz_ne hm_c3 hc2_mem).symm, (hz_ne hm_c4 hc2_mem).symm, hc2_ne_c5,
        (hz_ne hm_c6 hc2_mem).symm, (hz_ne hm_c7 hc2_mem).symm, (hz_ne hm_c8 hc2_mem).symm⟩,
      ⟨?_, hz_ne hm_c3 hc5_mem, ?_, ?_, ?_⟩,
      ⟨hz_ne hm_c4 hc5_mem, ?_, ?_, ?_⟩,
      ⟨(hz_ne hm_c6 hc5_mem).symm, (hz_ne hm_c7 hc5_mem).symm, (hz_ne hm_c8 hc5_mem).symm⟩,
      ⟨?_, ?_⟩, ?_⟩
    all_goals first
      | (have := hring_ne 2 1 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 0 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 0 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 0 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 4 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 4 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 5 6 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
  have hprev_prev : R.v (k + R.N - 1 + R.N - 1) = c₄ := by
    unfold c₄ v; congr 1; apply Fin.ext; dsimp only
    rw [show k + R.N - 1 + R.N - 1 = (k + R.N - 2) + R.N by omega, Nat.add_mod_right]
  have hprev_succ : R.v (k + R.N - 1 + 1) = c := by
    rw [show k + R.N - 1 + 1 = k + R.N by omega, R.v_add_N]
  have hnext_prev : R.v (k + 1 + R.N - 1) = c := by
    rw [show k + 1 + R.N - 1 = k + R.N by omega, R.v_add_N]
  have h2_prev : R.v (k + 2 + R.N - 1) = c₃ := by
    rw [show k + 2 + R.N - 1 = (k + 1) + R.N by omega, R.v_add_N]
  have h3_prev : R.v (k + 3 + R.N - 1) = c₆ := by
    rw [show k + 3 + R.N - 1 = (k + 2) + R.N by omega, R.v_add_N]
  -- Build Fc2 (0: c4, 1: c1, 2: c, 3: c3, 4: c5) and Fc5 (0: c2, 1: c3, 2: c6, 3: c7, 4: c8)!
  rcases build_five_nbr_frame (zone_subset_sites37 hc2_mem) (R.v_mem_sites37 (k + R.N - 2)) (R.v_mem_sites37 (k + R.N - 1))
      (R.v_mem_sites37 k) (R.v_mem_sites37 (k + 1)) (zone_subset_sites37 hc5_mem)
      (by change Adj37 c₂ c₄; rw [← hc2_eq_m1, ← hprev_prev]; exact R.adj_inL_prev (k + R.N - 1))
      (by change Adj37 c₂ c₁; rw [← hc2_eq_m1]; exact adj37_symm (R.adj_v_inL (k + R.N - 1)))
      (adj37_symm (R.adj_v_inL k))
      (by change Adj37 c₂ c₃; rw [← hc2_eq_1L]; exact adj37_symm (R.adj_v_inL (k + 1)))
      hc2_c5_adj
      (by change Adj37 c₄ c₁; rw [← hprev_prev]; exact adj37_symm (R.adj_v_prev (k + R.N - 1)))
      (by change Adj37 c₁ c; rw [← hprev_succ]; exact R.adj_v_succ (k + R.N - 1))
      (R.adj_v_succ k)
      (R.adj_v_inR (k + 1))
      (by have := hring_ne 2 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (by have := hring_ne 3 1 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (hz_ne (R.v_mem_zone k) hc5_mem).symm with ⟨Fc2, h2_0, h2_1, h2_2, h2_3, h2_4⟩
  rcases build_five_nbr_frame (zone_subset_sites37 hc5_mem) (zone_subset_sites37 hc2_mem) (R.v_mem_sites37 (k + 1))
      (R.v_mem_sites37 (k + 2)) (R.v_mem_sites37 (k + 3)) (R.v_mem_sites37 (k + 4))
      (adj37_symm hc2_c5_adj)
      (adj37_symm (R.adj_v_inR (k + 1)))
      (by rw [← hc5_eq_2L]; exact adj37_symm (R.adj_v_inL (k + 2)))
      (by rw [← hc5_eq_3L]; exact adj37_symm (R.adj_v_inL (k + 3)))
      (by rw [← hc5_eq_4L]; exact adj37_symm (R.adj_v_inL (k + 4)))
      (by rw [← hc2_eq_1L]; exact adj37_symm (R.adj_v_inL (k + 1)))
      (R.adj_v_succ (k + 1))
      (R.adj_v_succ (k + 2))
      (R.adj_v_succ (k + 3))
      (hz_ne (R.v_mem_zone (k + 2)) hc2_mem)
      (by have := hring_ne 5 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (by have := hring_ne 6 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this) with
    ⟨Fc5, h5_0, h5_1, h5_2, h5_3, h5_4⟩
  have hc2_u : c₂ ∈ UnfixedSites c₀.1 (insert c s) :=
    Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_coe.mp (hprev_zone (zone_subset_zoneUnion (by omega) le_rfl hc2_mem)))))
  have hc5_u : c₅ ∈ UnfixedSites c₀.1 (insert c s) :=
    Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_coe.mp (hprev_zone (zone_subset_zoneUnion (by omega) le_rfl hc5_mem)))))
  exact j_nine_site c₀.1 c₀.2 s c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ hs (R.v_mem_oneVacancy k) hnot hdistinct
    Fc2 h2_0 h2_1 h2_2 h2_3 h2_4 Fc5 h5_0 h5_1 h5_2 h5_3 h5_4
    hc1_s hc3_s hc6_s hc7_s hc2_u hc5_u
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins k hw hadj hu
      rw [R.inL_eq_inR_of_t1 _ ht_0] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + R.N - 1) hw hadj hu
      rw [hprev_prev, hprev_succ, R.inL_eq_inR_of_t1 _ ht_m1, hc2_eq_m1] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 1) hw hadj hu
      rw [hnext_prev, hc2_eq_1L] at h4
      exact h4)
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 2) hw hadj hu
      rw [h2_prev, hc5_eq_2L, hc5_eq_2R] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 3) hw hadj hu
      rw [h3_prev, hc5_eq_3L, hc5_eq_3R] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))

/-- **Primitive 5**: Close `c = v k` (`d₂`) in an `S-D-S` arc (`t2, t1, [t1], t2, t1, t2` at `k-2..k+3`, `m ≥ 3`)
    when `v(k+4)` (`c₉`) is still FIXED (`∉ s`), via `lem_4_5_nine_site`! -/
lemma close_SDS (R : ZoneRing c₀ m hm) (hm3 : 3 ≤ m) {s : Finset H2}
    (hs : IsGood c₀.1 s)
    (hprev_zone : ZoneUnion c₀ (m - 1) ⊆ (s : Set H2))
    (hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m)
    (k : ℕ)
    (_ht_m2 : zty m hm (k + R.N - 2) = .t2) (ht_m1 : zty m hm (k + R.N - 1) = .t1)
    (ht_0 : zty m hm k = .t1) (ht_1 : zty m hm (k + 1) = .t2)
    (ht_2 : zty m hm (k + 2) = .t1) (ht_3 : zty m hm (k + 3) = .t2)
    (hnot : R.v k ∉ s) (hc9_not : R.v (k + 4) ∉ s)
    (hc1_s : R.v (k + R.N - 1) ∈ s) (hc3_s : R.v (k + 1) ∈ s)
    (hc6_s : R.v (k + 2) ∈ s) (hc7_s : R.v (k + 3) ∈ s) :
    CanJoin c₀.1 s (R.v k) := by
  have hN56 : 56 ≤ R.N := by rw [R.N_eq]; exact zoneWord_length_ge_56 m hm3
  have hsub_ins : ((insert (R.v k) s : Finset H2) : Set H2) ⊆ ZoneUnion c₀ m := by
    intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion hm le_rfl (R.v_mem_zone k)
    · exact hs_sub hxs
  set c := R.v k
  set c₁ := R.v (k + R.N - 1)
  set c₂ := R.inL k
  set c₃ := R.v (k + 1)
  set c₄ := R.v (k + R.N - 2)
  set c₅ := R.inR (k + 1)
  set c₆ := R.v (k + 2)
  set c₇ := R.v (k + 3)
  set c₈ := R.inR (k + 3)
  have hmod7 : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → (k + R.N - 2 + a) % R.N ≠ (k + R.N - 2 + b) % R.N := by
    intro a b ha hb hab heq
    have hsub := congrArg (fun t => (t + (R.N - (k + R.N - 2) % R.N)) % R.N) heq
    have hsimp : ∀ d < 7, ((k + R.N - 2 + d) % R.N + (R.N - (k + R.N - 2) % R.N)) % R.N = d := by
      intro d hd
      have hlt := Nat.mod_lt (k + R.N - 2) R.N_pos
      rw [Nat.mod_add_mod]
      have h1 : k + R.N - 2 + d + (R.N - (k + R.N - 2) % R.N) =
          d + ((k + R.N - 2) / R.N + 1) * R.N := by
        have hdiv := Nat.div_add_mod' (k + R.N - 2) R.N
        rw [add_mul, one_mul]; omega
      rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsimp a ha, hsimp b hb] at hsub; exact hab hsub
  have hv_shift : ∀ d : ℕ, R.v (k + R.N - 2 + d) = match d with
      | 0 => c₄ | 1 => c₁ | 2 => c | 3 => c₃ | 4 => c₆ | 5 => c₇ | 6 => R.v (k + 4) | _ => R.v (k + R.N - 2 + d) := by
    intro d
    rcases d with _ | _ | _ | _ | _ | _ | _ | _
    · rfl
    · simp only [c₁]; unfold v; congr 1; apply Fin.ext; dsimp only; congr 1; omega
    · simp only [c]; rw [show k + R.N - 2 + 2 = k + R.N by omega, R.v_add_N]
    · simp only [c₃]; rw [show k + R.N - 2 + 3 = (k + 1) + R.N by omega, R.v_add_N]
    · simp only [c₆]; rw [show k + R.N - 2 + 4 = (k + 2) + R.N by omega, R.v_add_N]
    · simp only [c₇]; rw [show k + R.N - 2 + 5 = (k + 3) + R.N by omega, R.v_add_N]
    · change R.v (k + R.N - 2 + 6) = R.v (k + 4)
      rw [show k + R.N - 2 + 6 = (k + 4) + R.N by omega, R.v_add_N]
    · rfl
  have hring_ne : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → R.v (k + R.N - 2 + a) ≠ R.v (k + R.N - 2 + b) :=
    fun a b ha hb hab => R.v_ne_of_mod_ne (hmod7 a b ha hb hab)
  have hc2_eq_m1 : R.inL (k + R.N - 1) = c₂ := by
    have h1 := R.inL_succ_eq_inR (k + R.N - 1)
    have h2 : R.inL (k + R.N - 1 + 1) = c₂ :=
      R.inL_congr (by rw [show k + R.N - 1 + 1 = k + R.N by omega, Nat.add_mod_right])
    rw [← R.inL_eq_inR_of_t1 _ ht_m1]; exact h1.symm.trans h2
  have hc2_eq_1L : R.inL (k + 1) = c₂ := by rw [R.inL_succ_eq_inR, R.inL_eq_inR_of_t1 _ ht_0]
  have hc5_eq_2L : R.inL (k + 2) = c₅ := R.inL_succ_eq_inR (k + 1)
  have hc5_eq_2R : R.inR (k + 2) = c₅ := by rw [R.inL_eq_inR_of_t1 _ ht_2, hc5_eq_2L]
  have hc5_eq_3L : R.inL (k + 3) = c₅ := by rw [R.inL_succ_eq_inR, hc5_eq_2R]
  have hc2_c5_adj : Adj37 c₂ c₅ := by rw [← hc2_eq_1L]; exact R.adj_inL_inR_of_t2 (k + 1) ht_1
  have hc5_c8_adj : Adj37 c₅ c₈ := by rw [← hc5_eq_3L]; exact R.adj_inL_inR_of_t2 (k + 3) ht_3
  have hc2_mem : c₂ ∈ Zone c₀ (m - 1) := R.inL_mem k
  have hc5_mem : c₅ ∈ Zone c₀ (m - 1) := R.inR_mem (k + 1)
  have hc8_mem : c₈ ∈ Zone c₀ (m - 1) := R.inR_mem (k + 3)
  have hz_ne : ∀ {x y : H2}, x ∈ Zone c₀ m → y ∈ Zone c₀ (m - 1) → x ≠ y :=
    fun hx hy h => zone_disjoint (show m ≠ m - 1 by omega) hx (h ▸ hy)
  have hprev_prev : R.v (k + R.N - 1 + R.N - 1) = c₄ := by
    unfold c₄ v; congr 1; apply Fin.ext; dsimp only
    rw [show k + R.N - 1 + R.N - 1 = (k + R.N - 2) + R.N by omega, Nat.add_mod_right]
  have hprev_succ : R.v (k + R.N - 1 + 1) = c := by
    rw [show k + R.N - 1 + 1 = k + R.N by omega, R.v_add_N]
  have hnext_prev : R.v (k + 1 + R.N - 1) = c := by
    rw [show k + 1 + R.N - 1 = k + R.N by omega, R.v_add_N]
  have h2_prev : R.v (k + 2 + R.N - 1) = c₃ := by
    rw [show k + 2 + R.N - 1 = (k + 1) + R.N by omega, R.v_add_N]
  have h3_prev : R.v (k + 3 + R.N - 1) = c₆ := by
    rw [show k + 3 + R.N - 1 = (k + 2) + R.N by omega, R.v_add_N]
  -- Build Fc2 (0: c4, 1: c1, 2: c, 3: c3, 4: c5) and Fc5 (0: c2, 1: c3, 2: c6, 3: c7, 4: c8)!
  rcases build_five_nbr_frame (zone_subset_sites37 hc2_mem) (R.v_mem_sites37 (k + R.N - 2)) (R.v_mem_sites37 (k + R.N - 1))
      (R.v_mem_sites37 k) (R.v_mem_sites37 (k + 1)) (zone_subset_sites37 hc5_mem)
      (by change Adj37 c₂ c₄; rw [← hc2_eq_m1, ← hprev_prev]; exact R.adj_inL_prev (k + R.N - 1))
      (by change Adj37 c₂ c₁; rw [← hc2_eq_m1]; exact adj37_symm (R.adj_v_inL (k + R.N - 1)))
      (adj37_symm (R.adj_v_inL k))
      (by change Adj37 c₂ c₃; rw [← hc2_eq_1L]; exact adj37_symm (R.adj_v_inL (k + 1)))
      hc2_c5_adj
      (by change Adj37 c₄ c₁; rw [← hprev_prev]; exact adj37_symm (R.adj_v_prev (k + R.N - 1)))
      (by change Adj37 c₁ c; rw [← hprev_succ]; exact R.adj_v_succ (k + R.N - 1))
      (R.adj_v_succ k)
      (R.adj_v_inR (k + 1))
      (by have := hring_ne 2 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (by have := hring_ne 3 1 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (hz_ne (R.v_mem_zone k) hc5_mem).symm with ⟨Fc2, h2_0, h2_1, h2_2, h2_3, h2_4⟩
  rcases build_five_nbr_frame (zone_subset_sites37 hc5_mem) (zone_subset_sites37 hc2_mem) (R.v_mem_sites37 (k + 1))
      (R.v_mem_sites37 (k + 2)) (R.v_mem_sites37 (k + 3)) (zone_subset_sites37 hc8_mem)
      (adj37_symm hc2_c5_adj)
      (adj37_symm (R.adj_v_inR (k + 1)))
      (by rw [← hc5_eq_2L]; exact adj37_symm (R.adj_v_inL (k + 2)))
      (by rw [← hc5_eq_3L]; exact adj37_symm (R.adj_v_inL (k + 3)))
      hc5_c8_adj
      (by rw [← hc2_eq_1L]; exact adj37_symm (R.adj_v_inL (k + 1)))
      (R.adj_v_succ (k + 1))
      (R.adj_v_succ (k + 2))
      (R.adj_v_inR (k + 3))
      (hz_ne (R.v_mem_zone (k + 2)) hc2_mem)
      (by have := hring_ne 5 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      (hz_ne (R.v_mem_zone (k + 2)) hc8_mem).symm with ⟨Fc5, h5_0, h5_1, h5_2, h5_3, h5_4⟩
  -- Distinctness of c₂, c₅, c₈ comes immediately from Fc5 (nbr 0 = c₂, origin = c₅, nbr 4 = c₈)!
  have hc2_ne_c5 : c₂ ≠ c₅ := by
    intro h; have hd := hc2_c5_adj; rw [h] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
  have hc5_ne_c8 : c₅ ≠ c₈ := by
    intro h; have hd := hc5_c8_adj; rw [h] at hd; unfold Adj37 at hd; rw [dist_self] at hd; linarith [r7_pos]
  have hc2_ne_c8 : c₂ ≠ c₈ := by
    intro h
    have h04 : Fc5.nbr (⟨0, by omega⟩ : Fin 7) = Fc5.nbr (⟨4, by omega⟩ : Fin 7) := by
      simpa [h5_0, h5_4] using h
    have := congrArg Fin.val (Fc5.nbr_injective h04); dsimp only at this; omega
  have hdistinct : [c, c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    have hm_c : c ∈ Zone c₀ m := R.v_mem_zone k
    have hm_c1 : c₁ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c3 : c₃ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c4 : c₄ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c6 : c₆ ∈ Zone c₀ m := R.v_mem_zone _
    have hm_c7 : c₇ ∈ Zone c₀ m := R.v_mem_zone _
    refine ⟨⟨?_, hz_ne hm_c hc2_mem, ?_, ?_, hz_ne hm_c hc5_mem, ?_, ?_, hz_ne hm_c hc8_mem⟩,
      ⟨hz_ne hm_c1 hc2_mem, ?_, ?_, hz_ne hm_c1 hc5_mem, ?_, ?_, hz_ne hm_c1 hc8_mem⟩,
      ⟨(hz_ne hm_c3 hc2_mem).symm, (hz_ne hm_c4 hc2_mem).symm, hc2_ne_c5,
        (hz_ne hm_c6 hc2_mem).symm, (hz_ne hm_c7 hc2_mem).symm, hc2_ne_c8⟩,
      ⟨?_, hz_ne hm_c3 hc5_mem, ?_, ?_, hz_ne hm_c3 hc8_mem⟩,
      ⟨hz_ne hm_c4 hc5_mem, ?_, ?_, hz_ne hm_c4 hc8_mem⟩,
      ⟨(hz_ne hm_c6 hc5_mem).symm, (hz_ne hm_c7 hc5_mem).symm, hc5_ne_c8⟩,
      ⟨?_, hz_ne hm_c6 hc8_mem⟩, hz_ne hm_c7 hc8_mem⟩
    all_goals first
      | (have := hring_ne 2 1 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 2 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 3 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 1 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 0 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 3 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 0 4 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 0 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
      | (have := hring_ne 4 5 (by omega) (by omega) (by omega); simpa [hv_shift] using this)
  have hc2_u : c₂ ∈ UnfixedSites c₀.1 (insert c s) :=
    Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_coe.mp (hprev_zone (zone_subset_zoneUnion (by omega) le_rfl hc2_mem)))))
  have hc5_u : c₅ ∈ UnfixedSites c₀.1 (insert c s) :=
    Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_coe.mp (hprev_zone (zone_subset_zoneUnion (by omega) le_rfl hc5_mem)))))
  exact j_nine_site c₀.1 c₀.2 s c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ hs (R.v_mem_oneVacancy k) hnot hdistinct
    Fc2 h2_0 h2_1 h2_2 h2_3 h2_4 Fc5 h5_0 h5_1 h5_2 h5_3 h5_4
    hc1_s hc3_s hc6_s hc7_s hc2_u hc5_u
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins k hw hadj hu
      rw [R.inL_eq_inR_of_t1 _ ht_0] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + R.N - 1) hw hadj hu
      rw [hprev_prev, hprev_succ, R.inL_eq_inR_of_t1 _ ht_m1, hc2_eq_m1] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 1) hw hadj hu
      rw [hnext_prev, hc2_eq_1L] at h4; exact h4)
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 2) hw hadj hu
      rw [h2_prev, hc5_eq_2L, hc5_eq_2R] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    (fun w hw hadj hu => by
      have h4 := R.unfixed_nbrs_subset hsub_ins (k + 3) hw hadj hu
      rw [h3_prev, hc5_eq_3L] at h4
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exfalso
        rw [h] at hu
        rcases hu with h1 | h2
        · simp only [Finset.mem_coe, Finset.mem_insert] at h1
          rcases h1 with hvk | hvs
          · have hne' : R.v (k + 4) ≠ c := by
              have := hring_ne 6 2 (by omega) (by omega) (by omega); simpa [hv_shift] using this
            exact hne' hvk
          · exact hc9_not hvs
        · rw [Set.mem_singleton_iff] at h2
          exact zone_disjoint (show m ≠ 0 by omega) (R.v_mem_zone (k + 4)) (by rw [zone_zero_eq]; exact h2))

end ZoneRing

/-! ### Section 5: Inductive Construction of Good Sets `U_1`, `U_2`, and `U_m` (`m ≥ 1`) -/

/-- **Theorem 1.1 named step (Zone `Z₁`)**: `U₁ = Z₁` is finite and good. -/
theorem thm_1_1_step_zone1 (c₀ : sites37) :
    ∃ u1 : Finset H2, (u1 : Set H2) = ZoneUnion c₀ 1 ∧ IsGood c₀.1 u1 := by
  let R := mkZoneRing c₀ 1 (by omega)
  have hN7 : R.N = 7 := by rw [R.N_eq]; decide
  have ht1 : ∀ k, zty 1 (by omega) k = .t1 := by
    intro k
    have hfin : ∀ i : Fin (zoneWord 1).length, (zoneWord 1).get i = .t1 := by decide
    exact hfin ⟨k % (zoneWord 1).length, Nat.mod_lt _ (zoneWord_length_pos 1 (by omega))⟩
  have hprefix : ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
      ∃ s : Finset H2, (∀ x, x ∈ s ↔ ∃ i < n, x = R.v i) ∧ IsGood c₀.1 s := by
    intro n hn1 hn6
    induction n, hn1 using Nat.le_induction with
    | base =>
      refine ⟨{R.v 0}, fun x => by simp, j_singleton c₀.1 c₀.2 (R.v_mem_oneVacancy 0)⟩
    | succ k hk ih =>
      rcases ih (by omega) with ⟨s, hs_iff, hs_good⟩
      have hsub : (s : Set H2) ⊆ ZoneUnion c₀ 1 := by
        intro x hx; rcases (hs_iff x).mp hx with ⟨i, _, rfl⟩
        exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
      have hnot : R.v k ∉ s := by
        intro hmem; rcases (hs_iff _).mp hmem with ⟨i, hik, heq⟩
        exact R.v_ne_of_mod_ne (by rw [hN7, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) heq
      have hnext_not : R.v (k + 1) ∉ s := by
        intro hmem; rcases (hs_iff _).mp hmem with ⟨i, hik, heq⟩
        exact R.v_ne_of_mod_ne (by rw [hN7, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) heq
      have hjoin := R.join_t1_one_ring hs_good hsub k (ht1 k) hnot (Or.inr hnext_not)
      refine ⟨insert (R.v k) s, fun x => ?_, hjoin⟩
      rw [Finset.mem_insert, hs_iff]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨k, by omega, rfl⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        by_cases hik : i = k
        · left; rw [hik]
        · right; exact ⟨i, by omega, rfl⟩
  rcases hprefix 6 (by omega) le_rfl with ⟨s6, hs6_iff, hs6_good⟩
  have hsub6 : (s6 : Set H2) ⊆ ZoneUnion c₀ 1 := by
    intro x hx; rcases (hs6_iff x).mp hx with ⟨i, _, rfl⟩
    exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
  have hnot6 : R.v 6 ∉ s6 := by
    intro hmem; rcases (hs6_iff _).mp hmem with ⟨i, hi6, heq⟩
    exact R.v_ne_of_mod_ne (by rw [hN7, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) heq
  have h5_in : R.v (6 + R.N - 1) ∈ s6 := by
    rw [hs6_iff]; refine ⟨5, by omega, ?_⟩
    rw [R.v_eq_iff, hN7]
  have h0_in : R.v (6 + 1) ∈ s6 := by
    rw [hs6_iff]; refine ⟨0, by omega, ?_⟩
    rw [R.v_eq_iff, hN7]
  have hjoin6 := R.join_t1_tau3 hs6_good
    (by intro x hx; simp [ZoneUnion] at hx) hsub6 6 (ht1 6) hnot6 h5_in h0_in
    (Or.inl (ht1 _)) (Or.inl (ht1 _))
  refine ⟨insert (R.v 6) s6, ?_, hjoin6⟩
  ext x
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hs6_iff, ZoneUnion,
    Set.mem_iUnion, Finset.mem_Icc]
  constructor
  · rintro (rfl | ⟨i, _, rfl⟩)
    · exact ⟨1, ⟨le_rfl, le_rfl⟩, R.v_mem_zone 6⟩
    · exact ⟨1, ⟨le_rfl, le_rfl⟩, R.v_mem_zone i⟩
  · rintro ⟨r, ⟨hr1, hr2⟩, hxr⟩
    have hr_eq : r = 1 := by omega
    rw [hr_eq, ← R.set_eq] at hxr
    rcases List.mem_iff_get.mp hxr with ⟨idx, rfl⟩
    have hidx7 : idx.1 < 7 := by rw [← hN7]; exact idx.2
    have hv_eq : R.cyc.get idx = R.v idx.1 := by
      unfold ZoneRing.v; congr 1; exact Fin.ext (Nat.mod_eq_of_lt idx.2).symm
    rw [hv_eq]
    by_cases h6 : idx.1 = 6
    · left; rw [h6]
    · right; exact ⟨idx.1, by omega, rfl⟩

/-- Phase A helper: given `U_{m-1}` good (`m ≥ 2`), join all `t2` vertices of `Z_m`! -/
lemma zone_phase_t2 (c₀ : sites37) {m : ℕ} (hm : 2 ≤ m) (R : ZoneRing c₀ m (by omega))
    {um1 : Finset H2} (hum1_eq : (um1 : Set H2) = ZoneUnion c₀ (m - 1)) (hum1_good : IsGood c₀.1 um1) :
    ∃ s : Finset H2,
      (∀ x, x ∈ s ↔ x ∈ um1 ∨ ∃ i < R.N, zty m (by omega) i = .t2 ∧ x = R.v i) ∧
      IsGood c₀.1 s := by
  have hstep : ∀ n ≤ R.N,
      ∃ s : Finset H2,
        (∀ x, x ∈ s ↔ x ∈ um1 ∨ ∃ i < n, zty m (by omega) i = .t2 ∧ x = R.v i) ∧
        IsGood c₀.1 s := by
    intro n hn
    induction n with
    | zero => exact ⟨um1, fun x => by simp, hum1_good⟩
    | succ k ih =>
      rcases ih (by omega) with ⟨s, hs_iff, hs_good⟩
      by_cases ht2 : zty m (by omega) k = .t2
      · have hsub : (s : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; rcases (hs_iff x).mp hx with hx1 | ⟨i, _, _, rfl⟩
          · rw [← Finset.mem_coe, hum1_eq] at hx1
            simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
            rcases hx1 with ⟨r, ⟨hr1, hrm⟩, hxr⟩; exact ⟨r, ⟨hr1, by omega⟩, hxr⟩
          · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
        have hnot_zone : ∀ j, R.v j ∉ um1 := by
          intro j hj; rw [← Finset.mem_coe, hum1_eq] at hj
          exact zone_not_mem_zoneUnion_of_gt (by omega) (R.v_mem_zone j) hj
        have hnot_k : R.v k ∉ s := by
          intro hmem; rcases (hs_iff _).mp hmem with h1 | ⟨i, hik, _, heq⟩
          · exact hnot_zone k h1
          · exact R.v_ne_of_mod_ne (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) heq
        have hnot_t1 : ∀ j, zty m (by omega) j = .t1 → R.v j ∉ s := by
          intro j hjt hmem; rcases (hs_iff _).mp hmem with h1 | ⟨i, _, hi2, heq⟩
          · exact hnot_zone j h1
          · have hmod := R.v_eq_iff.mp heq
            have hty_eq : zty m (by omega) j = zty m (by omega) i := by
              rw [← zty_mod, ← R.N_eq, hmod, R.N_eq, zty_mod]
            rw [hjt, hi2] at hty_eq; cases hty_eq
        have hjoin := R.join_t2 hs_good hsub k ht2 hnot_k
          (hnot_t1 _ (by rw [R.N_eq]; exact zty_prev_t1_of_t2 hm k ht2)) (hnot_t1 _ (zty_no_adj_t2 hm k ht2))
        refine ⟨insert (R.v k) s, fun x => ?_, hjoin⟩
        rw [Finset.mem_insert, hs_iff]
        constructor
        · rintro (rfl | h1 | ⟨i, hi, hi2, rfl⟩)
          · exact Or.inr ⟨k, by omega, ht2, rfl⟩
          · exact Or.inl h1
          · exact Or.inr ⟨i, by omega, hi2, rfl⟩
        · rintro (h1 | ⟨i, hi, hi2, rfl⟩)
          · exact Or.inr (Or.inl h1)
          · by_cases hik : i = k
            · left; rw [hik]
            · exact Or.inr (Or.inr ⟨i, by omega, hi2, rfl⟩)
      · refine ⟨s, fun x => ?_, hs_good⟩
        rw [hs_iff]
        constructor
        · rintro (h1 | ⟨i, hi, hi2, rfl⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨i, by omega, hi2, rfl⟩
        · rintro (h1 | ⟨i, hi, hi2, rfl⟩)
          · exact Or.inl h1
          · by_cases hik : i = k
            · rw [hik] at hi2; exact absurd hi2 ht2
            · exact Or.inr ⟨i, by omega, hi2, rfl⟩
  exact hstep R.N le_rfl

/-- **Theorem 1.1 named step (Zone `Z₂`)**: `U₂` is finite and good. -/
theorem thm_1_1_step_zone2 (c₀ : sites37) :
    ∃ u2 : Finset H2, (u2 : Set H2) = ZoneUnion c₀ 2 ∧ IsGood c₀.1 u2 := by
  rcases thm_1_1_step_zone1 c₀ with ⟨u1, hu1_eq, hu1_good⟩
  let R := mkZoneRing c₀ 2 (by omega)
  have hN21 : R.N = 21 := by rw [R.N_eq]; decide
  have hzty2 : ∀ k, zty 2 (by omega) k = if k % 3 = 2 then .t2 else .t1 := by
    intro k
    have hfin : ∀ i : Fin (zoneWord 2).length, (zoneWord 2).get i = if i.1 % 3 = 2 then .t2 else .t1 := by decide
    have h := hfin ⟨k % (zoneWord 2).length, Nat.mod_lt _ (zoneWord_length_pos 2 (by omega))⟩
    have hmod3 : (k % (zoneWord 2).length) % 3 = k % 3 := by
      have hlen : (zoneWord 2).length = 21 := by decide
      rw [hlen]; omega
    simpa [zty, hmod3] using h
  rcases zone_phase_t2 c₀ (by omega) R hu1_eq hu1_good with ⟨sA, hsA_iff, hsA_good⟩
  have hnot_u1 : ∀ j, R.v j ∉ u1 := by
    intro j hj; rw [← Finset.mem_coe, hu1_eq] at hj
    exact zone_not_mem_zoneUnion_of_gt (by omega) (R.v_mem_zone j) hj
  -- Close first 6 doubles (blocks r = 0..5, vertices 3*r and 3*r + 1)!
  have hblocks : ∀ b ≤ 6,
      ∃ s : Finset H2,
        (∀ x, x ∈ s ↔ x ∈ u1 ∨ ∃ i < 21, (i % 3 = 2 ∨ i < 3 * b) ∧ x = R.v i) ∧
        IsGood c₀.1 s := by
    intro b hb
    induction b with
    | zero =>
      refine ⟨sA, fun x => ?_, hsA_good⟩
      rw [hsA_iff, hN21]
      constructor
      · rintro (h | ⟨i, hi, hi2, rfl⟩)
        · exact Or.inl h
        · rw [hzty2] at hi2; split_ifs at hi2 with h3
          exact Or.inr ⟨i, hi, Or.inl h3, rfl⟩
      · rintro (h | ⟨i, hi, hcond, rfl⟩)
        · exact Or.inl h
        · rcases hcond with h3 | hlt
          · exact Or.inr ⟨i, hi, by rw [hzty2]; simp [h3], rfl⟩
          · omega
    | succ r ih =>
      rcases ih (by omega) with ⟨s, hs_iff, hs_good⟩
      have hprev_sub : ZoneUnion c₀ 1 ⊆ (s : Set H2) := by
        intro x hx; rw [← hu1_eq] at hx; exact Finset.mem_coe.mpr ((hs_iff x).mpr (Or.inl hx))
      have hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ 2 := by
        intro x hx; rcases (hs_iff x).mp hx with hx1 | ⟨i, _, _, rfl⟩
        · rw [← Finset.mem_coe, hu1_eq] at hx1
          simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
          rcases hx1 with ⟨q, ⟨hq1, hq2⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
        · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
      have hnot_idx : ∀ j < 21, j % 3 ≠ 2 → 3 * r ≤ j → R.v j ∉ s := by
        intro j hj21 hj3 hjge hmem
        rcases (hs_iff _).mp hmem with h1 | ⟨i, hi21, hcond, heq⟩
        · exact hnot_u1 j h1
        · have hij : j = i := by
            have := R.v_eq_iff.mp heq; rw [hN21, Nat.mod_eq_of_lt hj21, Nat.mod_eq_of_lt hi21] at this; exact this
          subst hij; rcases hcond with h | h <;> omega
      -- Step 1: join v(3*r) via join_t1_one_ring (v(3*r + 1) ∉ s)!
      have hjoin1 := R.join_t1_one_ring hs_good hs_sub (3 * r)
        (by rw [hzty2]; simp [show 3 * r % 3 = 0 by omega])
        (hnot_idx (3 * r) (by omega) (by omega) (by omega))
        (Or.inr (hnot_idx (3 * r + 1) (by omega) (by omega) (by omega)))
      -- Step 2: join v(3*r + 1) via join_t1_tau3 (v(3*r + 3) ∉ s since r < 6)!
      set s1 := insert (R.v (3 * r)) s
      have hs1_sub : (s1 : Set H2) ⊆ ZoneUnion c₀ 2 := by
        intro x hx; simp only [s1, Finset.coe_insert, Set.mem_insert_iff] at hx
        rcases hx with rfl | hxs
        · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
        · exact hs_sub hxs
      have hprev_sub1 : ZoneUnion c₀ 1 ⊆ (s1 : Set H2) :=
        Set.Subset.trans hprev_sub (Finset.coe_subset.mpr (Finset.subset_insert _ _))
      have hnot_3r1 : R.v (3 * r + 1) ∉ s1 := by
        simp only [s1, Finset.mem_insert, not_or]
        exact ⟨R.v_ne_of_mod_ne (by rw [hN21, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          hnot_idx (3 * r + 1) (by omega) (by omega) (by omega)⟩
      have hnot_3r3 : R.v (3 * r + 1 + 2) ∉ s1 := by
        simp only [s1, Finset.mem_insert, not_or]
        exact ⟨R.v_ne_of_mod_ne (by rw [hN21, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          hnot_idx (3 * r + 3) (by omega) (by omega) (by omega)⟩
      have h3r_in : R.v (3 * r + 1 + R.N - 1) ∈ s1 := by
        rw [show 3 * r + 1 + R.N - 1 = 3 * r + R.N by omega, R.v_add_N]; exact Finset.mem_insert_self _ _
      have h3r2_in : R.v (3 * r + 1 + 1) ∈ s1 := by
        apply Finset.mem_insert_of_mem; rw [hs_iff]
        exact Or.inr ⟨3 * r + 2, by omega, Or.inl (by omega), rfl⟩
      have hjoin2 := R.join_t1_tau3 hjoin1 hprev_sub1 hs1_sub (3 * r + 1)
        (by rw [hzty2]; simp [show (3 * r + 1) % 3 = 1 by omega])
        hnot_3r1 h3r_in h3r2_in
        (Or.inl (by rw [hzty2, hN21]; simp))
        (Or.inr ⟨by rw [hzty2]; simp [show (3 * r + 1 + 1) % 3 = 2 by omega], hnot_3r3⟩)
      refine ⟨insert (R.v (3 * r + 1)) s1, fun x => ?_, hjoin2⟩
      simp only [s1, Finset.mem_insert, hs_iff]
      constructor
      · rintro (rfl | rfl | h1 | ⟨i, hi21, hcond, rfl⟩)
        · exact Or.inr ⟨3 * r + 1, by omega, Or.inr (by omega), rfl⟩
        · exact Or.inr ⟨3 * r, by omega, Or.inr (by omega), rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨i, hi21, by rcases hcond with h | h; exact Or.inl h; exact Or.inr (by omega), rfl⟩
      · rintro (h1 | ⟨i, hi21, hcond, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl h1))
        · rcases hcond with h3 | hlt
          · exact Or.inr (Or.inr (Or.inr ⟨i, hi21, Or.inl h3, rfl⟩))
          · by_cases hi0 : i = 3 * r
            · right; left; rw [hi0]
            · by_cases hi1 : i = 3 * r + 1
              · left; rw [hi1]
              · by_cases hi2 : i = 3 * r + 2
                · exact Or.inr (Or.inr (Or.inr ⟨i, hi21, Or.inl (by omega), rfl⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨i, hi21, Or.inr (by omega), rfl⟩))
  rcases hblocks 6 le_rfl with ⟨s6, hs6_iff, hs6_good⟩
  have hs6_sub : (s6 : Set H2) ⊆ ZoneUnion c₀ 2 := by
    intro x hx; rcases (hs6_iff x).mp hx with hx1 | ⟨i, _, _, rfl⟩
    · rw [← Finset.mem_coe, hu1_eq] at hx1
      simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
      rcases hx1 with ⟨q, ⟨hq1, hq2⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
  have hnot_18 : R.v 18 ∉ s6 := by
    intro hmem; rcases (hs6_iff _).mp hmem with h1 | ⟨i, hi21, hcond, heq⟩
    · exact hnot_u1 18 h1
    · have hij : 18 = i := by
        have := R.v_eq_iff.mp heq; rw [hN21, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hi21] at this; exact this
      subst hij; rcases hcond with h | h <;> omega
  have hnot_19 : R.v 19 ∉ s6 := by
    intro hmem; rcases (hs6_iff _).mp hmem with h1 | ⟨i, hi21, hcond, heq⟩
    · exact hnot_u1 19 h1
    · have hij : 19 = i := by
        have := R.v_eq_iff.mp heq; rw [hN21, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hi21] at this; exact this
      subst hij; rcases hcond with h | h <;> omega
  -- 7th double: join v 18 via join_t1_one_ring, then close v 19 via close_DD!
  have hjoin18 := R.join_t1_one_ring hs6_good hs6_sub 18 (by rw [hzty2]; decide) hnot_18 (Or.inr hnot_19)
  set s7 := insert (R.v 18) s6
  have hs7_sub : (s7 : Set H2) ⊆ ZoneUnion c₀ 2 := by
    intro x hx; simp only [s7, Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hxs
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
    · exact hs6_sub hxs
  have hprev7 : ZoneUnion c₀ 1 ⊆ (s7 : Set H2) := by
    intro x hx; rw [← hu1_eq] at hx
    exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem ((hs6_iff x).mpr (Or.inl hx)))
  have hnot_19_s7 : R.v 19 ∉ s7 := by
    simp only [s7, Finset.mem_insert, not_or]
    exact ⟨R.v_ne_of_mod_ne (by rw [hN21]; omega), hnot_19⟩
  have hjoin19 := R.close_DD (by omega) hjoin18 hprev7 hs7_sub 19
    (by rw [hzty2, hN21]; decide) (by rw [hzty2, hN21]; decide) (by rw [hzty2]; decide)
    (by rw [hzty2]; decide) (by rw [hzty2]; decide) (by rw [hzty2]; decide) (by rw [hzty2]; decide)
    hnot_19_s7
    (by rw [show 19 + R.N - 1 = 18 + R.N by omega, R.v_add_N]; exact Finset.mem_insert_self _ _)
    (by apply Finset.mem_insert_of_mem; rw [hs6_iff]; exact Or.inr ⟨20, by omega, Or.inl (by omega), rfl⟩)
    (by apply Finset.mem_insert_of_mem; rw [hs6_iff]
        refine Or.inr ⟨0, by omega, Or.inr (by omega), ?_⟩; rw [R.v_eq_iff, hN21])
    (by apply Finset.mem_insert_of_mem; rw [hs6_iff]
        refine Or.inr ⟨1, by omega, Or.inr (by omega), ?_⟩; rw [R.v_eq_iff, hN21])
  refine ⟨insert (R.v 19) s7, ?_, hjoin19⟩
  ext x
  simp only [s7, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hs6_iff]
  constructor
  · rintro (rfl | rfl | hx1 | ⟨i, _, _, rfl⟩)
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone 19)
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone 18)
    · rw [← Finset.mem_coe, hu1_eq] at hx1
      simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
      rcases hx1 with ⟨q, ⟨hq1, hq2⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
  · intro hx
    simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx
    rcases hx with ⟨q, ⟨hq1, hq2⟩, hxq⟩
    by_cases hq_eq : q = 1
    · right; right; left; rw [← Finset.mem_coe, hu1_eq]
      exact zone_subset_zoneUnion (by omega) le_rfl (hq_eq ▸ hxq)
    · have hq2' : q = 2 := by omega
      rw [hq2', ← R.set_eq] at hxq
      rcases List.mem_iff_get.mp hxq with ⟨idx, rfl⟩
      have hidx21 : idx.1 < 21 := by rw [← hN21]; exact idx.2
      have hv_eq : R.cyc.get idx = R.v idx.1 := by
        unfold ZoneRing.v; congr 1; exact Fin.ext (Nat.mod_eq_of_lt idx.2).symm
      rw [hv_eq]
      by_cases h19 : idx.1 = 19
      · left; rw [h19]
      · by_cases h18 : idx.1 = 18
        · right; left; rw [h18]
        · right; right; right
          refine ⟨idx.1, hidx21, ?_, rfl⟩
          by_cases h20 : idx.1 = 20
          · left; omega
          · right; omega

/-- Zone induction step `m - 1 → m` for ALL `m ≥ 3` (Phases A, B, C)! -/
lemma zone_step_ge_three (c₀ : sites37) {m : ℕ} (hm : 3 ≤ m)
    {um1 : Finset H2} (hum1_eq : (um1 : Set H2) = ZoneUnion c₀ (m - 1)) (hum1_good : IsGood c₀.1 um1) :
    ∃ um : Finset H2, (um : Set H2) = ZoneUnion c₀ m ∧ IsGood c₀.1 um := by
  let R := mkZoneRing c₀ m (by omega)
  have hN56 : 56 ≤ R.N := by rw [R.N_eq]; exact zoneWord_length_ge_56 m hm
  have hnot_um1 : ∀ j, R.v j ∉ um1 := by
    intro j hj; rw [← Finset.mem_coe, hum1_eq] at hj
    exact zone_not_mem_zoneUnion_of_gt (by omega) (R.v_mem_zone j) hj
  -- Phase A: Join all t2 vertices!
  rcases zone_phase_t2 c₀ (by omega) R hum1_eq hum1_good with ⟨sA, hsA_iff, hsA_good⟩
  -- Phase B: Close all S-D-S arcs!
  let sdsSet (n : ℕ) : Set H2 :=
    {x | ∃ a < n, isSDS m (by omega) a = true ∧
      (x = R.v a ∨ x = R.v (a + 2) ∨ x = R.v (a + 3) ∨ x = R.v (a + 5))}
  have hphaseB : ∀ n ≤ R.N,
      ∃ s : Finset H2, (∀ x, x ∈ s ↔ x ∈ sA ∨ x ∈ sdsSet n) ∧ IsGood c₀.1 s := by
    intro n hn
    induction n with
    | zero => exact ⟨sA, fun x => by simp [sdsSet], hsA_good⟩
    | succ k ih =>
      rcases ih (by omega) with ⟨s, hs_iff, hs_good⟩
      by_cases hk_sds : isSDS m (by omega) k = true
      · have hsk := isSDS_spec hk_sds
        have hnk := isSDS_next_six hm hk_sds
        have hprev_sub : ZoneUnion c₀ (m - 1) ⊆ (s : Set H2) := by
          intro x hx; rw [← hum1_eq] at hx
          exact Finset.mem_coe.mpr ((hs_iff x).mpr (Or.inl ((hsA_iff x).mpr (Or.inl hx))))
        have hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx
          rcases (hs_iff x).mp hx with hxA | ⟨a, _, _, hcases⟩
          · rcases (hsA_iff x).mp hxA with hx1 | ⟨i, _, _, rfl⟩
            · rw [← Finset.mem_coe, hum1_eq] at hx1
              simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
              rcases hx1 with ⟨q, ⟨hq1, hqm⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
            · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
          · rcases hcases with rfl | rfl | rfl | rfl <;> exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
        have hnot_sA_t1 : ∀ j, zty m (by omega) j = .t1 → R.v j ∉ sA := by
          intro j hjt hmem
          rcases (hsA_iff _).mp hmem with h1 | ⟨i, _, hi2, heq⟩
          · exact hnot_um1 j h1
          · have hmod := R.v_eq_iff.mp heq
            have hty_eq : zty m (by omega) j = zty m (by omega) i := by
              rw [← zty_mod, ← R.N_eq, hmod, R.N_eq, zty_mod]
            rw [hjt, hi2] at hty_eq; cases hty_eq
        have hin_sA_t2 : ∀ j, zty m (by omega) j = .t2 → R.v j ∈ sA := by
          intro j hjt; rw [hsA_iff]; right
          refine ⟨j % R.N, Nat.mod_lt _ R.N_pos, ?_, (R.v_mod j).symm⟩
          rw [R.N_eq, zty_mod]; exact hjt
        -- None of k-2, k, k+2, k+3, k+5, k+7 is in s!
        have hnot_s : ∀ j, zty m (by omega) j = .t1 →
            (∀ a < k, isSDS m (by omega) a = true →
              j % R.N ≠ a % R.N ∧ j % R.N ≠ (a + 2) % R.N ∧ j % R.N ≠ (a + 3) % R.N ∧ j % R.N ≠ (a + 5) % R.N) →
            R.v j ∉ s := by
          intro j hjt hdisj hmem
          rcases (hs_iff _).mp hmem with hA | ⟨a, hak, ha_sds, hcases⟩
          · exact hnot_sA_t1 j hjt hA
          · have hd := hdisj a hak ha_sds
            rcases hcases with heq | heq | heq | heq
            · exact hd.1 (R.v_eq_iff.mp heq)
            · exact hd.2.1 (R.v_eq_iff.mp heq)
            · exact hd.2.2.1 (R.v_eq_iff.mp heq)
            · exact hd.2.2.2 (R.v_eq_iff.mp heq)
        have hkm2_t1 : zty m (by omega) (k + R.N - 2) = .t1 := by
          have h1 := zty_prev_t1_of_t2 (by omega : 2 ≤ m) (k + R.N - 1) (by rw [R.N_eq]; exact hsk.1)
          have hmod : (k + R.N - 1 + (zoneWord m).length - 1) % (zoneWord m).length =
              (k + R.N - 2) % (zoneWord m).length := by
            rw [← R.N_eq, show k + R.N - 1 + R.N - 1 = (k + R.N - 2) + R.N by omega, Nat.add_mod_right]
          rw [← zty_mod, hmod, zty_mod] at h1; exact h1
        have hnot_km2 : R.v (k + R.N - 2) ∉ s := hnot_s _ hkm2_t1 fun a _ ha => by
          have hd := (isSDS_disjointness hm hk_sds ha).2.1
          simpa [R.N_eq] using hd
        have hnot_k : R.v k ∉ s := hnot_s _ hsk.2.1 fun a hak ha => by
          have hne : k % (zoneWord m).length ≠ a % (zoneWord m).length := by
            rw [← R.N_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          have hd := (isSDS_disjointness hm hk_sds ha).2.2 hne
          simpa [R.N_eq] using ⟨hne, hd.1, hd.2.1, hd.2.2.1⟩
        have hnot_k2 : R.v (k + 2) ∉ s := hnot_s _ hsk.2.2.2.1 fun a hak ha => by
          have hne : k % (zoneWord m).length ≠ a % (zoneWord m).length := by
            rw [← R.N_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          have hd := (isSDS_disjointness hm hk_sds ha).2.2 hne
          simpa [R.N_eq] using ⟨hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1⟩
        have hnot_k3 : R.v (k + 3) ∉ s := hnot_s _ hsk.2.2.2.2.1 fun a hak ha => by
          have hne : k % (zoneWord m).length ≠ a % (zoneWord m).length := by
            rw [← R.N_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          have hd := (isSDS_disjointness hm hk_sds ha).2.2 hne
          simpa [R.N_eq] using ⟨hd.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.1⟩
        have hnot_k5 : R.v (k + 5) ∉ s := hnot_s _ hsk.2.2.2.2.2.2.1 fun a hak ha => by
          have hne : k % (zoneWord m).length ≠ a % (zoneWord m).length := by
            rw [← R.N_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          have hd := (isSDS_disjointness hm hk_sds ha).2.2 hne
          simpa [R.N_eq] using ⟨hd.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
        have hnot_k7 : R.v (k + 7) ∉ s := hnot_s _ hnk.1 fun a _ ha => by
          have hd := (isSDS_disjointness hm hk_sds ha).1
          simpa [R.N_eq] using hd
        have hmod10 : ∀ a b : ℕ, a < 10 → b < 10 → a ≠ b → (k + a) % R.N ≠ (k + b) % R.N := by
          intro a b ha hb hab heq
          have hsub := congrArg (fun t => (t + (R.N - k % R.N)) % R.N) heq
          have hsimp : ∀ d < 10, ((k + d) % R.N + (R.N - k % R.N)) % R.N = d := by
            intro d hd
            have hlt := Nat.mod_lt k R.N_pos
            rw [Nat.mod_add_mod]
            have h1 : k + d + (R.N - k % R.N) = d + (k / R.N + 1) * R.N := by
              have := Nat.div_add_mod' k R.N; rw [add_mul, one_mul]; omega
            rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsimp a ha, hsimp b hb] at hsub; exact hab hsub
        -- 1. Join S₁ = v k via join_t1_tau3!
        have hjoin1 := R.join_t1_tau3 hs_good hprev_sub hs_sub k hsk.2.1 hnot_k
          ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ (by rw [R.N_eq]; exact hsk.1))))
          ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ hsk.2.2.1)))
          (Or.inr ⟨by rw [R.N_eq]; exact hsk.1, hnot_km2⟩)
          (Or.inr ⟨hsk.2.2.1, hnot_k2⟩)
        set s1 := insert (R.v k) s
        have hs1_sub : (s1 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s1, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs_sub h
        have hprev1 : ZoneUnion c₀ (m - 1) ⊆ (s1 : Set H2) :=
          Set.Subset.trans hprev_sub (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- 2. Join S₂ = v(k + 5) via join_t1_tau3!
        have hnot_k5_1 : R.v (k + 5) ∉ s1 := by
          simp only [s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (by simpa using hmod10 5 0 (by omega) (by omega) (by omega)), hnot_k5⟩
        have hnot_k3_1 : R.v (k + 5 + R.N - 2) ∉ s1 := by
          rw [show k + 5 + R.N - 2 = (k + 3) + R.N by omega, R.v_add_N]
          simp only [s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (by simpa using hmod10 3 0 (by omega) (by omega) (by omega)), hnot_k3⟩
        have hnot_k7_1 : R.v (k + 5 + 2) ∉ s1 := by
          rw [show k + 5 + 2 = k + 7 by omega]
          simp only [s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (by simpa using hmod10 7 0 (by omega) (by omega) (by omega)), hnot_k7⟩
        have hjoin2 := R.join_t1_tau3 hjoin1 hprev1 hs1_sub (k + 5) hsk.2.2.2.2.2.2.1 hnot_k5_1
          (Finset.mem_insert_of_mem ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ (by
            rw [R.N_eq, show k + 5 + (zoneWord m).length - 1 = (k + 4) + (zoneWord m).length by omega, zty_add_len]
            exact hsk.2.2.2.2.2.1)))))
          (Finset.mem_insert_of_mem ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ hsk.2.2.2.2.2.2.2))))
          (Or.inr ⟨by rw [R.N_eq, show k + 5 + (zoneWord m).length - 1 = (k + 4) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.2.2.2.1,
            hnot_k3_1⟩)
          (Or.inr ⟨hsk.2.2.2.2.2.2.2, hnot_k7_1⟩)
        set s2 := insert (R.v (k + 5)) s1
        have hs2_sub : (s2 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s2, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs1_sub h
        have hprev2 : ZoneUnion c₀ (m - 1) ⊆ (s2 : Set H2) :=
          Set.Subset.trans hprev1 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- 3. Join d₁ = v(k + 2) via join_t1_one_ring (d₂ = v(k + 3) ∉ s2)!
        have hnot_k2_2 : R.v (k + 2) ∉ s2 := by
          simp only [s2, s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod10 2 5 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (by simpa using hmod10 2 0 (by omega) (by omega) (by omega)), hnot_k2⟩
        have hnot_k3_2 : R.v (k + 2 + 1) ∉ s2 := by
          rw [show k + 2 + 1 = k + 3 by omega]
          simp only [s2, s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod10 3 5 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (by simpa using hmod10 3 0 (by omega) (by omega) (by omega)), hnot_k3⟩
        have hjoin3 := R.join_t1_one_ring hjoin2 hs2_sub (k + 2) hsk.2.2.2.1 hnot_k2_2 (Or.inr hnot_k3_2)
        set s3 := insert (R.v (k + 2)) s2
        have hs3_sub : (s3 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s3, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs2_sub h
        have hprev3 : ZoneUnion c₀ (m - 1) ⊆ (s3 : Set H2) :=
          Set.Subset.trans hprev2 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- 4. Close d₂ = v(k + 3) via close_SDS (c₉ = v(k + 7) ∉ s3)!
        have hnot_k3_3 : R.v (k + 3) ∉ s3 := by
          simp only [s3, s2, s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod10 3 2 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod10 3 5 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (by simpa using hmod10 3 0 (by omega) (by omega) (by omega)), hnot_k3⟩
        have hnot_k7_3 : R.v (k + 3 + 4) ∉ s3 := by
          rw [show k + 3 + 4 = k + 7 by omega]
          simp only [s3, s2, s1, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod10 7 2 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod10 7 5 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (by simpa using hmod10 7 0 (by omega) (by omega) (by omega)), hnot_k7⟩
        have hjoin4 := R.close_SDS hm hjoin3 hprev3 hs3_sub (k + 3)
          (by rw [R.N_eq, show k + 3 + (zoneWord m).length - 2 = (k + 1) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.1)
          (by rw [R.N_eq, show k + 3 + (zoneWord m).length - 1 = (k + 2) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.2.1)
          hsk.2.2.2.2.1 hsk.2.2.2.2.2.1 hsk.2.2.2.2.2.2.1 hsk.2.2.2.2.2.2.2
          hnot_k3_3 hnot_k7_3
          (by rw [show k + 3 + R.N - 1 = (k + 2) + R.N by omega, R.v_add_N]; exact Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ hsk.2.2.2.2.2.1))))))
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            ((hs_iff _).mpr (Or.inl (hin_sA_t2 _ hsk.2.2.2.2.2.2.2))))))
        refine ⟨insert (R.v (k + 3)) s3, fun x => ?_, hjoin4⟩
        simp only [s3, s2, s1, Finset.mem_insert, hs_iff, sdsSet, Set.mem_ofPred_eq]
        constructor
        · rintro (rfl | rfl | rfl | rfl | hxA | ⟨a, hak, ha, hcases⟩)
          · exact Or.inr ⟨k, by omega, hk_sds, Or.inr (Or.inr (Or.inl rfl))⟩
          · exact Or.inr ⟨k, by omega, hk_sds, Or.inr (Or.inl rfl)⟩
          · exact Or.inr ⟨k, by omega, hk_sds, Or.inr (Or.inr (Or.inr rfl))⟩
          · exact Or.inr ⟨k, by omega, hk_sds, Or.inl rfl⟩
          · exact Or.inl hxA
          · exact Or.inr ⟨a, by omega, ha, hcases⟩
        · rintro (hxA | ⟨a, ha_lt, ha, hcases⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxA))))
          · by_cases hak : a = k
            · rw [hak] at hcases
              rcases hcases with rfl | rfl | rfl | rfl
              · right; right; right; left; rfl
              · right; left; rfl
              · left; rfl
              · right; right; left; rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, by omega, ha, hcases⟩))))
      · refine ⟨s, fun x => ?_, hs_good⟩
        simp only [hs_iff, sdsSet, Set.mem_ofPred_eq]
        constructor
        · rintro (hA | ⟨a, hak, ha, hc⟩); exact Or.inl hA; exact Or.inr ⟨a, by omega, ha, hc⟩
        · rintro (hA | ⟨a, ha_lt, ha, hc⟩)
          · exact Or.inl hA
          · by_cases hak : a = k
            · rw [hak] at ha; exact absurd ha hk_sds
            · exact Or.inr ⟨a, by omega, ha, hc⟩
  rcases hphaseB R.N le_rfl with ⟨sB, hsB_iff, hsB_good⟩
  -- Phase C: Close all S-D-D-S arcs!
  let sddsSet (n : ℕ) : Set H2 :=
    {x | ∃ a < n, isSDDS m (by omega) a = true ∧
      (x = R.v a ∨ x = R.v (a + 2) ∨ x = R.v (a + 3) ∨ x = R.v (a + 5) ∨ x = R.v (a + 6) ∨ x = R.v (a + 8))}
  have hphaseC : ∀ n ≤ R.N,
      ∃ s : Finset H2, (∀ x, x ∈ s ↔ x ∈ sB ∨ x ∈ sddsSet n) ∧ IsGood c₀.1 s := by
    intro n hn
    induction n with
    | zero => exact ⟨sB, fun x => by simp [sddsSet], hsB_good⟩
    | succ k ih =>
      rcases ih (by omega) with ⟨s, hs_iff, hs_good⟩
      by_cases hk_sdds : isSDDS m (by omega) k = true
      · have hsk := isSDDS_spec hk_sdds
        have hprev_sub : ZoneUnion c₀ (m - 1) ⊆ (s : Set H2) := by
          intro x hx; rw [← hum1_eq] at hx
          exact Finset.mem_coe.mpr ((hs_iff x).mpr (Or.inl ((hsB_iff x).mpr (Or.inl ((hsA_iff x).mpr (Or.inl hx))))))
        have hs_sub : (s : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx
          rcases (hs_iff x).mp hx with hxB | ⟨a, _, _, hc⟩
          · rcases (hsB_iff x).mp hxB with hxA | ⟨a, _, _, hc⟩
            · rcases (hsA_iff x).mp hxA with hx1 | ⟨i, _, _, rfl⟩
              · rw [← Finset.mem_coe, hum1_eq] at hx1
                simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
                rcases hx1 with ⟨q, ⟨hq1, hqm⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
              · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
            · rcases hc with rfl | rfl | rfl | rfl <;> exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
          · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
        have hin_s_t2 : ∀ j, zty m (by omega) j = .t2 → R.v j ∈ s := by
          intro j hjt
          apply (hs_iff _).mpr; left; apply (hsB_iff _).mpr; left; apply (hsA_iff _).mpr; right
          refine ⟨j % R.N, Nat.mod_lt _ R.N_pos, ?_, (R.v_mod j).symm⟩
          rw [R.N_eq, zty_mod]; exact hjt
        have hnot_sA_t1 : ∀ j, zty m (by omega) j = .t1 → R.v j ∉ sA := by
          intro j hjt hmem
          rcases (hsA_iff _).mp hmem with h1 | ⟨i, _, hi2, heq⟩
          · exact hnot_um1 j h1
          · have hmod := R.v_eq_iff.mp heq
            have hty_eq : zty m (by omega) j = zty m (by omega) i := by
              rw [← zty_mod, ← R.N_eq, hmod, R.N_eq, zty_mod]
            rw [hjt, hi2] at hty_eq; cases hty_eq
        -- Helper: all four double vertices {k+2, k+3, k+5, k+6} are NOT in s!
        have hnot_dbl : ∀ x ∈ ({k + 2, k + 3, k + 5, k + 6} : Finset ℕ), R.v x ∉ s := by
          intro x hx hmem
          have hxt : zty m (by omega) x = .t1 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact hsk.2.2.2.1
            · exact hsk.2.2.2.2.1
            · exact hsk.2.2.2.2.2.2.1
            · exact hsk.2.2.2.2.2.2.2.1
          rcases (hs_iff _).mp hmem with hxB | ⟨a, hak, ha, hc⟩
          · rcases (hsB_iff _).mp hxB with hxA | ⟨a, _, ha, hc⟩
            · exact hnot_sA_t1 x hxt hxA
            · have hd := (isSDDS_disjoint_doubles hm hk_sdds).1 ha x hx
              rcases hc with heq | heq | heq | heq
              · exact hd a (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
              · exact hd (a + 2) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
              · exact hd (a + 3) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
              · exact hd (a + 5) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
          · have hne : k % (zoneWord m).length ≠ a % (zoneWord m).length := by
              rw [← R.N_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
            have hd := (isSDDS_disjoint_doubles hm hk_sdds).2 ha hne x hx
            rcases hc with heq | heq | heq | heq | heq | heq
            · exact hd a (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
            · exact hd (a + 2) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
            · exact hd (a + 3) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
            · exact hd (a + 5) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
            · exact hd (a + 6) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
            · exact hd (a + 8) (by simp) (by rw [← R.N_eq]; exact R.v_eq_iff.mp heq)
        -- Helper: if a single p (`t2, p, t2`) is NOT in s, then neither p-2 nor p+2 is in s!
        have hsingle_nbrs_out : ∀ p : ℕ,
            zty m (by omega) (p + R.N - 1) = .t2 → zty m (by omega) p = .t1 → zty m (by omega) (p + 1) = .t2 →
            R.v p ∉ s → R.v (p + R.N - 2) ∉ s ∧ R.v (p + 2) ∉ s := by
          intro p hpm hp0 hpp hp_not
          have hpm_t1 : zty m (by omega) (p + R.N - 2) = .t1 := by
            have h1 := zty_prev_t1_of_t2 (by omega) (p + R.N - 1) hpm
            have hmod : (p + R.N - 1 + (zoneWord m).length - 1) % (zoneWord m).length =
                (p + R.N - 2) % (zoneWord m).length := by
              rw [← R.N_eq, show p + R.N - 1 + R.N - 1 = (p + R.N - 2) + R.N by omega, Nat.add_mod_right]
            rw [← zty_mod, hmod, zty_mod] at h1; exact h1
          have hpp_t1 : zty m (by omega) (p + 2) = .t1 := zty_no_adj_t2 (by omega) (p + 1) hpp
          constructor
          · intro hmem
            rcases (hs_iff _).mp hmem with hB | ⟨a, hak, ha, hc⟩
            · rcases (hsB_iff _).mp hB with hA | ⟨a, haN, ha, hc⟩
              · exact hnot_sA_t1 _ hpm_t1 hA
              · have hmem_fin : (p + (zoneWord m).length - 2) % (zoneWord m).length ∈
                    ({a % (zoneWord m).length, (a + 2) % (zoneWord m).length,
                      (a + 3) % (zoneWord m).length, (a + 5) % (zoneWord m).length} : Finset ℕ) := by
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  rcases hc with heq | heq | heq | heq
                  · left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; right; right; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                rcases (single_nbr2_in_arc_imp_self hm (by rw [← R.N_eq]; exact hpm) hp0 hpp).1 ha (Or.inl hmem_fin) with hp_a | hp_a5
                · exact hp_not ((hs_iff _).mpr (Or.inl ((hsB_iff _).mpr (Or.inr ⟨a, haN, ha, Or.inl (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a))⟩))))
                · exact hp_not ((hs_iff _).mpr (Or.inl ((hsB_iff _).mpr (Or.inr ⟨a, haN, ha, Or.inr (Or.inr (Or.inr (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a5))))⟩))))
            · have hmem_fin : (p + (zoneWord m).length - 2) % (zoneWord m).length ∈
                  ({a % (zoneWord m).length, (a + 2) % (zoneWord m).length, (a + 3) % (zoneWord m).length,
                    (a + 5) % (zoneWord m).length, (a + 6) % (zoneWord m).length, (a + 8) % (zoneWord m).length} : Finset ℕ) := by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hc with heq | heq | heq | heq | heq | heq
                · left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; right; right; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
              rcases (single_nbr2_in_arc_imp_self hm (by rw [← R.N_eq]; exact hpm) hp0 hpp).2 ha (Or.inl hmem_fin) with hp_a | hp_a8
              · exact hp_not ((hs_iff _).mpr (Or.inr ⟨a, hak, ha, Or.inl (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a))⟩))
              · exact hp_not ((hs_iff _).mpr (Or.inr ⟨a, hak, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a8))))))⟩))
          · intro hmem
            rcases (hs_iff _).mp hmem with hB | ⟨a, hak, ha, hc⟩
            · rcases (hsB_iff _).mp hB with hA | ⟨a, haN, ha, hc⟩
              · exact hnot_sA_t1 _ hpp_t1 hA
              · have hmem_fin : (p + 2) % (zoneWord m).length ∈
                    ({a % (zoneWord m).length, (a + 2) % (zoneWord m).length,
                      (a + 3) % (zoneWord m).length, (a + 5) % (zoneWord m).length} : Finset ℕ) := by
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  rcases hc with heq | heq | heq | heq
                  · left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                  · right; right; right; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                rcases (single_nbr2_in_arc_imp_self hm (by rw [← R.N_eq]; exact hpm) hp0 hpp).1 ha (Or.inr hmem_fin) with hp_a | hp_a5
                · exact hp_not ((hs_iff _).mpr (Or.inl ((hsB_iff _).mpr (Or.inr ⟨a, haN, ha, Or.inl (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a))⟩))))
                · exact hp_not ((hs_iff _).mpr (Or.inl ((hsB_iff _).mpr (Or.inr ⟨a, haN, ha, Or.inr (Or.inr (Or.inr (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a5))))⟩))))
            · have hmem_fin : (p + 2) % (zoneWord m).length ∈
                  ({a % (zoneWord m).length, (a + 2) % (zoneWord m).length, (a + 3) % (zoneWord m).length,
                    (a + 5) % (zoneWord m).length, (a + 6) % (zoneWord m).length, (a + 8) % (zoneWord m).length} : Finset ℕ) := by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hc with heq | heq | heq | heq | heq | heq
                · left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; right; left; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
                · right; right; right; right; right; rw [← R.N_eq]; exact R.v_eq_iff.mp heq
              rcases (single_nbr2_in_arc_imp_self hm (by rw [← R.N_eq]; exact hpm) hp0 hpp).2 ha (Or.inr hmem_fin) with hp_a | hp_a8
              · exact hp_not ((hs_iff _).mpr (Or.inr ⟨a, hak, ha, Or.inl (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a))⟩))
              · exact hp_not ((hs_iff _).mpr (Or.inr ⟨a, hak, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (R.v_eq_iff.mpr (by rw [R.N_eq]; exact hp_a8))))))⟩))
        have hmod12 : ∀ a b : ℕ, a < 12 → b < 12 → a ≠ b → (k + a) % R.N ≠ (k + b) % R.N := by
          intro a b ha hb hab heq
          have hsub := congrArg (fun t => (t + (R.N - k % R.N)) % R.N) heq
          have hsimp : ∀ d < 12, ((k + d) % R.N + (R.N - k % R.N)) % R.N = d := by
            intro d hd
            have hlt := Nat.mod_lt k R.N_pos
            rw [Nat.mod_add_mod]
            have h1 : k + d + (R.N - k % R.N) = d + (k / R.N + 1) * R.N := by
              have := Nat.div_add_mod' k R.N; rw [add_mul, one_mul]; omega
            rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsimp a ha, hsimp b hb] at hsub; exact hab hsub
        -- Step 1: ensure S₁ = v k ∈ s1 (either already in s, or join via join_t1_tau3!)
        have hs1_ex : ∃ s1 : Finset H2, s1 = insert (R.v k) s ∧ IsGood c₀.1 s1 := by
          by_cases hkin : R.v k ∈ s
          · exact ⟨s, (Finset.insert_eq_of_mem hkin).symm, hs_good⟩
          · have hnbrs := hsingle_nbrs_out k (by rw [R.N_eq]; exact hsk.1) hsk.2.1 hsk.2.2.1 hkin
            exact ⟨insert (R.v k) s, rfl, R.join_t1_tau3 hs_good hprev_sub hs_sub k hsk.2.1 hkin
              (hin_s_t2 _ (by rw [R.N_eq]; exact hsk.1)) (hin_s_t2 _ hsk.2.2.1)
              (Or.inr ⟨by rw [R.N_eq]; exact hsk.1, hnbrs.1⟩) (Or.inr ⟨hsk.2.2.1, hnbrs.2⟩)⟩
        rcases hs1_ex with ⟨s1, hs1_eq, hs1_good⟩
        have hs1_sub : (s1 : Set H2) ⊆ ZoneUnion c₀ m := by
          rw [hs1_eq]; intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs_sub h
        have hprev1 : ZoneUnion c₀ (m - 1) ⊆ (s1 : Set H2) := by
          rw [hs1_eq]; exact Set.Subset.trans hprev_sub (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- Step 2: ensure S₂ = v(k + 8) ∈ s2 (either already in s1, or join via join_t1_tau3!)
        have hs2_ex : ∃ s2 : Finset H2, s2 = insert (R.v (k + 8)) s1 ∧ IsGood c₀.1 s2 := by
          by_cases hk8in : R.v (k + 8) ∈ s1
          · exact ⟨s1, (Finset.insert_eq_of_mem hk8in).symm, hs1_good⟩
          · have hk8_not_s : R.v (k + 8) ∉ s := fun h => hk8in (by rw [hs1_eq]; exact Finset.mem_insert_of_mem h)
            have h8m : zty m (by omega) (k + 8 + R.N - 1) = .t2 := by
              rw [R.N_eq, show k + 8 + (zoneWord m).length - 1 = (k + 7) + (zoneWord m).length by omega, zty_add_len]
              exact hsk.2.2.2.2.2.2.2.2.1
            have hnbrs := hsingle_nbrs_out (k + 8) h8m hsk.2.2.2.2.2.2.2.2.2.1 hsk.2.2.2.2.2.2.2.2.2.2 hk8_not_s
            have hnot_k6_1 : R.v (k + 8 + R.N - 2) ∉ s1 := by
              rw [hs1_eq, show k + 8 + R.N - 2 = (k + 6) + R.N by omega, R.v_add_N]
              simp only [Finset.mem_insert, not_or]
              exact ⟨R.v_ne_of_mod_ne (by simpa using hmod12 6 0 (by omega) (by omega) (by omega)), hnot_dbl (k + 6) (by simp)⟩
            have hnot_k10_1 : R.v (k + 8 + 2) ∉ s1 := by
              rw [hs1_eq]; simp only [Finset.mem_insert, not_or]
              exact ⟨R.v_ne_of_mod_ne (by simpa using hmod12 10 0 (by omega) (by omega) (by omega)), hnbrs.2⟩
            exact ⟨insert (R.v (k + 8)) s1, rfl, R.join_t1_tau3 hs1_good hprev1 hs1_sub (k + 8)
              hsk.2.2.2.2.2.2.2.2.2.1 hk8in
              (by rw [hs1_eq]; exact Finset.mem_insert_of_mem (hin_s_t2 _ h8m))
              (by rw [hs1_eq]; exact Finset.mem_insert_of_mem (hin_s_t2 _ hsk.2.2.2.2.2.2.2.2.2.2))
              (Or.inr ⟨h8m, hnot_k6_1⟩) (Or.inr ⟨hsk.2.2.2.2.2.2.2.2.2.2, hnot_k10_1⟩)⟩
        rcases hs2_ex with ⟨s2, hs2_eq, hs2_good⟩
        have hs2_sub : (s2 : Set H2) ⊆ ZoneUnion c₀ m := by
          rw [hs2_eq]; intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs1_sub h
        have hprev2 : ZoneUnion c₀ (m - 1) ⊆ (s2 : Set H2) := by
          rw [hs2_eq]; exact Set.Subset.trans hprev1 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        have hnot_dbl_2 : ∀ d ∈ ({2, 3, 5, 6} : Finset ℕ), R.v (k + d) ∉ s2 := by
          intro d hd
          rw [hs2_eq, hs1_eq]; simp only [Finset.mem_insert, not_or]
          have hd_lt : d < 12 ∧ d ≠ 8 ∧ d ≠ 0 := by simp at hd; omega
          refine ⟨R.v_ne_of_mod_ne (hmod12 d 8 hd_lt.1 (by omega) hd_lt.2.1),
            R.v_ne_of_mod_ne (by simpa using hmod12 d 0 hd_lt.1 (by omega) hd_lt.2.2),
            hnot_dbl (k + d) (by simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢; rcases hd with rfl | rfl | rfl | rfl <;> simp)⟩
        -- Step 3: join d₁ = v(k + 2) via join_t1_one_ring (d₂ = v(k + 3) ∉ s2)!
        have hjoin3 := R.join_t1_one_ring hs2_good hs2_sub (k + 2) hsk.2.2.2.1
          (hnot_dbl_2 2 (by simp)) (Or.inr (by rw [show k + 2 + 1 = k + 3 by omega]; exact hnot_dbl_2 3 (by simp)))
        set s3 := insert (R.v (k + 2)) s2
        have hs3_sub : (s3 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s3, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs2_sub h
        have hprev3 : ZoneUnion c₀ (m - 1) ⊆ (s3 : Set H2) :=
          Set.Subset.trans hprev2 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- Step 4: join d₄ = v(k + 6) via join_t1_one_ring (d₃ = v(k + 5) ∉ s3)!
        have hnot_k6_3 : R.v (k + 6) ∉ s3 := by
          simp only [s3, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod12 6 2 (by omega) (by omega) (by omega)), hnot_dbl_2 6 (by simp)⟩
        have hnot_k5_3 : R.v (k + 6 + R.N - 1) ∉ s3 := by
          rw [show k + 6 + R.N - 1 = (k + 5) + R.N by omega, R.v_add_N]
          simp only [s3, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod12 5 2 (by omega) (by omega) (by omega)), hnot_dbl_2 5 (by simp)⟩
        have hjoin4 := R.join_t1_one_ring hjoin3 hs3_sub (k + 6) hsk.2.2.2.2.2.2.2.1
          hnot_k6_3 (Or.inl hnot_k5_3)
        set s4 := insert (R.v (k + 6)) s3
        have hs4_sub : (s4 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s4, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs3_sub h
        have hprev4 : ZoneUnion c₀ (m - 1) ⊆ (s4 : Set H2) :=
          Set.Subset.trans hprev3 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- Step 5: join d₃ = v(k + 5) via join_t1_tau3 (d₂ = v(k + 3) ∉ s4)!
        have hnot_k5_4 : R.v (k + 5) ∉ s4 := by
          simp only [s4, s3, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod12 5 6 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod12 5 2 (by omega) (by omega) (by omega)), hnot_dbl_2 5 (by simp)⟩
        have hnot_k3_4 : R.v (k + 5 + R.N - 2) ∉ s4 := by
          rw [show k + 5 + R.N - 2 = (k + 3) + R.N by omega, R.v_add_N]
          simp only [s4, s3, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod12 3 6 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod12 3 2 (by omega) (by omega) (by omega)), hnot_dbl_2 3 (by simp)⟩
        have hjoin5 := R.join_t1_tau3 hjoin4 hprev4 hs4_sub (k + 5) hsk.2.2.2.2.2.2.1 hnot_k5_4
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by rw [hs2_eq, hs1_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (hin_s_t2 _ (by rw [R.N_eq, show k + 5 + (zoneWord m).length - 1 = (k + 4) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.2.2.2.1))))))
          (Finset.mem_insert_self _ _)
          (Or.inr ⟨by rw [R.N_eq, show k + 5 + (zoneWord m).length - 1 = (k + 4) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.2.2.2.1,
            hnot_k3_4⟩)
          (Or.inl hsk.2.2.2.2.2.2.2.1)
        set s5 := insert (R.v (k + 5)) s4
        have hs5_sub : (s5 : Set H2) ⊆ ZoneUnion c₀ m := by
          intro x hx; simp only [s5, Finset.coe_insert, Set.mem_insert_iff] at hx
          rcases hx with rfl | h; exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _); exact hs4_sub h
        have hprev5 : ZoneUnion c₀ (m - 1) ⊆ (s5 : Set H2) :=
          Set.Subset.trans hprev4 (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        -- Step 6: close d₂ = v(k + 3) via close_DD!
        have hnot_k3_5 : R.v (k + 3) ∉ s5 := by
          simp only [s5, s4, s3, Finset.mem_insert, not_or]
          exact ⟨R.v_ne_of_mod_ne (hmod12 3 5 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod12 3 6 (by omega) (by omega) (by omega)),
            R.v_ne_of_mod_ne (hmod12 3 2 (by omega) (by omega) (by omega)), hnot_dbl_2 3 (by simp)⟩
        have hjoin6 := R.close_DD (by omega) hjoin5 hprev5 hs5_sub (k + 3)
          (by rw [R.N_eq, show k + 3 + (zoneWord m).length - 2 = (k + 1) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.1)
          (by rw [R.N_eq, show k + 3 + (zoneWord m).length - 1 = (k + 2) + (zoneWord m).length by omega, zty_add_len]; exact hsk.2.2.2.1)
          hsk.2.2.2.2.1 hsk.2.2.2.2.2.1 hsk.2.2.2.2.2.2.1 hsk.2.2.2.2.2.2.2.1 hsk.2.2.2.2.2.2.2.2.1
          hnot_k3_5
          (by rw [show k + 3 + R.N - 1 = (k + 2) + R.N by omega, R.v_add_N]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by
            rw [hs2_eq, hs1_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hin_s_t2 _ hsk.2.2.2.2.2.1))))))
          (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        refine ⟨insert (R.v (k + 3)) s5, fun x => ?_, hjoin6⟩
        simp only [s5, s4, s3, hs2_eq, hs1_eq, Finset.mem_insert, hs_iff, sddsSet, Set.mem_ofPred_eq]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl | rfl | hxB | ⟨a, hak, ha, hc⟩)
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inr (Or.inr (Or.inl rfl))⟩
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inr (Or.inl rfl)⟩
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
          · exact Or.inr ⟨k, by omega, hk_sdds, Or.inl rfl⟩
          · exact Or.inl hxB
          · exact Or.inr ⟨a, by omega, ha, hc⟩
        · rintro (hxB | ⟨a, ha_lt, ha, hc⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxB))))))
          · by_cases hak : a = k
            · rw [hak] at hc
              rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
              · right; right; right; right; right; left; rfl
              · right; right; right; left; rfl
              · left; rfl
              · right; left; rfl
              · right; right; left; rfl
              · right; right; right; right; left; rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, by omega, ha, hc⟩))))))
      · refine ⟨s, fun x => ?_, hs_good⟩
        simp only [hs_iff, sddsSet, Set.mem_ofPred_eq]
        constructor
        · rintro (hB | ⟨a, hak, ha, hc⟩); exact Or.inl hB; exact Or.inr ⟨a, by omega, ha, hc⟩
        · rintro (hB | ⟨a, ha_lt, ha, hc⟩)
          · exact Or.inl hB
          · by_cases hak : a = k
            · rw [hak] at ha; exact absurd ha hk_sdds
            · exact Or.inr ⟨a, by omega, ha, hc⟩
  rcases hphaseC R.N le_rfl with ⟨sC, hsC_iff, hsC_good⟩
  refine ⟨sC, ?_, hsC_good⟩
  ext x
  rw [Finset.mem_coe, hsC_iff, hsB_iff, hsA_iff]
  constructor
  · rintro (((hx1 | ⟨i, _, _, rfl⟩) | ⟨a, _, _, hc⟩) | ⟨a, _, _, hc⟩)
    · rw [← Finset.mem_coe, hum1_eq] at hx1
      simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx1 ⊢
      rcases hx1 with ⟨q, ⟨hq1, hqm⟩, hxq⟩; exact ⟨q, ⟨hq1, by omega⟩, hxq⟩
    · exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone i)
    · rcases hc with rfl | rfl | rfl | rfl <;> exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact zone_subset_zoneUnion (by omega) le_rfl (R.v_mem_zone _)
  · intro hx
    simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hx
    rcases hx with ⟨q, ⟨hq1, hqm⟩, hxq⟩
    by_cases hqm' : q ≤ m - 1
    · left; left; left; rw [← Finset.mem_coe, hum1_eq]
      exact zone_subset_zoneUnion hq1 hqm' hxq
    · have hq_eq : q = m := by omega
      rw [hq_eq, ← R.set_eq] at hxq
      rcases List.mem_iff_get.mp hxq with ⟨idx, rfl⟩
      have hv_eq : R.cyc.get idx = R.v idx.1 := by
        unfold ZoneRing.v; congr 1; exact Fin.ext (Nat.mod_eq_of_lt idx.2).symm
      rw [hv_eq]
      cases ht : zty m (by omega) idx.1 with
      | t2 => left; left; right; exact ⟨idx.1, idx.2, ht, rfl⟩
      | t1 =>
        rcases zoneWord_t1_covered hm idx.1 ht with ⟨k, hkN, hk_sds, hmem⟩ | ⟨k, hkN, hk_sdds, hmem⟩
        · left; right
          refine ⟨k, by rw [R.N_eq]; exact hkN, hk_sds, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h
          · left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; right; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
        · right
          refine ⟨k, by rw [R.N_eq]; exact hkN, hk_sdds, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h | h | h
          · left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; right; right; left; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)
          · right; right; right; right; right; exact R.v_eq_iff.mpr (by rw [R.N_eq]; exact h)

/-- **Theorem 1.1 named step (Zone `Z_m`, `m ≥ 1`)**: For every `m ≥ 1`, `U_m` is finite and good. -/
theorem thm_1_1_step_zone_m (c₀ : sites37) (m : ℕ) (hm : 1 ≤ m) :
    ∃ um : Finset H2, (um : Set H2) = ZoneUnion c₀ m ∧ IsGood c₀.1 um := by
  induction m, hm using Nat.le_induction with
  | base => exact thm_1_1_step_zone1 c₀
  | succ k hk ih =>
    rcases ih with ⟨uk, huk_eq, huk_good⟩
    by_cases hk1 : k = 1
    · subst hk1; exact thm_1_1_step_zone2 c₀
    · exact zone_step_ge_three c₀ (by omega) huk_eq huk_good

/-! ### Section 6: **Theorem 1.1** and **Corollary 1.2** -/

/-- Every site `x ∈ oneVacancy c₀` lies in `Zone c₀ m` for some `m ≥ 1`. -/
lemma mem_some_zone_of_oneVacancy (c₀ : sites37) {x : H2} (hx : x ∈ oneVacancy c₀.1) :
    ∃ m : ℕ, 1 ≤ m ∧ x ∈ Zone c₀ m := by
  rcases delta237_direct_transitive c₀.2 origin_mem_sites37 with ⟨g, hg, hgc, hg_pres, _⟩
  have hgx : g x ∈ sites37 := delta237_apply_mem hg hx.1
  have hgx_V : g x ∈ V_all := V_all_eq_sites37.symm ▸ hgx
  rcases hgx_V with hgxo | hgxm
  · exfalso; exact hx.2 (g.injective (hgxo.trans hgc.symm))
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hgxm
    rcases hgxm with ⟨m, hm, hxm⟩
    refine ⟨m, hm, ?_⟩
    have h1 := zone_image_delta237 hg c₀ m
    have hgc' : (⟨g c₀.1, delta237_apply_mem hg c₀.2⟩ : sites37) = ⟨origin, origin_mem_sites37⟩ :=
      Subtype.ext hgc
    rw [hgc', zone_origin_eq_zoneVerts m hm] at h1
    have hmem : g x ∈ g '' Zone c₀ m := by rw [h1]; exact hxm
    rcases hmem with ⟨y, hy, heq⟩
    rwa [← g.injective heq]

/-- **Theorem 1.1 (Strong Solidity of `{7, 3}`)**:
    The face-incircles of the regular hyperbolic tiling `{7, 3}` form a strongly solid packing. -/
theorem thm_1_1_strong_solidity : IsStronglySolid r7 sites37 := by
  apply isStronglySolid_of_oneVacancy_solid
  intro c₀ hc₀
  refine ⟨fun x hx y hy hxy => isPacking_sites37 x hx.1 y hy.1 hxy, ?_⟩
  intro s X hX
  -- Every x ∈ s lies in some Zone ⟨c₀, hc₀⟩ m (m ≥ 1); take M = max over s!
  let zoneOf (x : H2) : ℕ :=
    if h : ∃ m : ℕ, 1 ≤ m ∧ x ∈ Zone ⟨c₀, hc₀⟩ m then Classical.choose h else 1
  let M : ℕ := max 1 (s.sup zoneOf)
  have hM : 1 ≤ M := le_max_left _ _
  rcases thm_1_1_step_zone_m ⟨c₀, hc₀⟩ M hM with ⟨uM, huM_eq, huM_good⟩
  have hs_sub_uM : s ⊆ uM := by
    intro x hxs
    have hx1 : x ∈ oneVacancy c₀ := hX.1 hxs
    have hex := mem_some_zone_of_oneVacancy ⟨c₀, hc₀⟩ hx1
    have hspec := Classical.choose_spec hex
    have hzm : zoneOf x = Classical.choose hex := by simp [zoneOf, hex]
    have hle : Classical.choose hex ≤ M := le_trans (hzm ▸ Finset.le_sup hxs) (le_max_right _ _)
    rw [← Finset.mem_coe, huM_eq]
    exact zone_subset_zoneUnion hspec.1 hle hspec.2
  have hs_good : IsGood c₀ s := j_subset c₀ hc₀ huM_good hs_sub_uM
  exact hs_good.2 X hX

/-- **Corollary 1.2**: `g₇ = 3` and `k₇ = 1 = g₇ - 2`. -/
theorem cor_1_2_grade_and_order :
    HasGradeOfSaturatedness r7 sites37 3 ∧ HasOrderOfSolidity r7 sites37 1 :=
  cor_1_2_of_strong_solidity thm_1_1_strong_solidity

end FejesTothP7.Proofs
