/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Defs.Tiling

/-!
# Combinatorial Properties of the Zone Substitution Words `w_m`

Proves the pure word-combinatorial claims of Lemma 5.1 (`zoneWord` lengths, non-emptiness,
parts (a), (b), (c) of the Zone Substitution Lemma, and block-level indexing for Theorem 1.1).
-/

namespace FejesTothP7.Proofs

lemma sigmaStep_length (t : ZoneType) : 2 ≤ (sigmaStep t).length := by
  cases t <;> decide

lemma zoneWord_one : zoneWord 1 = List.replicate 7 .t1 := rfl

lemma zoneWord_two : zoneWord 2 = (List.replicate 7 [.t1, .t1, .t2]).flatten := by
  decide

lemma zoneWord_three :
    zoneWord 3 = (List.replicate 7 [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]).flatten := by
  decide

lemma zoneWord_succ (m : ℕ) (hm : 1 ≤ m) :
    zoneWord (m + 1) = sigmaWord (zoneWord m) := by
  cases m with
  | zero => omega
  | succ k => rfl

lemma sigmaWord_cons (a : ZoneType) (tl : List ZoneType) :
    sigmaWord (a :: tl) = sigmaStep a ++ sigmaWord tl := rfl

lemma sigmaWord_append (u v : List ZoneType) :
    sigmaWord (u ++ v) = sigmaWord u ++ sigmaWord v := by
  simp [sigmaWord]

/-- Every `zoneWord m` (`m ≥ 1`) has length ≥ 7. -/
lemma zoneWord_length_ge_seven (m : ℕ) (hm : 1 ≤ m) : 7 ≤ (zoneWord m).length := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [zoneWord_succ k hk, sigmaWord, List.length_flatMap]
    have hsum : ∀ l : List ZoneType, l.length ≤ (l.map (fun t => (sigmaStep t).length)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a tl iht =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have ha := sigmaStep_length a
        omega
    exact le_trans ih (hsum (zoneWord k))

lemma zoneWord_length_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (zoneWord m).length :=
  lt_of_lt_of_le (by decide : 0 < 7) (zoneWord_length_ge_seven m hm)

lemma zoneWord_length_ge_21 (m : ℕ) (hm : 2 ≤ m) : 21 ≤ (zoneWord m).length := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [zoneWord_succ k (by omega), sigmaWord, List.length_flatMap]
    have hsum : ∀ l : List ZoneType, l.length ≤ (l.map (fun t => (sigmaStep t).length)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a tl iht =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have ha := sigmaStep_length a
        omega
    exact le_trans ih (hsum (zoneWord k))

lemma sigmaWord_head_eq_t1 (u : List ZoneType) (hu : u ≠ []) :
    (sigmaWord u).head? = some .t1 := by
  cases u with
  | nil => contradiction
  | cons a tl =>
    cases a <;> simp [sigmaWord_cons, sigmaStep]

/-- Linear local pattern invariant of `sigmaWord u`: no adjacent `t2, t2`. -/
lemma sigmaWord_no_adj_t2_linear (u : List ZoneType) :
    ∀ i : ℕ, (hi : i + 1 < (sigmaWord u).length) →
      (sigmaWord u)[i]'(by omega) = .t2 → (sigmaWord u)[i + 1]'hi = .t1 := by
  induction u with
  | nil => intro i hi; simp [sigmaWord] at hi
  | cons a tl ih =>
    intro i hi h2
    simp only [sigmaWord_cons] at hi h2 ⊢
    cases a with
    | t1 =>
      simp only [sigmaStep] at hi h2 ⊢
      have hlen : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl).length = 3 + (sigmaWord tl).length := by
        simp; omega
      match i with
      | 0 => simp at h2
      | 1 => simp at h2
      | 2 =>
        have htl_pos : 0 < (sigmaWord tl).length := by omega
        have htl_ne : tl ≠ [] := by intro h; subst h; simp [sigmaWord] at htl_pos
        have hhead := sigmaWord_head_eq_t1 tl htl_ne
        rw [List.head?_eq_getElem?] at hhead
        simp [htl_pos] at hhead
        simpa using hhead
      | k + 3 =>
        have g1 : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl)[k + 3]'(by omega) =
            (sigmaWord tl)[k]'(by omega) := by simp
        have g2 : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl)[k + 4]'hi =
            (sigmaWord tl)[k + 1]'(by omega) := by simp
        rw [g2]
        exact ih k (by omega) (g1.symm.trans h2)
    | t2 =>
      simp only [sigmaStep] at hi h2 ⊢
      have hlen : ([ZoneType.t1, .t2] ++ sigmaWord tl).length = 2 + (sigmaWord tl).length := by
        simp; omega
      match i with
      | 0 => simp at h2
      | 1 =>
        have htl_pos : 0 < (sigmaWord tl).length := by omega
        have htl_ne : tl ≠ [] := by intro h; subst h; simp [sigmaWord] at htl_pos
        have hhead := sigmaWord_head_eq_t1 tl htl_ne
        rw [List.head?_eq_getElem?] at hhead
        simp [htl_pos] at hhead
        simpa using hhead
      | k + 2 =>
        have g1 : ([ZoneType.t1, .t2] ++ sigmaWord tl)[k + 2]'(by omega) =
            (sigmaWord tl)[k]'(by omega) := by simp
        have g2 : ([ZoneType.t1, .t2] ++ sigmaWord tl)[k + 3]'hi =
            (sigmaWord tl)[k + 1]'(by omega) := by simp
        rw [g2]
        exact ih k (by omega) (g1.symm.trans h2)

/-- Linear local pattern invariant of `sigmaWord u`: no three consecutive `t1`. -/
lemma sigmaWord_no_triple_t1_linear (u : List ZoneType) :
    ∀ i : ℕ, (hi : i + 2 < (sigmaWord u).length) →
      (sigmaWord u)[i]'(by omega) = .t1 →
      (sigmaWord u)[i + 1]'(by omega) = .t1 →
      (sigmaWord u)[i + 2]'hi = .t2 := by
  induction u with
  | nil => intro i hi; simp [sigmaWord] at hi
  | cons a tl ih =>
    intro i hi h0 h1
    simp only [sigmaWord_cons] at hi h0 h1 ⊢
    cases a with
    | t1 =>
      simp only [sigmaStep] at hi h0 h1 ⊢
      have hlen : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl).length = 3 + (sigmaWord tl).length := by
        simp; omega
      match i with
      | 0 => rfl
      | 1 => simp at h1
      | 2 => simp at h0
      | k + 3 =>
        have g0 : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl)[k + 3]'(by omega) =
            (sigmaWord tl)[k]'(by omega) := by simp
        have g1 : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl)[k + 4]'(by omega) =
            (sigmaWord tl)[k + 1]'(by omega) := by simp
        have g2 : ([ZoneType.t1, .t1, .t2] ++ sigmaWord tl)[k + 5]'hi =
            (sigmaWord tl)[k + 2]'(by omega) := by simp
        rw [g2]
        exact ih k (by omega) (g0.symm.trans h0) (g1.symm.trans h1)
    | t2 =>
      simp only [sigmaStep] at hi h0 h1 ⊢
      have hlen : ([ZoneType.t1, .t2] ++ sigmaWord tl).length = 2 + (sigmaWord tl).length := by
        simp; omega
      match i with
      | 0 => simp at h1
      | 1 => simp at h0
      | k + 2 =>
        have g0 : ([ZoneType.t1, .t2] ++ sigmaWord tl)[k + 2]'(by omega) =
            (sigmaWord tl)[k]'(by omega) := by simp
        have g1 : ([ZoneType.t1, .t2] ++ sigmaWord tl)[k + 3]'(by omega) =
            (sigmaWord tl)[k + 1]'(by omega) := by simp
        have g2 : ([ZoneType.t1, .t2] ++ sigmaWord tl)[k + 4]'hi =
            (sigmaWord tl)[k + 2]'(by omega) := by simp
        rw [g2]
        exact ih k (by omega) (g0.symm.trans h0) (g1.symm.trans h1)

lemma getElem_append_self {α : Type*} (w : List α) (hw : 0 < w.length) (k d : ℕ)
    (hk : k < w.length) (hd : d ≤ w.length) :
    (w ++ w)[k + d]'(by simp; omega) = w[(k + d) % w.length]'(Nat.mod_lt _ hw) := by
  by_cases hlt : k + d < w.length
  · rw [List.getElem_append_left hlt]
    congr 1
    exact (Nat.mod_eq_of_lt hlt).symm
  · have hge : w.length ≤ k + d := by omega
    rw [List.getElem_append_right hge]
    congr 1
    have hsub : k + d - w.length < w.length := by omega
    have hmod : (k + d) % w.length = k + d - w.length := by
      have := Nat.mod_eq_sub_mod hge
      rw [this, Nat.mod_eq_of_lt hsub]
    exact hmod.symm

/-- **Lemma 5.1(a)**: For `m ≥ 2`, no two `t2`'s are cyclically adjacent in `zoneWord m`,
    and no three `t1`'s are cyclically consecutive. -/
theorem zoneWord_part_a (m : ℕ) (hm : 2 ≤ m) :
    let w := zoneWord m
    ∀ (k : Fin w.length),
      (w.get k = .t2 →
        w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1) ∧
      (w.get k = .t1 →
        w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1 →
        w.get ⟨(k.1 + 2) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t2) := by
  intro w k
  have hm1 : 1 ≤ m - 1 := by omega
  have hw_eq : w = sigmaWord (zoneWord (m - 1)) := by
    have h := zoneWord_succ (m - 1) hm1
    have hmeq : m - 1 + 1 = m := by omega
    rw [hmeq] at h
    exact h
  have hw_ge7 : 7 ≤ w.length := zoneWord_length_ge_seven m (by omega)
  have hw_pos : 0 < w.length := by omega
  let u := zoneWord (m - 1)
  have hww : w ++ w = sigmaWord (u ++ u) := by
    rw [hw_eq, sigmaWord_append]
  have h0 : (w ++ w)[k.1]'(by simp; omega) = w.get k := by
    rw [List.getElem_append_left k.2]; rfl
  have h1 : (w ++ w)[k.1 + 1]'(by simp; omega) =
      w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ hw_pos⟩ := by
    simpa [List.get_eq_getElem] using getElem_append_self w hw_pos k.1 1 k.2 (by omega)
  have h2 : (w ++ w)[k.1 + 2]'(by simp; omega) =
      w.get ⟨(k.1 + 2) % w.length, Nat.mod_lt _ hw_pos⟩ := by
    simpa [List.get_eq_getElem] using getElem_append_self w hw_pos k.1 2 k.2 (by omega)
  constructor
  · intro hk2
    have hlin := sigmaWord_no_adj_t2_linear (u ++ u) k.1 (by rw [← hww]; simp; omega)
    rw [← h1]
    have hk2' : (sigmaWord (u ++ u))[k.1]'(by rw [← hww]; simp; omega) = .t2 := by
      simpa [hww] using h0.trans hk2
    simpa [hww] using hlin hk2'
  · intro hk0 hk1
    have hlin := sigmaWord_no_triple_t1_linear (u ++ u) k.1 (by rw [← hww]; simp; omega)
    rw [← h2]
    have hk0' : (sigmaWord (u ++ u))[k.1]'(by rw [← hww]; simp; omega) = .t1 := by
      simpa [hww] using h0.trans hk0
    have hk1' : (sigmaWord (u ++ u))[k.1 + 1]'(by rw [← hww]; simp; omega) = .t1 := by
      simpa [hww] using h1.trans hk1
    simpa [hww] using hlin hk0' hk1'

/-- Two-step substitution `σ²(1)` (len 8) and `σ²(2)` (len 5). -/
def sigma2Step : ZoneType → List ZoneType
  | .t1 => [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]
  | .t2 => [.t1, .t1, .t2, .t1, .t2]

lemma sigmaWord_sigmaWord (v : List ZoneType) :
    sigmaWord (sigmaWord v) = v.flatMap sigma2Step := by
  induction v with
  | nil => rfl
  | cons a tl ih =>
    rw [sigmaWord_cons, sigmaWord_append, ih, List.flatMap_cons]
    cases a <;> rfl

/-- Linear invariant of `σ²(v)` when `v` has no adjacent `t2`. -/
lemma sigma2_no_adj_SDS_linear (v : List ZoneType)
    (hno22 : ∀ j : ℕ, (hj : j + 1 < v.length) → v[j]'(by omega) = .t2 → v[j + 1]'hj = .t1) :
    ∀ i : ℕ, (hi : i + 13 < (v.flatMap sigma2Step).length) →
      (v.flatMap sigma2Step)[i]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 1]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 2]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 3]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 4]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 5]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 6]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 7]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 8]'(by omega) = .t1 ∧
      (v.flatMap sigma2Step)[i + 9]'(by omega) = .t1 ∧
      (v.flatMap sigma2Step)[i + 10]'(by omega) = .t2 ∧
      (v.flatMap sigma2Step)[i + 11]'(by omega) = .t1 ∧
      (v.flatMap sigma2Step)[i + 12]'(by omega) = .t1 ∧
      (v.flatMap sigma2Step)[i + 13]'hi = .t2 := by
  induction v with
  | nil => intro i hi; simp at hi
  | cons a tl ih =>
    intro i hi h0 h1 h2 h3 h4 h5 h6 h7
    have hno22_tl : ∀ j : ℕ, (hj : j + 1 < tl.length) → tl[j]'(by omega) = .t2 → tl[j + 1]'hj = .t1 := by
      intro j hj htj
      exact hno22 (j + 1) (by simp; omega) (by simpa using htj)
    simp only [List.flatMap_cons] at hi h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    cases a with
    | t1 =>
      simp only [sigma2Step] at hi h0 h1 h2 h3 h4 h5 h6 h7 ⊢
      have hlen : ([ZoneType.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2] ++ tl.flatMap sigma2Step).length =
          8 + (tl.flatMap sigma2Step).length := by simp; omega
      by_cases hlt : i < 8
      · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · simp at h0
        · simp at h0
        · simp at h2
        · simp at h0
        · simp at h0
        · cases tl with
          | nil => simp at hi
          | cons b tl' =>
            cases b with
            | t1 =>
              simp only [List.flatMap_cons, sigma2Step] at h7
              simp at h7
            | t2 =>
              cases tl' with
              | nil =>
                simp only [List.flatMap_cons, sigma2Step] at hi
                simp at hi
              | cons c tl'' =>
                have hc : c = .t1 := hno22_tl 0 (by simp) rfl
                subst hc
                simp only [List.flatMap_cons, sigma2Step]
                simp
        · simp at h0
        · cases tl with
          | nil => simp at hi
          | cons b tl' =>
            cases b <;> simp only [List.flatMap_cons, sigma2Step] at h2 <;> simp at h2
        · omega
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 8 := ⟨i - 8, by omega⟩
        have hstep : ∀ d : ℕ, (hd : k + 8 + d < ([ZoneType.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2] ++
              tl.flatMap sigma2Step).length) →
            ([ZoneType.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2] ++ tl.flatMap sigma2Step)[k + 8 + d]'hd =
            (tl.flatMap sigma2Step)[k + d]'(by omega) := by
          intro d hd
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_cons, List.length_nil]
          congr 1; omega
        have h0' : (tl.flatMap sigma2Step)[k]'(by omega) = .t2 := by
          simpa using (hstep 0 (by omega)).symm.trans h0
        have h1' : (tl.flatMap sigma2Step)[k + 1]'(by omega) = .t1 := by
          simpa using (hstep 1 (by omega)).symm.trans h1
        have h2' : (tl.flatMap sigma2Step)[k + 2]'(by omega) = .t2 := by
          simpa using (hstep 2 (by omega)).symm.trans h2
        have h3' : (tl.flatMap sigma2Step)[k + 3]'(by omega) = .t1 := by
          simpa using (hstep 3 (by omega)).symm.trans h3
        have h4' : (tl.flatMap sigma2Step)[k + 4]'(by omega) = .t1 := by
          simpa using (hstep 4 (by omega)).symm.trans h4
        have h5' : (tl.flatMap sigma2Step)[k + 5]'(by omega) = .t2 := by
          simpa using (hstep 5 (by omega)).symm.trans h5
        have h6' : (tl.flatMap sigma2Step)[k + 6]'(by omega) = .t1 := by
          simpa using (hstep 6 (by omega)).symm.trans h6
        have h7' : (tl.flatMap sigma2Step)[k + 7]'(by omega) = .t2 := by
          simpa using (hstep 7 (by omega)).symm.trans h7
        have hrec := ih hno22_tl k (by omega) h0' h1' h2' h3' h4' h5' h6' h7'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using (hstep 8 (by omega)).trans hrec.1
        · simpa using (hstep 9 (by omega)).trans hrec.2.1
        · simpa using (hstep 10 (by omega)).trans hrec.2.2.1
        · simpa using (hstep 11 (by omega)).trans hrec.2.2.2.1
        · simpa using (hstep 12 (by omega)).trans hrec.2.2.2.2.1
        · simpa using (hstep 13 hi).trans hrec.2.2.2.2.2
    | t2 =>
      simp only [sigma2Step] at hi h0 h1 h2 h3 h4 h5 h6 h7 ⊢
      have hlen : ([ZoneType.t1, .t1, .t2, .t1, .t2] ++ tl.flatMap sigma2Step).length =
          5 + (tl.flatMap sigma2Step).length := by simp; omega
      by_cases hlt : i < 5
      · rcases i with _ | _ | _ | _ | _ | _
        · simp at h0
        · simp at h0
        · cases tl with
          | nil => simp at hi
          | cons b tl' =>
            have hb : b = .t1 := hno22 0 (by simp) rfl
            subst hb
            simp only [List.flatMap_cons, sigma2Step] at h7
            simp at h7
        · simp at h0
        · cases tl with
          | nil => simp at hi
          | cons b tl' =>
            cases b <;> simp only [List.flatMap_cons, sigma2Step] at h2 <;> simp at h2
        · omega
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
        have hstep : ∀ d : ℕ, (hd : k + 5 + d < ([ZoneType.t1, .t1, .t2, .t1, .t2] ++
              tl.flatMap sigma2Step).length) →
            ([ZoneType.t1, .t1, .t2, .t1, .t2] ++ tl.flatMap sigma2Step)[k + 5 + d]'hd =
            (tl.flatMap sigma2Step)[k + d]'(by omega) := by
          intro d hd
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_cons, List.length_nil]
          congr 1; omega
        have h0' : (tl.flatMap sigma2Step)[k]'(by omega) = .t2 := by
          simpa using (hstep 0 (by omega)).symm.trans h0
        have h1' : (tl.flatMap sigma2Step)[k + 1]'(by omega) = .t1 := by
          simpa using (hstep 1 (by omega)).symm.trans h1
        have h2' : (tl.flatMap sigma2Step)[k + 2]'(by omega) = .t2 := by
          simpa using (hstep 2 (by omega)).symm.trans h2
        have h3' : (tl.flatMap sigma2Step)[k + 3]'(by omega) = .t1 := by
          simpa using (hstep 3 (by omega)).symm.trans h3
        have h4' : (tl.flatMap sigma2Step)[k + 4]'(by omega) = .t1 := by
          simpa using (hstep 4 (by omega)).symm.trans h4
        have h5' : (tl.flatMap sigma2Step)[k + 5]'(by omega) = .t2 := by
          simpa using (hstep 5 (by omega)).symm.trans h5
        have h6' : (tl.flatMap sigma2Step)[k + 6]'(by omega) = .t1 := by
          simpa using (hstep 6 (by omega)).symm.trans h6
        have h7' : (tl.flatMap sigma2Step)[k + 7]'(by omega) = .t2 := by
          simpa using (hstep 7 (by omega)).symm.trans h7
        have hrec := ih hno22_tl k (by omega) h0' h1' h2' h3' h4' h5' h6' h7'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using (hstep 8 (by omega)).trans hrec.1
        · simpa using (hstep 9 (by omega)).trans hrec.2.1
        · simpa using (hstep 10 (by omega)).trans hrec.2.2.1
        · simpa using (hstep 11 (by omega)).trans hrec.2.2.2.1
        · simpa using (hstep 12 (by omega)).trans hrec.2.2.2.2.1
        · simpa using (hstep 13 hi).trans hrec.2.2.2.2.2

/-- **Lemma 5.1(c)**: For `m ≥ 4`, no two `S-D-S` arcs are adjacent in `zoneWord m`. -/
theorem zoneWord_part_c (m : ℕ) (hm : 4 ≤ m) :
    let w := zoneWord m
    ∀ (k : Fin w.length),
      let idx (i : ℕ) : Fin w.length := ⟨i % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
      w.get (idx (k.1 + w.length - 1)) = .t2 →
      w.get k = .t1 →
      w.get (idx (k.1 + 1)) = .t2 →
      w.get (idx (k.1 + 2)) = .t1 →
      w.get (idx (k.1 + 3)) = .t1 →
      w.get (idx (k.1 + 4)) = .t2 →
      w.get (idx (k.1 + 5)) = .t1 →
      w.get (idx (k.1 + 6)) = .t2 →
      w.get (idx (k.1 + 7)) = .t1 ∧
      w.get (idx (k.1 + 8)) = .t1 ∧
      w.get (idx (k.1 + 9)) = .t2 ∧
      w.get (idx (k.1 + 10)) = .t1 ∧
      w.get (idx (k.1 + 11)) = .t1 ∧
      w.get (idx (k.1 + 12)) = .t2 := by
  intro w k idx h_m1 h0 h1 h2 h3 h4 h5 h6
  have hw21 : 21 ≤ w.length := zoneWord_length_ge_21 m (by omega)
  have hw_pos : 0 < w.length := by omega
  let v := zoneWord (m - 2)
  have hw_eq : w = v.flatMap sigma2Step := by
    have h1s := zoneWord_succ (m - 1) (by omega)
    have h2s := zoneWord_succ (m - 2) (by omega)
    have hm1 : m - 1 + 1 = m := by omega
    have hm2 : m - 2 + 1 = m - 1 := by omega
    rw [hm1] at h1s; rw [hm2] at h2s
    change zoneWord m = _
    rw [h1s, h2s, sigmaWord_sigmaWord]
  have hww : w ++ w = (v ++ v).flatMap sigma2Step := by
    rw [hw_eq, List.flatMap_append]
  have hww_len : ((v ++ v).flatMap sigma2Step).length = w.length + w.length := by
    rw [← hww, List.length_append]
  have hno22 : ∀ j : ℕ, (hj : j + 1 < (v ++ v).length) →
      (v ++ v)[j]'(by omega) = .t2 → (v ++ v)[j + 1]'hj = .t1 := by
    have hv_eq : v = sigmaWord (zoneWord (m - 3)) := by
      have h := zoneWord_succ (m - 3) (by omega)
      have hm3 : m - 3 + 1 = m - 2 := by omega
      rw [hm3] at h
      exact h
    have hvv : v ++ v = sigmaWord (zoneWord (m - 3) ++ zoneWord (m - 3)) := by
      rw [hv_eq, sigmaWord_append]
    intro j hj hj2
    have hlin := sigmaWord_no_adj_t2_linear (zoneWord (m - 3) ++ zoneWord (m - 3)) j (by rwa [← hvv])
    simpa [hvv] using hlin (by simpa [hvv] using hj2)
  let i0 : ℕ := (k.1 + w.length - 1) % w.length
  have hi0_lt : i0 < w.length := Nat.mod_lt _ hw_pos
  have hshift : ∀ d : ℕ, (hd : d ≤ 13) →
      ((v ++ v).flatMap sigma2Step)[i0 + d]'(by omega) =
      w.get (idx (k.1 + w.length - 1 + d)) := by
    intro d hd
    have heq1 : ((v ++ v).flatMap sigma2Step)[i0 + d]'(by omega) =
        (w ++ w)[i0 + d]'(by simp; omega) := by simp [hww]
    rw [heq1, getElem_append_self w hw_pos i0 d hi0_lt (by omega)]
    simp only [List.get_eq_getElem, idx, i0]
    congr 1
    rw [Nat.mod_add_mod]
  have hmod_succ : ∀ d : ℕ, (k.1 + w.length - 1 + (d + 1)) % w.length = (k.1 + d) % w.length := by
    intro d
    have h1 : k.1 + w.length - 1 + (d + 1) = (k.1 + d) + w.length := by omega
    rw [h1, Nat.add_mod_right]
  have hlin := sigma2_no_adj_SDS_linear (v ++ v) hno22 i0 (by omega)
  have p0 : ((v ++ v).flatMap sigma2Step)[i0]'(by omega) = .t2 := by
    simpa using (hshift 0 (by omega)).trans h_m1
  have p1 : ((v ++ v).flatMap sigma2Step)[i0 + 1]'(by omega) = .t1 := by
    rw [hshift 1 (by omega)]
    have : idx (k.1 + w.length - 1 + 1) = k := by
      ext; simp [idx]; have := hmod_succ 0; simpa [Nat.mod_eq_of_lt k.2] using this
    rwa [this]
  have p2 : ((v ++ v).flatMap sigma2Step)[i0 + 2]'(by omega) = .t2 := by
    rw [hshift 2 (by omega)]
    have : idx (k.1 + w.length - 1 + 2) = idx (k.1 + 1) := by ext; simp [idx, hmod_succ 1]
    rwa [this]
  have p3 : ((v ++ v).flatMap sigma2Step)[i0 + 3]'(by omega) = .t1 := by
    rw [hshift 3 (by omega)]
    have : idx (k.1 + w.length - 1 + 3) = idx (k.1 + 2) := by ext; simp [idx, hmod_succ 2]
    rwa [this]
  have p4 : ((v ++ v).flatMap sigma2Step)[i0 + 4]'(by omega) = .t1 := by
    rw [hshift 4 (by omega)]
    have : idx (k.1 + w.length - 1 + 4) = idx (k.1 + 3) := by ext; simp [idx, hmod_succ 3]
    rwa [this]
  have p5 : ((v ++ v).flatMap sigma2Step)[i0 + 5]'(by omega) = .t2 := by
    rw [hshift 5 (by omega)]
    have : idx (k.1 + w.length - 1 + 5) = idx (k.1 + 4) := by ext; simp [idx, hmod_succ 4]
    rwa [this]
  have p6 : ((v ++ v).flatMap sigma2Step)[i0 + 6]'(by omega) = .t1 := by
    rw [hshift 6 (by omega)]
    have : idx (k.1 + w.length - 1 + 6) = idx (k.1 + 5) := by ext; simp [idx, hmod_succ 5]
    rwa [this]
  have p7 : ((v ++ v).flatMap sigma2Step)[i0 + 7]'(by omega) = .t2 := by
    rw [hshift 7 (by omega)]
    have : idx (k.1 + w.length - 1 + 7) = idx (k.1 + 6) := by ext; simp [idx, hmod_succ 6]
    rwa [this]
  have hres := hlin p0 p1 p2 p3 p4 p5 p6 p7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : idx (k.1 + w.length - 1 + 8) = idx (k.1 + 7) := by ext; simp [idx, hmod_succ 7]
    rw [← this, ← hshift 8 (by omega)]; exact hres.1
  · have : idx (k.1 + w.length - 1 + 9) = idx (k.1 + 8) := by ext; simp [idx, hmod_succ 8]
    rw [← this, ← hshift 9 (by omega)]; exact hres.2.1
  · have : idx (k.1 + w.length - 1 + 10) = idx (k.1 + 9) := by ext; simp [idx, hmod_succ 9]
    rw [← this, ← hshift 10 (by omega)]; exact hres.2.2.1
  · have : idx (k.1 + w.length - 1 + 11) = idx (k.1 + 10) := by ext; simp [idx, hmod_succ 10]
    rw [← this, ← hshift 11 (by omega)]; exact hres.2.2.2.1
  · have : idx (k.1 + w.length - 1 + 12) = idx (k.1 + 11) := by ext; simp [idx, hmod_succ 11]
    rw [← this, ← hshift 12 (by omega)]; exact hres.2.2.2.2.1
  · have : idx (k.1 + w.length - 1 + 13) = idx (k.1 + 12) := by ext; simp [idx, hmod_succ 12]
    rw [← this, ← hshift 13 (by omega)]; exact hres.2.2.2.2.2

end FejesTothP7.Proofs
