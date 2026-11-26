/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.MainTheorem
import FejesTothP7.Proofs.MetricGap

/-!
# Certification Bridges and Complete Lemma 5.1 Assembly

Provides the open-disc equivalence bridges, `{7, 3}` / `{3, 7}` tiling certification,
the Lemma 2.4 uniqueness consequence, the `Δ₇ = 0` identity, and the full assembly of
Lemma 5.1 (including the convex polygon `P_m`, the `σ²` block decomposition, and the
extended no-adjacent-SDS clause through `k + 14`).
-/

noncomputable section
open Classical

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Open-disc equivalence bridges -/

theorem overlaps_iff_balls_inter_nonempty {r : ℝ} (_hr : 0 < r) (P q : H2) :
    Overlaps r P q ↔ (Metric.ball P r ∩ Metric.ball q r).Nonempty := by
  unfold Overlaps
  constructor
  · intro hlt
    refine ⟨H2.mid P q, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm, H2.dist_mid_left]; linarith
    · rw [Metric.mem_ball, H2.dist_mid_right]; linarith
  · rintro ⟨z, hzP, hzq⟩
    rw [Metric.mem_ball] at hzP hzq
    have htri := dist_triangle P z q
    rw [dist_comm P z] at htri
    linarith

theorem isPacking_iff_pairwise_disjoint_balls {r : ℝ} (hr : 0 < r) (C : Set H2) :
    IsPacking r C ↔
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (Metric.ball x r) (Metric.ball y r) := by
  unfold IsPacking
  constructor
  · intro hpack x hx y hy hxy
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne
    have hne' : (Metric.ball x r ∩ Metric.ball y r).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hov : Overlaps r x y := (overlaps_iff_balls_inter_nonempty hr x y).mpr hne'
    have hge := hpack x hx y hy hxy
    unfold Overlaps at hov
    linarith
  · intro hdisj x hx y hy hxy
    by_contra hlt
    push Not at hlt
    have hne' : (Metric.ball x r ∩ Metric.ball y r).Nonempty :=
      (overlaps_iff_balls_inter_nonempty hr x y).mp hlt
    exact hne'.ne_empty (Set.disjoint_iff_inter_eq_empty.mp (hdisj x hx y hy hxy))

/-! ### `{7, 3}` / `{3, 7}` tiling certification -/

theorem sites37_tiling_certification :
    IsPacking r7 sites37 ∧
    (∀ v ∈ sites37, Nonempty (SiteFrame sites37 v)) ∧
    (∀ P : H2, ∃ v ∈ sites37, dist P v ≤ Rc7) ∧
    (∀ u ∈ sites37, ∀ v ∈ sites37, ∃ g ∈ Delta237, g u = v ∧ g '' sites37 = sites37) := by
  refine ⟨isPacking_sites37, ?_, covering_radius_Rc7, ?_⟩
  · intro v hv
    rcases exists_direct_siteFrame_sites37 hv with ⟨F, _, _⟩
    exact ⟨F⟩
  · intro u hu v hv
    rcases delta237_direct_transitive hu hv with ⟨g, hg, hgu, hgpres, _⟩
    exact ⟨g, hg, hgu, hgpres⟩

lemma hFrame_sites37 : ∀ v ∈ sites37, Nonempty (SiteFrame sites37 v) :=
  sites37_tiling_certification.2.1

/-! ### Lemma 2.4 consequence and `Δ₇ = 0` -/

theorem lem_2_4_edge_conseq (c₀ : H2) (s X : Finset H2)
    (hX : IsRearrangement r7 (oneVacancy c₀) s X)
    (v v' o : H2) (hvv' : Adj37 v v') (hvo : Adj37 v o) (hv'o : Adj37 v' o)
    (ho_fix : o ∈ sites37 \ UnfixedSites c₀ s) :
    (X.filter (fun P => Overlaps r7 P v ∧ Overlaps r7 P v')).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P₁ h₁ P₂ h₂
  rw [Finset.mem_filter] at h₁ h₂
  exact unique_overlapper_of_edge_with_fixed_nbr c₀ s X hX hvv' hvo hv'o ho_fix
    h₁.1 h₂.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2

theorem fig_2_delta7_zero : deltaP 7 = 0 := by
  unfold deltaP
  have h := prop_3_1_exact_identity
  unfold h7 r7 ρ7 at h
  linarith

/-! ### Complete Lemma 5.1 (convex polygon `P_m`, `σ²` block decomposition, extended part (c)) -/

theorem zoneWord_sigma2_eq (m : ℕ) (hm : 4 ≤ m) :
    zoneWord m = (zoneWord (m - 2)).flatMap (fun t =>
      if t = .t1 then [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]
      else [.t1, .t1, .t2, .t1, .t2]) := by
  have h1 := zoneWord_succ (m - 2) (by omega)
  have h2 := zoneWord_succ (m - 1) (by omega)
  rw [show m - 2 + 1 = m - 1 by omega] at h1
  rw [show m - 1 + 1 = m by omega] at h2
  rw [h2, h1, sigmaWord_sigmaWord]
  congr 1; funext t; cases t <;> rfl

private lemma sigma2_no_adj_SDS_linear_ext (v : List ZoneType)
    (hno22 : ∀ j : ℕ, (hj : j + 1 < v.length) → v[j]'(by omega) = .t2 → v[j + 1]'hj = .t1) :
    ∀ i : ℕ, (hi : i + 15 < (v.flatMap sigma2Step).length) →
      (v.flatMap sigma2Step)[i]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 1]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 2]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 3]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 4]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 5]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 6]'(by omega) = .t1 →
      (v.flatMap sigma2Step)[i + 7]'(by omega) = .t2 →
      (v.flatMap sigma2Step)[i + 14]'(by omega) = .t1 ∧
      (v.flatMap sigma2Step)[i + 15]'hi = .t2 := by
  induction v with
  | nil => intro i hi; simp at hi
  | cons a tl ih =>
    intro i hi h0 h1 h2 h3 h4 h5 h6 h7
    have hno22_tl : ∀ j : ℕ, (hj : j + 1 < tl.length) → tl[j]'(by omega) = .t2 → tl[j + 1]'hj = .t1 :=
      fun j hj htj => hno22 (j + 1) (by simp; omega) (by simpa using htj)
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
            | t1 => simp only [List.flatMap_cons, sigma2Step] at h7; simp at h7
            | t2 =>
              cases tl' with
              | nil => simp only [List.flatMap_cons, sigma2Step] at hi; simp at hi
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
        have hrec := ih hno22_tl k (by omega)
          (by simpa using (hstep 0 (by omega)).symm.trans h0)
          (by simpa using (hstep 1 (by omega)).symm.trans h1)
          (by simpa using (hstep 2 (by omega)).symm.trans h2)
          (by simpa using (hstep 3 (by omega)).symm.trans h3)
          (by simpa using (hstep 4 (by omega)).symm.trans h4)
          (by simpa using (hstep 5 (by omega)).symm.trans h5)
          (by simpa using (hstep 6 (by omega)).symm.trans h6)
          (by simpa using (hstep 7 (by omega)).symm.trans h7)
        exact ⟨by simpa using (hstep 14 (by omega)).trans hrec.1,
          by simpa using (hstep 15 hi).trans hrec.2⟩
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
        have hrec := ih hno22_tl k (by omega)
          (by simpa using (hstep 0 (by omega)).symm.trans h0)
          (by simpa using (hstep 1 (by omega)).symm.trans h1)
          (by simpa using (hstep 2 (by omega)).symm.trans h2)
          (by simpa using (hstep 3 (by omega)).symm.trans h3)
          (by simpa using (hstep 4 (by omega)).symm.trans h4)
          (by simpa using (hstep 5 (by omega)).symm.trans h5)
          (by simpa using (hstep 6 (by omega)).symm.trans h6)
          (by simpa using (hstep 7 (by omega)).symm.trans h7)
        exact ⟨by simpa using (hstep 14 (by omega)).trans hrec.1,
          by simpa using (hstep 15 hi).trans hrec.2⟩

theorem zoneWord_part_c_full (m : ℕ) (hm : 4 ≤ m) :
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
      w.get (idx (k.1 + 12)) = .t2 ∧
      w.get (idx (k.1 + 13)) = .t1 ∧
      w.get (idx (k.1 + 14)) = .t2 := by
  intro w k idx h_m1 h0 h1 h2 h3 h4 h5 h6
  have hbase := zoneWord_part_c m hm k h_m1 h0 h1 h2 h3 h4 h5 h6
  have hw21 : 21 ≤ w.length := zoneWord_length_ge_21 m (by omega)
  have hw_pos : 0 < w.length := by omega
  let v := zoneWord (m - 2)
  have hw_eq : w = v.flatMap sigma2Step := by
    have h := zoneWord_sigma2_eq m hm
    refine h.trans ?_
    congr 1; funext t; cases t <;> rfl
  have hww : w ++ w = (v ++ v).flatMap sigma2Step := by rw [hw_eq, List.flatMap_append]
  have hww_len : ((v ++ v).flatMap sigma2Step).length = w.length + w.length := by
    rw [← hww, List.length_append]
  have hno22 : ∀ j : ℕ, (hj : j + 1 < (v ++ v).length) →
      (v ++ v)[j]'(by omega) = .t2 → (v ++ v)[j + 1]'hj = .t1 := by
    have hv_eq : v = sigmaWord (zoneWord (m - 3)) := by
      have h := zoneWord_succ (m - 3) (by omega)
      rw [show m - 3 + 1 = m - 2 by omega] at h; exact h
    have hvv : v ++ v = sigmaWord (zoneWord (m - 3) ++ zoneWord (m - 3)) := by
      rw [hv_eq, sigmaWord_append]
    intro j hj hj2
    have hlin := sigmaWord_no_adj_t2_linear (zoneWord (m - 3) ++ zoneWord (m - 3)) j (by rwa [← hvv])
    simpa [hvv] using hlin (by simpa [hvv] using hj2)
  let i0 : ℕ := (k.1 + w.length - 1) % w.length
  have hi0_lt : i0 < w.length := Nat.mod_lt _ hw_pos
  have hshift : ∀ d : ℕ, (hd : d ≤ 15) →
      ((v ++ v).flatMap sigma2Step)[i0 + d]'(by omega) =
      w.get (idx (k.1 + w.length - 1 + d)) := by
    intro d hd
    have heq1 : ((v ++ v).flatMap sigma2Step)[i0 + d]'(by omega) =
        (w ++ w)[i0 + d]'(by simp; omega) := by simp [hww]
    rw [heq1, getElem_append_self w hw_pos i0 d hi0_lt (by omega)]
    simp only [List.get_eq_getElem, idx, i0]
    congr 1; rw [Nat.mod_add_mod]
  have hmod_succ : ∀ d : ℕ, (k.1 + w.length - 1 + (d + 1)) % w.length = (k.1 + d) % w.length := by
    intro d
    rw [show k.1 + w.length - 1 + (d + 1) = (k.1 + d) + w.length by omega, Nat.add_mod_right]
  have hres := sigma2_no_adj_SDS_linear_ext (v ++ v) hno22 i0 (by omega)
    (by simpa using (hshift 0 (by omega)).trans h_m1)
    (by rw [hshift 1 (by omega)]
        have : idx (k.1 + w.length - 1 + 1) = k := by
          ext; simp [idx]; have := hmod_succ 0; simpa [Nat.mod_eq_of_lt k.2] using this
        rwa [this])
    (by rw [hshift 2 (by omega)]
        have : idx (k.1 + w.length - 1 + 2) = idx (k.1 + 1) := by ext; simp [idx, hmod_succ 1]
        rwa [this])
    (by rw [hshift 3 (by omega)]
        have : idx (k.1 + w.length - 1 + 3) = idx (k.1 + 2) := by ext; simp [idx, hmod_succ 2]
        rwa [this])
    (by rw [hshift 4 (by omega)]
        have : idx (k.1 + w.length - 1 + 4) = idx (k.1 + 3) := by ext; simp [idx, hmod_succ 3]
        rwa [this])
    (by rw [hshift 5 (by omega)]
        have : idx (k.1 + w.length - 1 + 5) = idx (k.1 + 4) := by ext; simp [idx, hmod_succ 4]
        rwa [this])
    (by rw [hshift 6 (by omega)]
        have : idx (k.1 + w.length - 1 + 6) = idx (k.1 + 5) := by ext; simp [idx, hmod_succ 5]
        rwa [this])
    (by rw [hshift 7 (by omega)]
        have : idx (k.1 + w.length - 1 + 7) = idx (k.1 + 6) := by ext; simp [idx, hmod_succ 6]
        rwa [this])
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hbase.2.2.2.2.1, hbase.2.2.2.2.2, ?_, ?_⟩
  · have : idx (k.1 + w.length - 1 + 14) = idx (k.1 + 13) := by ext; simp [idx, hmod_succ 13]
    rw [← this, ← hshift 14 (by omega)]; exact hres.1
  · have : idx (k.1 + w.length - 1 + 15) = idx (k.1 + 14) := by ext; simp [idx, hmod_succ 14]
    rw [← this, ← hshift 15 (by omega)]; exact hres.2

theorem lem_5_1_zone_substitution (c₀ : sites37) :
    (∀ m : ℕ, 1 ≤ m →
      ∃ cyc : List H2,
        cyc.Nodup ∧
        ∃ hlen : cyc.length = (zoneWord m).length,
        ({x | x ∈ cyc} : Set H2) = Zone c₀ m ∧
        (∀ (k : Fin cyc.length),
          let v := cyc.get k
          let vPrev := cyc.get ⟨(k.1 + cyc.length - 1) % cyc.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
          let vNext := cyc.get ⟨(k.1 + 1) % cyc.length,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩
          let i : ℕ := if (zoneWord m).get (k.cast hlen) = .t1 then 1 else 2
          ∃ F : SiteFrame sites37 v,
            F.nbr 0 = vPrev ∧
            (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ i → F.nbr j ∈ Zone c₀ (m - 1)) ∧
            F.nbr (i + 1 : ℕ) = vNext ∧
            (∀ j : Fin 7, i + 2 ≤ j.1 → F.nbr j ∈ Zone c₀ (m + 1))) ∧
        (∀ (k : Fin cyc.length), ∀ x ∈ ZoneUnion c₀ m ∪ {c₀.1},
          0 ≤ H2.detH (cyc.get k)
            (cyc.get ⟨(k.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩) x)) ∧
    (∀ m : ℕ, 2 ≤ m →
      let w := zoneWord m
      ∀ (k : Fin w.length),
        (w.get k = .t2 →
          w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1) ∧
        (w.get k = .t1 →
          w.get ⟨(k.1 + 1) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t1 →
          w.get ⟨(k.1 + 2) % w.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ = .t2)) ∧
    (zoneWord 2 = (List.replicate 7 [.t1, .t1, .t2]).flatten) ∧
    (zoneWord 3 = (List.replicate 7 [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]).flatten) ∧
    (∀ m : ℕ, 4 ≤ m →
      zoneWord m = (zoneWord (m - 2)).flatMap (fun t =>
        if t = .t1 then [.t1, .t1, .t2, .t1, .t1, .t2, .t1, .t2]
        else [.t1, .t1, .t2, .t1, .t2])) ∧
    (∀ m : ℕ, 4 ≤ m →
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
        w.get (idx (k.1 + 12)) = .t2 ∧
        w.get (idx (k.1 + 13)) = .t1 ∧
        w.get (idx (k.1 + 14)) = .t2) :=
  ⟨fun m hm => by
    rcases lem_5_1_zone_substitution_geom c₀ m hm with ⟨cyc, hnd, hlen, hset, hfr, hpoly⟩
    refine ⟨cyc, hnd, hlen, hset, fun k => ?_, hpoly⟩
    have hfk := hfr k
    dsimp only at hfk ⊢
    cases ht : (zoneWord m).get (k.cast hlen) <;>
      (rw [ht] at hfk; simpa only [reduceCtorEq, ite_true, ite_false] using hfk),
   zoneWord_part_a, zoneWord_two, zoneWord_three, zoneWord_sigma2_eq, zoneWord_part_c_full⟩

end FejesTothP7.Proofs
