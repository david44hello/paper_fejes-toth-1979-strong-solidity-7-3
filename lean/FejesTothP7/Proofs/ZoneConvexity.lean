module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Proofs.ZoneGeometry

@[expose] public section

/-!
# Global Convexity, Exponential Radial Growth, and Injectivity of Zone Polygons `P_m`

Proves by induction on `m ≥ 1` that the framed zone layers `zoneLayer m` satisfy:
1. `origin ∈ OpenPoly m hm` and `ClosedPoly m hm` is globally convex (`∀ k j, k+1 < j < k+N_m → 0 < detH u_k u_{k+1} u_j`).
2. Exponential radial growth: every vertex `v ∈ zoneVerts m` satisfies
   `v.z ≥ (Real.cosh h7 / Real.cosh r7) ^ m` and `v.z ≥ Real.cosh (2 * r7)`.
3. `(zoneVerts m).Nodup` and every `v ∈ zoneVerts (m + 1)` lies strictly outside `ClosedPoly m hm`.
4. Exact parent-child indexing between `zoneLayer m` and `zoneLayer (m + 1)`.
-/

noncomputable section

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Helper constants and midpoint inequalities -/

/-- Radial growth factor per zone: `c = cosh h7 / cosh r7 > 1`. -/
def zoneGrowthBase : ℝ := Real.cosh h7 / Real.cosh r7

lemma cosh_r7_gt_one : 1 < Real.cosh r7 := by
  rw [cosh_r7]; exact one_lt_inv_two_sin_pi_div_seven

lemma cosh_two_r7_gt_one : 1 < Real.cosh (2 * r7) := by
  rw [cosh_two_r7_eq]; nlinarith [cosh_r7_gt_one]

lemma zoneGrowthBase_gt_one : 1 < zoneGrowthBase := by
  unfold zoneGrowthBase
  rw [one_lt_div (Real.cosh_pos r7), cosh_h7_eq, lt_div_iff₀ (Real.cosh_pos r7), cosh_two_r7_eq]
  nlinarith [cosh_r7_gt_one]

lemma zoneGrowthBase_le_cosh_two_r7 : zoneGrowthBase ≤ Real.cosh (2 * r7) := by
  unfold zoneGrowthBase
  rw [cosh_h7_eq, div_div, div_le_iff₀ (mul_pos (Real.cosh_pos r7) (Real.cosh_pos r7))]
  have h1 : 1 ≤ Real.cosh r7 ^ 2 := by nlinarith [cosh_r7_gt_one]
  have h2 : 0 < Real.cosh (2 * r7) := Real.cosh_pos (2 * r7)
  nlinarith

lemma detH_mid (a b u v : H2) :
    detH a b (mid u v) =
      (detH a b u + detH a b v) / Real.sqrt (2 * (lorentz u v + 1)) := by
  unfold detH mid
  have hD : Real.sqrt (2 * (lorentz u v + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith [one_le_lorentz u v])).ne'
  field_simp [hD]
  ring

lemma mid_mem_closedPolyOf {L : List (ZoneType × (H2 ≃ᵢ H2))} {hL : 0 < L.length}
    {u v : H2} (hu : u ∈ ClosedPolyOf L hL) (hv : v ∈ ClosedPolyOf L hL) :
    mid u v ∈ ClosedPolyOf L hL := by
  intro k
  rw [detH_mid]
  exact div_nonneg (add_nonneg (hu k) (hv k)) (Real.sqrt_nonneg _)

lemma mid_z_of_dist_two_r7 {u v : H2} (hd : dist u v = 2 * r7) :
    (mid u v).z = (u.z + v.z) / (2 * Real.cosh r7) := by
  have hl : lorentz u v = Real.cosh (2 * r7) := by rw [← cosh_dist, hd]
  have hsq : 2 * (lorentz u v + 1) = (2 * Real.cosh r7) ^ 2 := by
    rw [hl, cosh_two_r7_eq]; ring
  change (u.z + v.z) / Real.sqrt (2 * (lorentz u v + 1)) = _
  rw [hsq, Real.sqrt_sq (by linarith [Real.cosh_pos r7])]

/-! ### Parent-index correspondence for `L.flatMap nextLayerEntry` -/

/-- For each element of `L.flatMap nextLayerEntry`, record its parent index (offset by `off`). -/
def parentIdxAux (off : ℕ) : List (ZoneType × (H2 ≃ᵢ H2)) → List ℕ
  | [] => []
  | e :: tl => List.replicate (nextLayerEntry e).length off ++ parentIdxAux (off + 1) tl

lemma nextLayerEntry_length_ge_two (e : ZoneType × (H2 ≃ᵢ H2)) :
    2 ≤ (nextLayerEntry e).length := by
  rcases e with ⟨t, F⟩
  cases t <;> simp [nextLayerEntry]

lemma flatMap_nextLayerEntry_length_pos {L : List (ZoneType × (H2 ≃ᵢ H2))} (hL : 0 < L.length) :
    0 < (L.flatMap nextLayerEntry).length := by
  cases L with
  | nil => simp at hL
  | cons e tl =>
    rw [List.flatMap_cons, List.length_append]
    have := nextLayerEntry_length_ge_two e; omega

lemma parentIdxAux_length (off : ℕ) (L : List (ZoneType × (H2 ≃ᵢ H2))) :
    (parentIdxAux off L).length = (L.flatMap nextLayerEntry).length := by
  induction L generalizing off with
  | nil => rfl
  | cons e tl ih =>
    simp only [parentIdxAux, List.flatMap_cons, List.length_append, List.length_replicate, ih]

lemma parentIdxAux_bounds (off : ℕ) (L : List (ZoneType × (H2 ≃ᵢ H2))) :
    ∀ j : ℕ, (hj : j < (L.flatMap nextLayerEntry).length) →
      off ≤ (parentIdxAux off L)[j]'(by rw [parentIdxAux_length]; exact hj) ∧
      (parentIdxAux off L)[j]'(by rw [parentIdxAux_length]; exact hj) < off + L.length := by
  induction L generalizing off with
  | nil => intro j hj; simp at hj
  | cons e tl ih =>
    intro j hj
    have hj' : j < (nextLayerEntry e).length + (tl.flatMap nextLayerEntry).length := by
      simpa only [List.flatMap_cons, List.length_append] using hj
    have hrep_len : (List.replicate (nextLayerEntry e).length off).length = (nextLayerEntry e).length :=
      List.length_replicate
    by_cases hlt : j < (nextLayerEntry e).length
    · have h1 : (parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj) = off := by
        simp only [parentIdxAux]
        rw [List.getElem_append_left (by rw [hrep_len]; exact hlt), List.getElem_replicate]
      rw [h1]; simp only [List.length_cons]; omega
    · have hge : (List.replicate (nextLayerEntry e).length off).length ≤ j := by omega
      have h1 : (parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj) =
          (parentIdxAux (off + 1) tl)[j - (nextLayerEntry e).length]'(by
            rw [parentIdxAux_length]; omega) := by
        simp only [parentIdxAux]
        rw [List.getElem_append_right hge]
        simp only [hrep_len]
      rw [h1]
      have hrec := ih (off + 1) (j - (nextLayerEntry e).length) (by omega)
      simp only [List.length_cons]; omega

lemma parentIdxAux_mem (off : ℕ) (L : List (ZoneType × (H2 ≃ᵢ H2))) :
    ∀ j : ℕ, (hj : j < (L.flatMap nextLayerEntry).length) →
      let p := (parentIdxAux off L)[j]'(by rw [parentIdxAux_length]; exact hj)
      (L.flatMap nextLayerEntry)[j]'hj ∈
        nextLayerEntry (L[p - off]'(by have := parentIdxAux_bounds off L j hj; omega)) := by
  induction L generalizing off with
  | nil => intro j hj; simp at hj
  | cons e tl ih =>
    intro j hj
    have hj' : j < (nextLayerEntry e).length + (tl.flatMap nextLayerEntry).length := by
      simpa only [List.flatMap_cons, List.length_append] using hj
    have hrep_len : (List.replicate (nextLayerEntry e).length off).length = (nextLayerEntry e).length :=
      List.length_replicate
    by_cases hlt : j < (nextLayerEntry e).length
    · have hp : (parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj) = off := by
        simp only [parentIdxAux]
        rw [List.getElem_append_left (by rw [hrep_len]; exact hlt), List.getElem_replicate]
      have hget : ((e :: tl).flatMap nextLayerEntry)[j]'hj = (nextLayerEntry e)[j]'hlt := by
        simp only [List.flatMap_cons]
        exact List.getElem_append_left hlt
      change ((e :: tl).flatMap nextLayerEntry)[j]'hj ∈ nextLayerEntry ((e :: tl)[_ - off]'_)
      rw [hget]
      have hsub : ((parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj)) - off = 0 := by
        rw [hp]; omega
      simp only [hsub, List.getElem_cons_zero]
      exact List.getElem_mem hlt
    · have hge : (nextLayerEntry e).length ≤ j := by omega
      have hge' : (List.replicate (nextLayerEntry e).length off).length ≤ j := by omega
      have hp : (parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj) =
          (parentIdxAux (off + 1) tl)[j - (nextLayerEntry e).length]'(by
            rw [parentIdxAux_length]; omega) := by
        simp only [parentIdxAux]
        rw [List.getElem_append_right hge']
        simp only [hrep_len]
      have hget : ((e :: tl).flatMap nextLayerEntry)[j]'hj =
          (tl.flatMap nextLayerEntry)[j - (nextLayerEntry e).length]'(by omega) := by
        simp only [List.flatMap_cons]
        exact List.getElem_append_right hge
      change ((e :: tl).flatMap nextLayerEntry)[j]'hj ∈ nextLayerEntry ((e :: tl)[_ - off]'_)
      rw [hget]
      have hrec := ih (off + 1) (j - (nextLayerEntry e).length) (by omega)
      have hb := parentIdxAux_bounds (off + 1) tl (j - (nextLayerEntry e).length) (by omega)
      set p' := (parentIdxAux (off + 1) tl)[j - (nextLayerEntry e).length]'(by rw [parentIdxAux_length]; omega)
      have hsub : ((parentIdxAux off (e :: tl))[j]'(by rw [parentIdxAux_length]; exact hj)) - off =
          (p' - (off + 1)) + 1 := by
        rw [hp]; omega
      simp only [hsub, List.getElem_cons_succ]
      exact hrec

lemma parentIdxAux_zero (off : ℕ) {L : List (ZoneType × (H2 ≃ᵢ H2))} (hL : 0 < L.length) :
    (parentIdxAux off L)[0]'(by rw [parentIdxAux_length]; exact flatMap_nextLayerEntry_length_pos hL) = off := by
  cases L with
  | nil => simp at hL
  | cons e tl =>
    simp only [parentIdxAux]
    have hpos : 0 < (nextLayerEntry e).length := by have := nextLayerEntry_length_ge_two e; omega
    rw [List.getElem_append_left (by simp only [List.length_replicate]; exact hpos), List.getElem_replicate]

lemma parentIdxAux_cons_left (off : ℕ) (e : ZoneType × (H2 ≃ᵢ H2)) (tl : List (ZoneType × (H2 ≃ᵢ H2)))
    (i : ℕ) (hi : i < (parentIdxAux off (e :: tl)).length) (hlt : i < (nextLayerEntry e).length) :
    (parentIdxAux off (e :: tl))[i]'hi = off := by
  have hi' : i < (List.replicate (nextLayerEntry e).length off ++ parentIdxAux (off + 1) tl).length := hi
  have hlt' : i < (List.replicate (nextLayerEntry e).length off).length := by
    simp only [List.length_replicate]; exact hlt
  calc (parentIdxAux off (e :: tl))[i]'hi
      = (List.replicate (nextLayerEntry e).length off ++ parentIdxAux (off + 1) tl)[i]'hi' := rfl
    _ = (List.replicate (nextLayerEntry e).length off)[i]'hlt' := List.getElem_append_left hlt'
    _ = off := List.getElem_replicate hlt'

lemma parentIdxAux_cons_right (off : ℕ) (e : ZoneType × (H2 ≃ᵢ H2)) (tl : List (ZoneType × (H2 ≃ᵢ H2)))
    (i : ℕ) (hi : i < (parentIdxAux off (e :: tl)).length) (hge : (nextLayerEntry e).length ≤ i) :
    (parentIdxAux off (e :: tl))[i]'hi =
      (parentIdxAux (off + 1) tl)[i - (nextLayerEntry e).length]'(by
        have : i < (nextLayerEntry e).length + (parentIdxAux (off + 1) tl).length := by
          simpa only [parentIdxAux, List.length_append, List.length_replicate] using hi
        omega) := by
  have hi' : i < (List.replicate (nextLayerEntry e).length off ++ parentIdxAux (off + 1) tl).length := hi
  have hge' : (List.replicate (nextLayerEntry e).length off).length ≤ i := by
    simp only [List.length_replicate]; exact hge
  calc (parentIdxAux off (e :: tl))[i]'hi
      = (List.replicate (nextLayerEntry e).length off ++ parentIdxAux (off + 1) tl)[i]'hi' := rfl
    _ = (parentIdxAux (off + 1) tl)[i - (List.replicate (nextLayerEntry e).length off).length]'(by
          have : i < (nextLayerEntry e).length + (parentIdxAux (off + 1) tl).length := by
            simpa only [List.length_append, List.length_replicate] using hi'
          simp only [List.length_replicate]; omega) := List.getElem_append_right hge'
    _ = (parentIdxAux (off + 1) tl)[i - (nextLayerEntry e).length]'_ := by
          simp only [List.length_replicate]

lemma parentIdxAux_last (off : ℕ) {L : List (ZoneType × (H2 ≃ᵢ H2))} (hL : 0 < L.length) :
    (parentIdxAux off L)[(L.flatMap nextLayerEntry).length - 1]'(by
      rw [parentIdxAux_length]; have := flatMap_nextLayerEntry_length_pos hL; omega) =
      off + L.length - 1 := by
  induction L generalizing off with
  | nil => simp at hL
  | cons e tl ih =>
    cases tl with
    | nil =>
      have hflat : ([e].flatMap nextLayerEntry).length = (nextLayerEntry e).length := by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hpos : 0 < (nextLayerEntry e).length := by have := nextLayerEntry_length_ge_two e; omega
      rw [parentIdxAux_cons_left (hlt := by omega)]
      simp only [List.length_cons, List.length_nil]; omega
    | cons e2 tl2 =>
      have htl_pos : 0 < (e2 :: tl2).length := by simp
      have htl_flat_pos : 0 < ((e2 :: tl2).flatMap nextLayerEntry).length :=
        flatMap_nextLayerEntry_length_pos htl_pos
      have hlen_cons : ((e :: e2 :: tl2).flatMap nextLayerEntry).length =
          (nextLayerEntry e).length + ((e2 :: tl2).flatMap nextLayerEntry).length := by
        rw [List.flatMap_cons, List.length_append]
      rw [parentIdxAux_cons_right (hge := by omega)]
      have hsub : ((e :: e2 :: tl2).flatMap nextLayerEntry).length - 1 - (nextLayerEntry e).length =
          ((e2 :: tl2).flatMap nextLayerEntry).length - 1 := by omega
      simp only [hsub]
      rw [ih (off + 1) htl_pos]
      simp only [List.length_cons]; omega

lemma parentIdxAux_step (off : ℕ) (L : List (ZoneType × (H2 ≃ᵢ H2))) :
    ∀ j : ℕ, (hj : j + 1 < (L.flatMap nextLayerEntry).length) →
      let a := (parentIdxAux off L)[j]'(by rw [parentIdxAux_length]; omega)
      let b := (parentIdxAux off L)[j + 1]'(by rw [parentIdxAux_length]; exact hj)
      b = a ∨ b = a + 1 := by
  induction L generalizing off with
  | nil => intro j hj; simp at hj
  | cons e tl ih =>
    intro j hj
    have hj' : j + 1 < (nextLayerEntry e).length + (tl.flatMap nextLayerEntry).length := by
      simpa only [List.flatMap_cons, List.length_append] using hj
    by_cases h1 : j + 1 < (nextLayerEntry e).length
    · left
      rw [parentIdxAux_cons_left (hlt := h1), parentIdxAux_cons_left (hlt := by omega)]
    · by_cases h2 : j + 1 = (nextLayerEntry e).length
      · right
        have htl_pos : 0 < tl.length := by
          cases tl with
          | nil => simp only [List.flatMap_nil, List.length_nil] at hj'; omega
          | cons _ _ => simp
        rw [parentIdxAux_cons_right (hge := by omega), parentIdxAux_cons_left (hlt := by omega)]
        have hzero : j + 1 - (nextLayerEntry e).length = 0 := by omega
        simp only [hzero]
        exact parentIdxAux_zero (off + 1) htl_pos
      · have hge : (nextLayerEntry e).length ≤ j := by omega
        have hrec := ih (off + 1) (j - (nextLayerEntry e).length) (by omega)
        have hsub : j + 1 - (nextLayerEntry e).length = (j - (nextLayerEntry e).length) + 1 := by omega
        dsimp only
        rw [parentIdxAux_cons_right (hge := by omega), parentIdxAux_cons_right (hge := hge)]
        simp only [hsub]
        exact hrec

/-- Periodic parent index map `p : ℕ → ℕ` from `L.flatMap nextLayerEntry` to `L`. -/
def periodicParent (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) (j : ℕ) : ℕ :=
  (j / (L.flatMap nextLayerEntry).length) * L.length +
    (parentIdxAux 0 L)[j % (L.flatMap nextLayerEntry).length]'(by
      rw [parentIdxAux_length]; exact Nat.mod_lt j (flatMap_nextLayerEntry_length_pos hL))

lemma periodicParent_add_len (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) (j : ℕ) :
    periodicParent L hL (j + (L.flatMap nextLayerEntry).length) =
      periodicParent L hL j + L.length := by
  have hW : 0 < (L.flatMap nextLayerEntry).length := flatMap_nextLayerEntry_length_pos hL
  unfold periodicParent
  simp only [Nat.add_div_right _ hW, Nat.add_mod_right]
  ring

lemma periodicParent_step (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) (j : ℕ) :
    periodicParent L hL (j + 1) = periodicParent L hL j ∨
    periodicParent L hL (j + 1) = periodicParent L hL j + 1 := by
  have hW : 0 < (L.flatMap nextLayerEntry).length := flatMap_nextLayerEntry_length_pos hL
  set M := (L.flatMap nextLayerEntry).length
  unfold periodicParent
  change (j + 1) / M * L.length + (parentIdxAux 0 L)[(j + 1) % M]'_ =
      j / M * L.length + (parentIdxAux 0 L)[j % M]'_ ∨
    (j + 1) / M * L.length + (parentIdxAux 0 L)[(j + 1) % M]'_ =
      j / M * L.length + (parentIdxAux 0 L)[j % M]'_ + 1
  by_cases hlast : j % M + 1 < M
  · have hdiv : (j + 1) / M = j / M := by
      have h1 : j + 1 = M * (j / M) + (j % M + 1) := by
        have := (Nat.div_add_mod j M).symm; omega
      rw [h1, Nat.mul_add_div hW, Nat.div_eq_of_lt hlast, add_zero]
    have hmod : (j + 1) % M = j % M + 1 := by
      have h1 : j + 1 = M * (j / M) + (j % M + 1) := by
        have := (Nat.div_add_mod j M).symm; omega
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlast]
    have hst := parentIdxAux_step 0 L (j % M) hlast
    simp only [hdiv, hmod]
    rcases hst with h | h
    · left; rw [h]
    · right; rw [h]; omega
  · have hrem : j % M = M - 1 := by have := Nat.mod_lt j hW; omega
    have hdiv : (j + 1) / M = j / M + 1 := by
      have h1 : j + 1 = (j / M + 1) * M := by
        have := (Nat.div_add_mod' j M).symm; rw [add_mul, one_mul]; omega
      rw [h1, Nat.mul_div_cancel _ hW]
    have hmod : (j + 1) % M = 0 := by
      have h1 : j + 1 = (j / M + 1) * M := by
        have := (Nat.div_add_mod' j M).symm; rw [add_mul, one_mul]; omega
      rw [h1, Nat.mul_mod_left]
    right
    simp only [hdiv, hmod, hrem]
    rw [parentIdxAux_zero 0 hL, parentIdxAux_last 0 hL]
    have h1 : 0 + L.length - 1 + 1 = L.length := by omega
    nlinarith

lemma periodicParent_mem (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length)
    (hW : 0 < (L.flatMap nextLayerEntry).length) (j : ℕ) :
    (L.flatMap nextLayerEntry).get ⟨j % (L.flatMap nextLayerEntry).length, Nat.mod_lt _ hW⟩ ∈
      nextLayerEntry (L.get ⟨periodicParent L hL j % L.length, Nat.mod_lt _ hL⟩) := by
  have hb := parentIdxAux_bounds 0 L (j % (L.flatMap nextLayerEntry).length) (Nat.mod_lt _ hW)
  have hmod : periodicParent L hL j % L.length =
      (parentIdxAux 0 L)[j % (L.flatMap nextLayerEntry).length]'(by
        rw [parentIdxAux_length]; exact Nat.mod_lt _ hW) := by
    unfold periodicParent
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hmem := parentIdxAux_mem 0 L (j % (L.flatMap nextLayerEntry).length) (Nat.mod_lt _ hW)
  simp only [Nat.sub_zero] at hmem
  simp only [List.get_eq_getElem, hmod]
  exact hmem

/-! ### Normal-functional radial lower bounds for children of a convex layer -/

lemma stepFrame_origin_eq (F : H2 ≃ᵢ H2) (a d : ℤ) :
    stepFrame F a d origin = F (polarOrigin (2 * r7) ((a : ℝ) * α7)) := by
  simp only [stepFrame, IsometryEquiv.trans_apply]
  have h0 : (rot7 ^ (-d)) origin = origin := by
    rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
    simp [polarOrigin_zero]
  rw [h0, halfTurn_origin, rot7_zpow_apply_polarOrigin, zero_add]

lemma z_ge_of_type1_child {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c)
    (ho : origin ∈ ClosedPolyOf L hAdj.1)
    (k : ℕ) {j : ℤ}
    (hj : ((L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩).1 = .t1 ∧ j = 4) ∨ j = 5) :
    let e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    Real.cosh (2 * r7) * (layerVert L hAdj.1 k).z ≤ (e.2 (polarOrigin (2 * r7) ((j : ℝ) * α7))).z := by
  intro e
  set u := layerVert L hAdj.1 k
  set uNext := layerVert L hAdj.1 (k + 1)
  set uPrev := layerVert L hAdj.1 (k + L.length - 1)
  set v' := e.2 (polarOrigin (2 * r7) ((j : ℝ) * α7))
  have he_next : uNext = e.2 (polarOrigin (2 * r7) 0) := by
    have h := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    simpa [uNext, e, layerVert, Nat.mod_add_mod] using adjFrame_origin_eq h
  have he_prev : uPrev = e.2 (polarOrigin (2 * r7) (((e.1.innerCount + 1 : ℕ) : ℝ) * α7)) := by
    have hidx : ((k + L.length - 1) % L.length + 1) % L.length = k % L.length := by
      have hpos := hAdj.1
      rw [Nat.mod_add_mod]
      have heq : k + L.length - 1 + 1 = k + L.length := by omega
      rw [heq, Nat.add_mod_right]
    have h := hAdj.2 ⟨(k + L.length - 1) % L.length, Nat.mod_lt _ hAdj.1⟩
    have h1 := adjFrame_prev_eq h
    simp only [hidx] at h1
    exact h1.symm
  have hy_next : 0 ≤ detH u uNext origin := ho k
  have hy_prev : 0 ≤ detH u origin uPrev := by
    have h1 := ho (k + L.length - 1)
    have h2 : layerVert L hAdj.1 (k + L.length - 1 + 1) = u := by
      have hpos := hAdj.1
      have heq : k + L.length - 1 + 1 = k + L.length := by omega
      rw [heq, layerVert_add_len]
    rw [h2] at h1
    rwa [detH_cyclic] at h1
  have hab : 0 < detH u uNext uPrev := by
    rw [show u = e.2 origin from rfl, he_next, he_prev, hDet e (List.get_mem _ _)]
    have hcalc : ∀ θ : ℝ, detH origin (polarOrigin (2 * r7) 0) (polarOrigin (2 * r7) θ) =
        Real.sinh (2 * r7) ^ 2 * Real.sin θ := by
      intro θ; unfold detH origin polarOrigin
      simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]; ring
    rw [hcalc]
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hsin : 0 < Real.sin (((e.1.innerCount + 1 : ℕ) : ℝ) * α7) := by
      cases e.1 <;>
      · simp only [ZoneType.innerCount]
        apply Real.sin_pos_of_pos_of_lt_pi <;>
        · unfold α7 alphaP; push_cast; linarith [Real.pi_pos]
    positivity
  have hnorm_calc : ∀ θ₁ θ₂ : ℝ,
      normalFunc origin (polarOrigin (2 * r7) θ₁) (polarOrigin (2 * r7) θ₂) =
        -(Real.sinh (2 * r7) ^ 2 * Real.cos (θ₁ - θ₂)) := by
    intro θ₁ θ₂; unfold normalFunc
    rw [lorentz_polarOrigin, lorentz_symm _ origin, lorentz_origin_polarOrigin, lorentz_origin_polarOrigin]
    ring
  have hcos_neg : ∀ φ : ℝ, Real.pi / 2 < φ → φ < 3 * Real.pi / 2 → Real.cos φ < 0 := by
    intro φ hlo hhi
    by_cases hpi : φ ≤ Real.pi
    · simpa using Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], hpi⟩ hlo
    · push Not at hpi
      rw [← Real.cos_two_pi_sub]
      simpa using Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith : Real.pi / 2 < 2 * Real.pi - φ)
  have hxa : 0 ≤ normalFunc u v' uNext := by
    rw [show u = e.2 origin from rfl, he_next, normalFunc_isometry, hnorm_calc, sub_zero]
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hc : Real.cos ((j : ℝ) * α7) < 0 := by
      rcases hj with ⟨_, rfl⟩ | rfl <;>
      · apply hcos_neg <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
    nlinarith [sq_pos_of_pos hsh]
  have hxb : 0 ≤ normalFunc u v' uPrev := by
    rw [show u = e.2 origin from rfl, he_prev, normalFunc_isometry, hnorm_calc]
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hc : Real.cos ((j : ℝ) * α7 - ((e.1.innerCount + 1 : ℕ) : ℝ) * α7) < 0 := by
      rcases hj with ⟨ht1, rfl⟩ | rfl
      · rw [ht1]; simp only [ZoneType.innerCount]
        apply hcos_neg <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
      · cases e.1 <;>
        · simp only [ZoneType.innerCount]
          apply hcos_neg <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
    nlinarith [sq_pos_of_pos hsh]
  have hn := normalFunc_wedge_nonneg hab hy_next hy_prev hxa hxb
  unfold normalFunc at hn
  have hl1 : lorentz v' origin = v'.z := by unfold lorentz origin; ring
  have hl2 : lorentz u origin = u.z := by unfold lorentz origin; ring
  have hl3 : lorentz v' u = Real.cosh (2 * r7) := by
    rw [show u = e.2 origin from rfl, isometry_lorentz, lorentz_symm, lorentz_origin_polarOrigin]
  rw [hl1, hl2, hl3] at hn
  linarith

lemma z_ge_of_type2_child {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c)
    (ho : origin ∈ ClosedPolyOf L hAdj.1) (k : ℕ) :
    let e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    Real.cosh h7 * (mid (layerVert L hAdj.1 k) (layerVert L hAdj.1 (k + 1))).z ≤
      (e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7))).z := by
  intro e
  set u := layerVert L hAdj.1 k
  set uNext := layerVert L hAdj.1 (k + 1)
  set M := mid u uNext
  set w := e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7))
  have he_next : uNext = e.2 (polarOrigin (2 * r7) 0) := by
    have h := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    simpa [uNext, e, layerVert, Nat.mod_add_mod] using adjFrame_origin_eq h
  set G : H2 ≃ᵢ H2 := (boostX r7).trans e.2
  have hG_o : G origin = M := by
    simp only [G, IsometryEquiv.trans_apply, boostX_apply_origin]
    rw [show M = mid (e.2 origin) (e.2 (polarOrigin (2 * r7) 0)) by rw [← he_next]; rfl, mid_frame_edge]
  have hG_u : G (polarOrigin (-r7) 0) = u := by
    simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, neg_add_cancel,
      polarOrigin_zero]; rfl
  have hG_uNext : G (polarOrigin r7 0) = uNext := by
    simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, ← two_mul, he_next]
  have hG_w : G (polarOrigin h7 (-(Real.pi / 2))) = w := by
    simp only [G, IsometryEquiv.trans_apply, boostX_r7_altitude, w]
    congr 1
    have h6 : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
    rw [h6, polarOrigin_add_two_pi]
  have hG_det : ∀ a b c, detH (G a) (G b) (G c) = detH a b c := by
    intro a b c
    simp only [G, IsometryEquiv.trans_apply, hDet e (List.get_mem _ _), detH_boostX]
  set y0 := G.symm origin
  have hy_eq : origin = G y0 := by simp [y0]
  have hn : 0 ≤ normalFunc M w origin := by
    rw [hy_eq, ← hG_o, ← hG_w, normalFunc_isometry]
    apply normalFunc_edge_origin_nonneg r7_pos h7_pos y0
    rw [← hG_det, hG_u, hG_uNext, ← hy_eq]
    exact ho k
  unfold normalFunc at hn
  have hl1 : lorentz w origin = w.z := by unfold lorentz origin; ring
  have hl2 : lorentz M origin = M.z := by unfold lorentz origin; ring
  have hl3 : lorentz w M = Real.cosh h7 := by
    rw [← hG_w, ← hG_o, isometry_lorentz, lorentz_symm, lorentz_origin_polarOrigin]
  rw [hl1, hl2, hl3] at hn
  linarith

/-! ### Global convexity invariant for `zoneLayer m` (`m ≥ 1`) -/

/-- Radius of `klein p` in `ℝ²`. -/
def kleinNorm (p : H2) : ℝ :=
  Real.sqrt ((klein p).1 ^ 2 + (klein p).2 ^ 2)

lemma kleinNorm_pos_of_z_gt_one {p : H2} (hz : 1 < p.z) : 0 < kleinNorm p := by
  unfold kleinNorm klein
  apply Real.sqrt_pos.mpr
  have h1 : (p.x / p.z) ^ 2 + (p.y / p.z) ^ 2 = (p.z ^ 2 - 1) / p.z ^ 2 := by
    have hs := p.on_sheet
    have hpz : p.z ≠ 0 := p.hz.ne'
    field_simp [hpz]
    linarith
  rw [h1]
  exact div_pos (by nlinarith) (sq_pos_of_pos p.hz)

lemma klein_dot_pos_of_dist_two_r7 {u v : H2}
    (hu : Real.cosh (2 * r7) ≤ u.z) (hv : Real.cosh (2 * r7) ≤ v.z)
    (hd : dist u v = 2 * r7) :
    0 < (klein u).1 * (klein v).1 + (klein u).2 * (klein v).2 := by
  have hl : lorentz u v = Real.cosh (2 * r7) := by rw [← cosh_dist, hd]
  unfold lorentz at hl
  unfold klein
  have h1 : (u.x / u.z) * (v.x / v.z) + (u.y / u.z) * (v.y / v.z) =
      (u.z * v.z - Real.cosh (2 * r7)) / (u.z * v.z) := by
    have huz : u.z ≠ 0 := u.hz.ne'
    have hvz : v.z ≠ 0 := v.hz.ne'
    field_simp [huz, hvz]
    linarith
  rw [h1]
  have hgt := cosh_two_r7_gt_one
  exact div_pos (by nlinarith) (mul_pos u.hz v.hz)

/-- Full geometric invariant carried by induction on `m ≥ 1`. -/
structure ZoneConvexInv (m : ℕ) (hm : 1 ≤ m) : Prop where
  origin_open : origin ∈ OpenPoly m hm
  globally_convex : ∀ k j : ℕ, k + 1 < j → j < k + (zoneLayer m).length →
    0 < detH (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k)
      (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) (k + 1))
      (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) j)
  z_ge_cosh : ∀ k : ℕ, Real.cosh (2 * r7) ≤ (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k).z
  z_ge_pow : ∀ k : ℕ, zoneGrowthBase ^ m ≤ (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k).z
  lifted_angle : ∃ θ : ℕ → ℝ,
    (∀ k, 0 < θ (k + 1) - θ k ∧ θ (k + 1) - θ k < Real.pi) ∧
    (∀ k, θ (k + (zoneLayer m).length) = θ k + 2 * Real.pi) ∧
    (∀ k, klein (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k) =
      (kleinNorm (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k) * Real.cos (θ k),
       kleinNorm (layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k) * Real.sin (θ k)))

lemma layerVert_mem_closedPoly {m : ℕ} {hm : 1 ≤ m} (hInv : ZoneConvexInv m hm) (k : ℕ) :
    layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k ∈ ClosedPoly m hm := by
  intro i
  set hL := zoneLayer_length_pos m hm
  set N := (zoneLayer m).length
  set r := (k + N - i % N) % N
  have hr_lt : r < N := Nat.mod_lt _ hL
  have hmod_nat : (i + r) % N = k % N := by
    have h1 : (i + r) % N = (i % N + (k + N - i % N)) % N := by
      simp only [r]
      rw [Nat.add_mod_mod, Nat.mod_add_mod]
    have h2 : i % N < N := Nat.mod_lt i hL
    have h3 : i % N + (k + N - i % N) = k + N := by omega
    rw [h1, h3, Nat.add_mod_right]
  have hmod : layerVert (zoneLayer m) hL k = layerVert (zoneLayer m) hL (i + r) := by
    unfold layerVert
    have hfin : (⟨k % N, Nat.mod_lt k hL⟩ : Fin N) = ⟨(i + r) % N, Nat.mod_lt (i + r) hL⟩ :=
      Fin.ext hmod_nat.symm
    exact congrArg (fun x => ((zoneLayer m).get x).2 origin) hfin
  rw [hmod]
  by_cases hr0 : r = 0
  · rw [hr0, add_zero]; unfold detH; linarith
  · by_cases hr1 : r = 1
    · rw [hr1]; unfold detH; linarith
    · exact (hInv.globally_convex i (i + r) (by omega) (by omega)).le

lemma zoneLayer1_layerVert (k : ℕ) :
    layerVert zoneLayer1 (by rw [zoneLayer1_length]; omega) k =
      polarOrigin (2 * r7) ((k : ℝ) * α7) := by
  unfold layerVert
  rw [zoneLayer1_get]
  simp only [IsometryEquiv.trans_apply]
  have h0 : (rot7 ^ (-1 : ℤ)) origin = origin := by
    rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
    simp [polarOrigin_zero]
  rw [h0, halfTurn_origin, rot7_zpow_apply_polarOrigin, zero_add]
  have hlen : zoneLayer1.length = 7 := zoneLayer1_length
  have hmod : (((k % zoneLayer1.length : ℕ) : ℤ) : ℝ) * α7 =
      (k : ℝ) * α7 - ((k / 7 : ℕ) : ℝ) * (2 * Real.pi) := by
    have hdiv : k = 7 * (k / 7) + k % 7 := (Nat.div_add_mod k 7).symm
    have hcast : (k : ℝ) = 7 * (k / 7 : ℕ) + (k % 7 : ℕ) := by exact_mod_cast hdiv
    rw [hlen, Int.cast_natCast]
    have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; ring
    linear_combination -α7 * hcast - (k / 7 : ℕ) * h7a
  have hper : ∀ (n : ℕ) (θ : ℝ), polarOrigin (2 * r7) (θ - (n : ℝ) * (2 * Real.pi)) = polarOrigin (2 * r7) θ := by
    intro n θ
    induction n with
    | zero => simp
    | succ m ih =>
      have heq : θ - ((m + 1 : ℕ) : ℝ) * (2 * Real.pi) + 2 * Real.pi = θ - (m : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      rw [← polarOrigin_add_two_pi, heq, ih]
  rw [hmod, hper]

/-- Base case `m = 1` of `ZoneConvexInv`. -/
theorem zoneConvexInv_one : ZoneConvexInv 1 (by omega) := by
  have hlen : (zoneLayer 1).length = 7 := zoneLayer1_length
  have hv : ∀ k, layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) k =
      polarOrigin (2 * r7) ((k : ℝ) * α7) := zoneLayer1_layerVert
  have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hch : 0 < Real.cosh (2 * r7) := Real.cosh_pos (2 * r7)
  have hsin_a : 0 < Real.sin α7 := Real.sin_pos_of_pos_of_lt_pi
    (by unfold α7 alphaP; positivity) (by unfold α7 alphaP; linarith [Real.pi_pos])
  have hklein : ∀ k : ℕ, klein (polarOrigin (2 * r7) ((k : ℝ) * α7)) =
      ((Real.sinh (2 * r7) / Real.cosh (2 * r7)) * Real.cos ((k : ℝ) * α7),
       (Real.sinh (2 * r7) / Real.cosh (2 * r7)) * Real.sin ((k : ℝ) * α7)) := by
    intro k; unfold klein polarOrigin; ext <;> ring
  have hknorm : ∀ k : ℕ, kleinNorm (polarOrigin (2 * r7) ((k : ℝ) * α7)) =
      Real.sinh (2 * r7) / Real.cosh (2 * r7) := by
    intro k
    unfold kleinNorm
    rw [hklein k]
    have htrig := Real.cos_sq_add_sin_sq ((k : ℝ) * α7)
    have hsq : ((Real.sinh (2 * r7) / Real.cosh (2 * r7)) * Real.cos ((k : ℝ) * α7)) ^ 2 +
        ((Real.sinh (2 * r7) / Real.cosh (2 * r7)) * Real.sin ((k : ℝ) * α7)) ^ 2 =
        (Real.sinh (2 * r7) / Real.cosh (2 * r7)) ^ 2 := by
      linear_combination (Real.sinh (2 * r7) / Real.cosh (2 * r7)) ^ 2 * htrig
    rw [hsq, Real.sqrt_sq (div_pos hsh hch).le]
  have hloc : ∀ k, 0 < orient2D (klein (layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) k))
      (klein (layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) (k + 1)))
      (klein (layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) (k + 2))) := by
    intro k
    rw [← detH_pos_iff_orient2D_pos]
    exact cyclicAdj_local_convex (zoneLayer_cyclicAdj 1 (by omega))
      (fun e he => (zoneLayer_mem_Delta237_and_detH 1 e he).2) k
  have hglob := starShaped_locallyConvex_globallyConvex (N := (zoneLayer 1).length) (by omega)
    (fun k => klein (layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) k))
    (fun k => by rw [layerVert_add_len])
    (fun k => kleinNorm (layerVert (zoneLayer 1) (zoneLayer_length_pos 1 (by omega)) k))
    (fun k => (k : ℝ) * α7)
    (fun k => by rw [hv k, hknorm k]; exact div_pos hsh hch)
    (fun k => by rw [hv k, hknorm k, hklein k])
    (fun k => by
      have : ((k + 1 : ℕ) : ℝ) * α7 - (k : ℝ) * α7 = α7 := by push_cast; ring
      rw [this]; unfold α7 alphaP; constructor <;> linarith [Real.pi_pos])
    (fun k => by rw [hlen]; unfold α7 alphaP; push_cast; ring)
    hloc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [hv k, hv (k + 1)]
    have hcalc : detH (polarOrigin (2 * r7) ((k : ℝ) * α7))
        (polarOrigin (2 * r7) (((k + 1 : ℕ) : ℝ) * α7)) origin =
        Real.sinh (2 * r7) ^ 2 * Real.sin α7 := by
      unfold detH polarOrigin origin
      have hsub : ((k + 1 : ℕ) : ℝ) * α7 - (k : ℝ) * α7 = α7 := by push_cast; ring
      have hsin_eq : Real.sin α7 = Real.sin (((k + 1 : ℕ) : ℝ) * α7 - (k : ℝ) * α7) := by rw [hsub]
      rw [hsin_eq, Real.sin_sub]
      ring
    rw [hcalc]
    positivity
  · intro k j hkj hjN
    rw [detH_pos_iff_orient2D_pos]
    exact hglob k j hkj hjN
  · intro k; rw [hv k]; exact le_rfl
  · intro k; rw [hv k, pow_one]; exact zoneGrowthBase_le_cosh_two_r7
  · refine ⟨fun k => (k : ℝ) * α7, ?_, ?_, ?_⟩
    · intro k
      have : ((k + 1 : ℕ) : ℝ) * α7 - (k : ℝ) * α7 = α7 := by push_cast; ring
      rw [this]; unfold α7 alphaP; constructor <;> linarith [Real.pi_pos]
    · intro k; rw [hlen]; unfold α7 alphaP; push_cast; ring
    · intro k; rw [hv k, hknorm k, hklein k]

/-- Helper: lift angle `ψ₀` near `θ₀` given positive dot product in `ℝ²`. -/
lemma exists_angle_near_of_dot_pos {x y R θ₀ : ℝ} (hR : 0 < R) (hxy : x ^ 2 + y ^ 2 = R ^ 2)
    (hdot : 0 < Real.cos θ₀ * x + Real.sin θ₀ * y) :
    ∃ ψ₀ : ℝ, -(Real.pi / 2) < ψ₀ - θ₀ ∧ ψ₀ - θ₀ < Real.pi / 2 ∧
      x = R * Real.cos ψ₀ ∧ y = R * Real.sin ψ₀ := by
  set c := (Real.cos θ₀ * x + Real.sin θ₀ * y) / R
  set s := (-Real.sin θ₀ * x + Real.cos θ₀ * y) / R
  have hc_pos : 0 < c := div_pos hdot hR
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, div_pow, ← add_div]
    rw [div_eq_one_iff_eq (pow_ne_zero 2 hR.ne')]
    have htrig := Real.cos_sq_add_sin_sq θ₀
    linear_combination (x ^ 2 + y ^ 2) * htrig + hxy
  have hc_le : c ≤ 1 := by nlinarith [sq_nonneg s]
  have hc_ge : -1 ≤ c := by nlinarith [sq_nonneg s]
  by_cases hs : 0 ≤ s
  · refine ⟨θ₀ + Real.arccos c, ?_, ?_, ?_, ?_⟩
    · have := Real.arccos_nonneg c; linarith [Real.pi_pos]
    · have := Real.arccos_lt_pi_div_two.mpr hc_pos; linarith
    · rw [Real.cos_add, Real.cos_arccos hc_ge hc_le, Real.sin_arccos,
        show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs]
      have htrig := Real.cos_sq_add_sin_sq θ₀
      simp only [c, s]; field_simp [hR.ne']; linear_combination -x * htrig
    · rw [Real.sin_add, Real.cos_arccos hc_ge hc_le, Real.sin_arccos,
        show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs]
      have htrig := Real.cos_sq_add_sin_sq θ₀
      simp only [c, s]; field_simp [hR.ne']; linear_combination -y * htrig
  · refine ⟨θ₀ - Real.arccos c, ?_, ?_, ?_, ?_⟩
    · have := Real.arccos_lt_pi_div_two.mpr hc_pos; linarith
    · have := Real.arccos_nonneg c; linarith [Real.pi_pos]
    · rw [Real.cos_sub, Real.cos_arccos hc_ge hc_le, Real.sin_arccos,
        show 1 - c ^ 2 = (-s) ^ 2 by linarith, Real.sqrt_sq (by linarith)]
      have htrig := Real.cos_sq_add_sin_sq θ₀
      simp only [c, s]; field_simp [hR.ne']; linear_combination -x * htrig
    · rw [Real.sin_sub, Real.cos_arccos hc_ge hc_le, Real.sin_arccos,
        show 1 - c ^ 2 = (-s) ^ 2 by linarith, Real.sqrt_sq (by linarith)]
      have htrig := Real.cos_sq_add_sin_sq θ₀
      simp only [c, s]; field_simp [hR.ne']; linear_combination -y * htrig

lemma closedPoly_subset_openPoly_succ (m : ℕ) (hm : 1 ≤ m) :
    ClosedPoly m hm ⊆ OpenPoly (m + 1) (by omega) := by
  cases m with
  | zero => omega
  | succ n =>
    exact closedPoly_subset_openPoly_next (zoneLayer_cyclicAdj (n + 1) hm)
      (fun e he => (zoneLayer_mem_Delta237_and_detH (n + 1) e he).2)
      (flatMap_nextLayerEntry_cyclicAdj (zoneLayer_cyclicAdj (n + 1) hm))

/-- Inductive step `m → m + 1` of `ZoneConvexInv`. -/
theorem zoneConvexInv_step {m : ℕ} (hm : 1 ≤ m) (hInv : ZoneConvexInv m hm) :
    ZoneConvexInv (m + 1) (by omega) := by
  have hsucc : zoneLayer (m + 1) = (zoneLayer m).flatMap nextLayerEntry := by
    cases m with
    | zero => omega
    | succ n => rfl
  set hL := zoneLayer_length_pos m hm
  set hAdj := zoneLayer_cyclicAdj m hm
  set hDet := fun e he => (zoneLayer_mem_Delta237_and_detH m e he).2
  set hW := zoneLayer_length_pos (m + 1) (by omega)
  have hW_pos : 0 < ((zoneLayer m).flatMap nextLayerEntry).length :=
    flatMap_nextLayerEntry_length_pos hL
  have ho_closed : origin ∈ ClosedPoly m hm := fun k => (hInv.origin_open k).le
  -- 1. origin ∈ OpenPoly (m + 1)
  have ho_next : origin ∈ OpenPoly (m + 1) (by omega) :=
    closedPoly_subset_openPoly_succ m hm ho_closed
  -- 2. Radial lower bounds for every vertex j of zoneLayer (m + 1)
  have hchild_info : ∀ j : ℕ,
      let k := periodicParent (zoneLayer m) hL j
      let v' := layerVert (zoneLayer (m + 1)) hW j
      dist (layerVert (zoneLayer m) hL k) v' = 2 * r7 ∧
      Real.cosh (2 * r7) ≤ v'.z ∧
      zoneGrowthBase ^ (m + 1) ≤ v'.z := by
    intro j
    set k := periodicParent (zoneLayer m) hL j
    set e := (zoneLayer m).get ⟨k % (zoneLayer m).length, Nat.mod_lt _ hL⟩
    set wEntry := ((zoneLayer m).flatMap nextLayerEntry).get
      ⟨j % ((zoneLayer m).flatMap nextLayerEntry).length, Nat.mod_lt _ hW_pos⟩
    have hmem : wEntry ∈ nextLayerEntry e := periodicParent_mem (zoneLayer m) hL hW_pos j
    have hv'_eq : layerVert (zoneLayer (m + 1)) hW j = wEntry.2 origin := by
      cases m with
      | zero => omega
      | succ n => rfl
    have hdist_step : ∀ (G : H2 ≃ᵢ H2) (a d : ℤ),
        dist (G origin) (stepFrame G a d origin) = 2 * r7 := by
      intro G a d
      rw [stepFrame_origin_eq, G.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
    have h1_bound : ∀ {a : ℤ}, (e.1 = .t1 ∧ a = 4) ∨ a = 5 →
        Real.cosh (2 * r7) ≤ (e.2 (polarOrigin (2 * r7) ((a : ℝ) * α7))).z ∧
        zoneGrowthBase ^ (m + 1) ≤ (e.2 (polarOrigin (2 * r7) ((a : ℝ) * α7))).z := by
      intro a ha
      have hz := z_ge_of_type1_child hAdj hDet ho_closed k ha
      have hzk_c := hInv.z_ge_cosh k
      have hzk_p := hInv.z_ge_pow k
      have hch_gt := cosh_two_r7_gt_one
      have hbase_le := zoneGrowthBase_le_cosh_two_r7
      have hpow_pos : 0 < zoneGrowthBase ^ m := pow_pos (by linarith [zoneGrowthBase_gt_one]) m
      refine ⟨?_, ?_⟩
      · nlinarith
      · rw [pow_succ']
        have h1 : zoneGrowthBase * zoneGrowthBase ^ m ≤
            Real.cosh (2 * r7) * (layerVert (zoneLayer m) hL k).z :=
          mul_le_mul hbase_le hzk_p hpow_pos.le (Real.cosh_pos _).le
        exact le_trans h1 hz
    have h2_bound :
        Real.cosh (2 * r7) ≤ (e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7))).z ∧
        zoneGrowthBase ^ (m + 1) ≤ (e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7))).z := by
      have hz := z_ge_of_type2_child hAdj hDet ho_closed k
      have hd_edge : dist (layerVert (zoneLayer m) hL k) (layerVert (zoneLayer m) hL (k + 1)) = 2 * r7 := by
        have ha := hAdj.2 ⟨k % (zoneLayer m).length, Nat.mod_lt _ hL⟩
        have hnext : layerVert (zoneLayer m) hL (k + 1) = e.2 (polarOrigin (2 * r7) 0) := by
          simpa [layerVert, e, Nat.mod_add_mod] using adjFrame_origin_eq ha
        change dist (e.2 origin) (layerVert (zoneLayer m) hL (k + 1)) = 2 * r7
        rw [hnext, e.2.dist_eq, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
      rw [mid_z_of_dist_two_r7 hd_edge] at hz
      have hchr_pos : 0 < Real.cosh r7 := Real.cosh_pos r7
      have hchh_pos : 0 < Real.cosh h7 := Real.cosh_pos h7
      have hbase_gt := zoneGrowthBase_gt_one
      refine ⟨?_, ?_⟩
      · have h1 : Real.cosh (2 * r7) ≤ (layerVert (zoneLayer m) hL k).z := hInv.z_ge_cosh k
        have h2 : Real.cosh (2 * r7) ≤ (layerVert (zoneLayer m) hL (k + 1)).z := hInv.z_ge_cosh (k + 1)
        have hm' : Real.cosh (2 * r7) / Real.cosh r7 ≤
            ((layerVert (zoneLayer m) hL k).z + (layerVert (zoneLayer m) hL (k + 1)).z) / (2 * Real.cosh r7) := by
          rw [div_le_div_iff₀ hchr_pos (by linarith)]; nlinarith
        have h3 : zoneGrowthBase * Real.cosh (2 * r7) ≤
            Real.cosh h7 * (((layerVert (zoneLayer m) hL k).z +
              (layerVert (zoneLayer m) hL (k + 1)).z) / (2 * Real.cosh r7)) := by
          have heq : zoneGrowthBase * Real.cosh (2 * r7) =
              Real.cosh h7 * (Real.cosh (2 * r7) / Real.cosh r7) := by
            unfold zoneGrowthBase; ring
          rw [heq]; exact mul_le_mul_of_nonneg_left hm' hchh_pos.le
        have h4 : Real.cosh (2 * r7) ≤ zoneGrowthBase * Real.cosh (2 * r7) := by
          nlinarith [Real.cosh_pos (2 * r7)]
        exact le_trans h4 (le_trans h3 hz)
      · have h1 : zoneGrowthBase ^ m ≤ (layerVert (zoneLayer m) hL k).z := hInv.z_ge_pow k
        have h2 : zoneGrowthBase ^ m ≤ (layerVert (zoneLayer m) hL (k + 1)).z := hInv.z_ge_pow (k + 1)
        have hm' : zoneGrowthBase ^ m / Real.cosh r7 ≤
            ((layerVert (zoneLayer m) hL k).z + (layerVert (zoneLayer m) hL (k + 1)).z) / (2 * Real.cosh r7) := by
          rw [div_le_div_iff₀ hchr_pos (by linarith)]; nlinarith
        rw [pow_succ']
        have h3 : zoneGrowthBase * zoneGrowthBase ^ m ≤
            Real.cosh h7 * (((layerVert (zoneLayer m) hL k).z +
              (layerVert (zoneLayer m) hL (k + 1)).z) / (2 * Real.cosh r7)) := by
          have heq : zoneGrowthBase * zoneGrowthBase ^ m =
              Real.cosh h7 * (zoneGrowthBase ^ m / Real.cosh r7) := by
            unfold zoneGrowthBase; ring
          rw [heq]; exact mul_le_mul_of_nonneg_left hm' hchh_pos.le
        exact le_trans h3 hz
    rcases he_eq : e with ⟨t, F⟩
    rw [he_eq] at hmem
    cases t with
    | t1 =>
      simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hEq | hEq | hEq
      · rw [hv'_eq, hEq]
        refine ⟨?_, ?_⟩
        · change dist (e.2 origin) (stepFrame F 4 1 origin) = 2 * r7
          rw [he_eq]; exact hdist_step F 4 1
        · simpa [he_eq, stepFrame_origin_eq] using h1_bound (Or.inl ⟨by rw [he_eq], rfl⟩)
      · rw [hv'_eq, hEq]
        refine ⟨?_, ?_⟩
        · change dist (e.2 origin) (stepFrame F 5 1 origin) = 2 * r7
          rw [he_eq]; exact hdist_step F 5 1
        · simpa [he_eq, stepFrame_origin_eq] using h1_bound (Or.inr rfl)
      · rw [hv'_eq, hEq]
        refine ⟨?_, ?_⟩
        · change dist (e.2 origin) (stepFrame F 6 2 origin) = 2 * r7
          rw [he_eq]; exact hdist_step F 6 2
        · simpa [he_eq, stepFrame_origin_eq] using h2_bound
    | t2 =>
      simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hEq | hEq
      · rw [hv'_eq, hEq]
        refine ⟨?_, ?_⟩
        · change dist (e.2 origin) (stepFrame F 5 1 origin) = 2 * r7
          rw [he_eq]; exact hdist_step F 5 1
        · simpa [he_eq, stepFrame_origin_eq] using h1_bound (Or.inr rfl)
      · rw [hv'_eq, hEq]
        refine ⟨?_, ?_⟩
        · change dist (e.2 origin) (stepFrame F 6 2 origin) = 2 * r7
          rw [he_eq]; exact hdist_step F 6 2
        · simpa [he_eq, stepFrame_origin_eq] using h2_bound
  -- 3. Lift polar angle ψ for zoneLayer (m + 1) and track |ψ j - θ (p j)| < π/2!
  rcases hInv.lifted_angle with ⟨θ, hθ_step, hθ_wind, hθ_rep⟩
  set v' : ℕ → H2 := layerVert (zoneLayer (m + 1)) hW
  set p : ℕ → ℕ := periodicParent (zoneLayer m) hL
  have hR_pos : ∀ j, 0 < kleinNorm (v' j) := fun j =>
    kleinNorm_pos_of_z_gt_one (lt_of_lt_of_le cosh_two_r7_gt_one (hchild_info j).2.1)
  have hR_sq_pos : ∀ j, 0 < (klein (v' j)).1 ^ 2 + (klein (v' j)).2 ^ 2 := by
    intro j; exact Real.sqrt_pos.mp (hR_pos j)
  have hcross_v' : ∀ j, 0 < (klein (v' j)).1 * (klein (v' (j + 1))).2 -
      (klein (v' j)).2 * (klein (v' (j + 1))).1 := by
    intro j
    have h1 : 0 < detH origin (v' j) (v' (j + 1)) := by
      rw [detH_cyclic]; exact ho_next j
    rw [detH_pos_iff_orient2D_pos] at h1
    have ho_k : klein origin = (0, 0) := by unfold klein origin; simp
    rw [ho_k] at h1
    simpa [orient2D] using h1
  have hdot_p : ∀ j, 0 < Real.cos (θ (p j)) * (klein (v' j)).1 +
      Real.sin (θ (p j)) * (klein (v' j)).2 := by
    intro j
    have hd := klein_dot_pos_of_dist_two_r7 (hInv.z_ge_cosh (p j)) (hchild_info j).2.1 (hchild_info j).1
    rw [hθ_rep (p j)] at hd
    have hRp : 0 < kleinNorm (layerVert (zoneLayer m) hL (p j)) :=
      kleinNorm_pos_of_z_gt_one (lt_of_lt_of_le cosh_two_r7_gt_one (hInv.z_ge_cosh (p j)))
    nlinarith
  rcases exists_angle_near_of_dot_pos (hR_pos 0)
    (Real.sq_sqrt (hR_sq_pos 0).le).symm (hdot_p 0) with ⟨ψ₀, hψ0_lo, hψ0_hi, hψ0_x, hψ0_y⟩
  have hlift : ∃ ψ : ℕ → ℝ,
      ψ 0 = ψ₀ ∧
      (∀ j, 0 < ψ (j + 1) - ψ j ∧ ψ (j + 1) - ψ j < Real.pi) ∧
      (∀ j, (klein (v' j)).1 = kleinNorm (v' j) * Real.cos (ψ j) ∧
            (klein (v' j)).2 = kleinNorm (v' j) * Real.sin (ψ j)) := by
    let P : ℕ → ℝ → Prop := fun j a =>
      (klein (v' j)).1 = kleinNorm (v' j) * Real.cos a ∧
      (klein (v' j)).2 = kleinNorm (v' j) * Real.sin a
    let step : ∀ j, { a : ℝ // P j a } → { a : ℝ // P (j + 1) a } := fun j ⟨a, ha⟩ =>
      let hex := exists_angle_step_in_Ioo (hR_sq_pos j) (hR_sq_pos (j + 1)) ha.1 ha.2 (hcross_v' j)
      ⟨a + Classical.choose hex,
        by have hs := Classical.choose_spec hex; exact ⟨hs.2.2.1, hs.2.2.2⟩⟩
    let seq : (j : ℕ) → { a : ℝ // P j a } :=
      Nat.rec ⟨ψ₀, ⟨hψ0_x, hψ0_y⟩⟩ step
    refine ⟨fun j => (seq j).1, rfl, ?_, fun j => (seq j).2⟩
    intro j
    have hs := Classical.choose_spec
      (exists_angle_step_in_Ioo (hR_sq_pos j) (hR_sq_pos (j + 1))
        (seq j).2.1 (seq j).2.2 (hcross_v' j))
    change 0 < ((seq j).1 + Classical.choose _) - (seq j).1 ∧
      ((seq j).1 + Classical.choose _) - (seq j).1 < Real.pi
    constructor <;> linarith [hs.1, hs.2.1]
  rcases hlift with ⟨ψ, hψ0, hψ_step, hψ_rep⟩
  have htrack : ∀ j, -(Real.pi / 2) < ψ j - θ (p j) ∧ ψ j - θ (p j) < Real.pi / 2 := by
    intro j
    induction j with
    | zero => simpa [hψ0] using And.intro hψ0_lo hψ0_hi
    | succ j ih =>
      have hcos_pos : 0 < Real.cos (ψ (j + 1) - θ (p (j + 1))) := by
        have hd := hdot_p (j + 1)
        have hr := hψ_rep (j + 1)
        have h1 : Real.cos (θ (p (j + 1))) * (klein (v' (j + 1))).1 +
            Real.sin (θ (p (j + 1))) * (klein (v' (j + 1))).2 =
            kleinNorm (v' (j + 1)) * Real.cos (ψ (j + 1) - θ (p (j + 1))) := by
          rw [hr.1, hr.2, Real.cos_sub]; ring
        rw [h1] at hd
        nlinarith [hR_pos (j + 1)]
      have h1 := hψ_step j
      have hθp_diff : 0 ≤ θ (p (j + 1)) - θ (p j) ∧ θ (p (j + 1)) - θ (p j) < Real.pi := by
        rcases periodicParent_step (zoneLayer m) hL j with hsame | hinc
        · change p (j + 1) = p j at hsame
          rw [hsame, sub_self]; exact ⟨le_rfl, Real.pi_pos⟩
        · change p (j + 1) = p j + 1 at hinc
          rw [hinc]; exact ⟨(hθ_step (p j)).1.le, (hθ_step (p j)).2⟩
      exact abs_lt_pi_div_two_of_cos_pos hcos_pos
        (by linarith [ih.1, h1.1, hθp_diff.2]) (by linarith [ih.2, h1.2, hθp_diff.1])
  -- Therefore ψ (j + N') = ψ j + 2π for ALL j!
  set N' := (zoneLayer (m + 1)).length
  have hψ_wind : ∀ j, ψ (j + N') = ψ j + 2 * Real.pi := by
    intro j
    have hN'_eq : N' = ((zoneLayer m).flatMap nextLayerEntry).length := congrArg List.length hsucc
    have hp_add : p (j + N') = p j + (zoneLayer m).length := by
      change periodicParent (zoneLayer m) hL (j + N') = periodicParent (zoneLayer m) hL j + (zoneLayer m).length
      rw [hN'_eq]; exact periodicParent_add_len (zoneLayer m) hL j
    have htr1 := htrack j
    have htr2 := htrack (j + N')
    rw [hp_add, hθ_wind (p j)] at htr2
    have hv'_per : v' (j + N') = v' j := layerVert_add_len (zoneLayer (m + 1)) hW j
    have hrep1 := hψ_rep j
    have hrep2 := hψ_rep (j + N')
    rw [hv'_per] at hrep2
    have hcos_eq : Real.cos (ψ (j + N') - ψ j) = 1 := by
      have hc : Real.cos (ψ (j + N')) = Real.cos (ψ j) :=
        mul_left_cancel₀ (hR_pos j).ne' (hrep2.1.symm.trans hrep1.1)
      have hs : Real.sin (ψ (j + N')) = Real.sin (ψ j) :=
        mul_left_cancel₀ (hR_pos j).ne' (hrep2.2.symm.trans hrep1.2)
      rw [Real.cos_sub, hc, hs]
      have := Real.cos_sq_add_sin_sq (ψ j); nlinarith
    have hlo : Real.pi < ψ (j + N') - ψ j := by linarith [htr1.2, htr2.1]
    have hhi : ψ (j + N') - ψ j < 3 * Real.pi := by linarith [htr1.1, htr2.2]
    have hcos_shift : Real.cos (ψ (j + N') - ψ j - 2 * Real.pi) = 1 := by
      rw [Real.cos_sub_two_pi]; exact hcos_eq
    by_contra hne
    have hne0 : ψ (j + N') - ψ j - 2 * Real.pi ≠ 0 := fun h => hne (by linarith)
    rcases lt_or_gt_of_ne hne0 with hneg | hpos
    · have hlt : Real.cos (ψ (j + N') - ψ j - 2 * Real.pi) < Real.cos 0 := by
        rw [← Real.cos_neg (ψ (j + N') - ψ j - 2 * Real.pi)]
        exact Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
          ⟨by linarith, by linarith⟩ (by linarith)
      simp at hlt; linarith
    · have hlt : Real.cos (ψ (j + N') - ψ j - 2 * Real.pi) < Real.cos 0 :=
        Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
          ⟨by linarith, by linarith⟩ hpos
      simp at hlt; linarith
  -- 4. Global convexity by starShaped_locallyConvex_globallyConvex!
  have hN'_ge3 : 3 ≤ N' := by
    have hlen_ge : ∀ M : List (ZoneType × (H2 ≃ᵢ H2)), 2 * M.length ≤ (M.flatMap nextLayerEntry).length := by
      intro M
      induction M with
      | nil => simp
      | cons a tl ih =>
        rw [List.flatMap_cons, List.length_append, List.length_cons]
        have := nextLayerEntry_length_ge_two a; omega
    have h1 := hlen_ge (zoneLayer m)
    have hN'_eq : N' = ((zoneLayer m).flatMap nextLayerEntry).length := congrArg List.length hsucc
    have hL_ge2 : 2 ≤ (zoneLayer m).length := by
      rw [zoneLayer_length]
      have h7 : ∀ n, 1 ≤ n → 7 ≤ (zoneWord n).length := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => decide
        | succ r hr ih =>
          have hstep : zoneWord (r + 1) = (zoneWord r).flatMap sigmaStep := by
            cases r with | zero => omega | succ k => rfl
          rw [hstep]
          have hge : ∀ w : List ZoneType, w.length ≤ (w.flatMap sigmaStep).length := by
            intro w; induction w with
            | nil => simp
            | cons x xs ihw =>
              rw [List.flatMap_cons, List.length_append, List.length_cons]
              cases x <;> simp only [sigmaStep, List.length_cons, List.length_nil] <;> omega
          exact le_trans ih (hge _)
      have := h7 m hm; omega
    omega
  have hloc : ∀ j, 0 < orient2D (klein (v' j)) (klein (v' (j + 1))) (klein (v' (j + 2))) := by
    intro j
    rw [← detH_pos_iff_orient2D_pos]
    exact cyclicAdj_local_convex (zoneLayer_cyclicAdj (m + 1) (by omega))
      (fun e he => (zoneLayer_mem_Delta237_and_detH (m + 1) e he).2) j
  have hglob := starShaped_locallyConvex_globallyConvex hN'_ge3
    (fun j => klein (v' j))
    (fun j => congrArg klein (layerVert_add_len (zoneLayer (m + 1)) hW j))
    (fun j => kleinNorm (v' j))
    ψ
    hR_pos
    (fun j => by ext; exact (hψ_rep j).1; exact (hψ_rep j).2)
    hψ_step
    hψ_wind
    hloc
  refine ⟨ho_next, ?_, fun j => (hchild_info j).2.1, fun j => (hchild_info j).2.2, ?_⟩
  · intro k j hkj hjN
    rw [detH_pos_iff_orient2D_pos]
    exact hglob k j hkj hjN
  · exact ⟨ψ, hψ_step, hψ_wind, fun j => by ext; exact (hψ_rep j).1; exact (hψ_rep j).2⟩

/-- **Global Convexity & Growth Theorem**: `ZoneConvexInv m hm` holds for EVERY `m ≥ 1`! -/
theorem zoneConvexInv (m : ℕ) (hm : 1 ≤ m) : ZoneConvexInv m hm := by
  induction m, hm using Nat.le_induction with
  | base => exact zoneConvexInv_one
  | succ k hk ih => exact zoneConvexInv_step hk ih

/-! ### Consequences: `Nodup`, nestedness `ClosedPoly m ⊆ OpenPoly (m+1)`, and disjointness of zones -/

theorem zoneVerts_nodup (m : ℕ) : (zoneVerts m).Nodup := by
  cases m with
  | zero => simp [zoneVerts, zoneLayer]
  | succ n =>
    have hm : 1 ≤ n + 1 := by omega
    have hInv := zoneConvexInv (n + 1) hm
    rcases hInv.lifted_angle with ⟨θ, hθ_step, hθ_wind, hθ_rep⟩
    set hL := zoneLayer_length_pos (n + 1) hm
    rw [List.nodup_iff_injective_get]
    intro i j hij
    have hi_lt : i.1 < (zoneLayer (n + 1)).length := by simpa [zoneVerts_length] using i.2
    have hj_lt : j.1 < (zoneLayer (n + 1)).length := by simpa [zoneVerts_length] using j.2
    have hvert : layerVert (zoneLayer (n + 1)) hL i.1 = layerVert (zoneLayer (n + 1)) hL j.1 := by
      have hi : (zoneVerts (n + 1)).get i = layerVert (zoneLayer (n + 1)) hL i.1 := by
        rw [List.get_eq_getElem]
        simp only [zoneVerts, List.getElem_map, layerVert, List.get_eq_getElem, Nat.mod_eq_of_lt hi_lt]
      have hj : (zoneVerts (n + 1)).get j = layerVert (zoneLayer (n + 1)) hL j.1 := by
        rw [List.get_eq_getElem]
        simp only [zoneVerts, List.getElem_map, layerVert, List.get_eq_getElem, Nat.mod_eq_of_lt hj_lt]
      rw [← hi, ← hj, hij]
    have hθ_mono : ∀ a b, a < b → θ a < θ b := by
      intro a b hab
      induction hab with
      | refl => linarith [(hθ_step a).1]
      | @step r _ ih => linarith [ih, (hθ_step r).1]
    by_contra hne
    have hlt_or : i.1 < j.1 ∨ j.1 < i.1 := lt_or_gt_of_ne (fun h => hne (Fin.ext h))
    have hdiff_imp : ∀ a b : ℕ, a < b → b < (zoneLayer (n + 1)).length →
        layerVert (zoneLayer (n + 1)) hL a = layerVert (zoneLayer (n + 1)) hL b → False := by
      intro a b hab hbL heq
      have hRa : 0 < kleinNorm (layerVert (zoneLayer (n + 1)) hL a) :=
        kleinNorm_pos_of_z_gt_one (lt_of_lt_of_le cosh_two_r7_gt_one (hInv.z_ge_cosh a))
      have hk := congrArg klein heq
      rw [hθ_rep a, hθ_rep b, heq] at hk
      have hcos : Real.cos (θ a) = Real.cos (θ b) := by
        have h1 := congrArg Prod.fst hk
        rw [← heq] at h1
        exact mul_left_cancel₀ hRa.ne' h1
      have hsin : Real.sin (θ a) = Real.sin (θ b) := by
        have h1 := congrArg Prod.snd hk
        rw [← heq] at h1
        exact mul_left_cancel₀ hRa.ne' h1
      have hcos_sub : Real.cos (θ b - θ a) = 1 := by
        rw [Real.cos_sub, ← hcos, ← hsin]
        have := Real.cos_sq_add_sin_sq (θ a); nlinarith
      have hlo : 0 < θ b - θ a := by linarith [hθ_mono a b hab]
      have hhi : θ b - θ a < 2 * Real.pi := by
        have h1 : θ b < θ (a + (zoneLayer (n + 1)).length) := hθ_mono b (a + (zoneLayer (n + 1)).length) (by omega)
        linarith [hθ_wind a]
      by_cases hpi : θ b - θ a ≤ Real.pi
      · have hlt := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) ⟨hlo.le, hpi⟩ hlo
        simp at hlt; linarith
      · push Not at hpi
        have h1 : Real.cos (2 * Real.pi - (θ b - θ a)) = 1 := by
          rw [Real.cos_two_pi_sub]; exact hcos_sub
        have hlt := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
          ⟨by linarith, by linarith⟩ (by linarith : 0 < 2 * Real.pi - (θ b - θ a))
        simp at hlt; linarith
    rcases hlt_or with h | h
    · exact hdiff_imp i.1 j.1 h hj_lt hvert
    · exact hdiff_imp j.1 i.1 h hi_lt hvert.symm

lemma closedPoly_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ClosedPoly m hm ⊆ ClosedPoly n (by omega) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ k hk ih =>
    intro y hy
    have h1 := closedPoly_subset_openPoly_succ k (by omega) (ih hy)
    exact fun j => (h1 j).le

lemma zoneVert_not_mem_closedPoly_prev {m : ℕ} (hm : 1 ≤ m) (v : H2)
    (hv : v ∈ zoneVerts (m + 1)) : v ∉ ClosedPoly m hm := by
  have hsucc : zoneLayer (m + 1) = (zoneLayer m).flatMap nextLayerEntry := by
    cases m with | zero => omega | succ n => rfl
  simp only [zoneVerts, hsucc, List.mem_map, List.mem_flatMap] at hv
  rcases hv with ⟨e', ⟨e, heL, he'c⟩, rfl⟩
  rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
  set hL := zoneLayer_length_pos m hm
  set hAdj := zoneLayer_cyclicAdj m hm
  set hDet := fun x hx => (zoneLayer_mem_Delta237_and_detH m x hx).2
  have hInv := zoneConvexInv m hm
  have huk_mem : layerVert (zoneLayer m) hL k.1 ∈ ClosedPoly m hm := layerVert_mem_closedPoly hInv k.1
  have hMk_mem : mid (layerVert (zoneLayer m) hL k.1) (layerVert (zoneLayer m) hL (k.1 + 1)) ∈ ClosedPoly m hm :=
    mid_mem_closedPolyOf huk_mem (layerVert_mem_closedPoly hInv (k.1 + 1))
  have hfoot_out : ∀ {x p : H2}, IsFoot (ClosedPoly m hm) x p → x ≠ p → x ∉ ClosedPoly m hm := by
    intro x p hfoot hne hxmem
    have hlt := hfoot.2 x hxmem hne
    rw [lorentz_self] at hlt
    linarith [one_le_lorentz x p]
  have hget_mod : (zoneLayer m).get ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩ = (zoneLayer m).get k := by
    congr 1; ext; exact Nat.mod_eq_of_lt k.2
  rcases hk_eq : (zoneLayer m).get k with ⟨t, F⟩
  rw [hk_eq] at he'c
  have hu_eq : layerVert (zoneLayer m) hL k.1 = F origin := by
    unfold layerVert; rw [hget_mod, hk_eq]
  cases t with
  | t1 =>
    simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
    rcases he'c with rfl | rfl | rfl
    · rw [stepFrame_origin_eq]
      have hf := isFoot_type1_child hAdj hDet k.1 huk_mem (j := 4) (Or.inl ⟨by rw [hget_mod, hk_eq], rfl⟩)
      simp only [hget_mod, hk_eq] at hf
      apply hfoot_out hf
      intro heq
      have hd : dist (F origin) (F (polarOrigin (2 * r7) ((4 : ℤ) * α7))) = 2 * r7 := by
        rw [F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
      rw [hu_eq] at heq; rw [heq, dist_self] at hd; linarith [r7_pos]
    · rw [stepFrame_origin_eq]
      have hf := isFoot_type1_child hAdj hDet k.1 huk_mem (j := 5) (Or.inr rfl)
      simp only [hget_mod, hk_eq] at hf
      apply hfoot_out hf
      intro heq
      have hd : dist (F origin) (F (polarOrigin (2 * r7) ((5 : ℤ) * α7))) = 2 * r7 := by
        rw [F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
      rw [hu_eq] at heq; rw [heq, dist_self] at hd; linarith [r7_pos]
    · rw [stepFrame_origin_eq]
      have hf := isFoot_type2_child hAdj hDet k.1 hMk_mem
      simp only [hget_mod, hk_eq] at hf
      apply hfoot_out hf
      intro heq
      have hd : dist (F origin) (F (polarOrigin (2 * r7) ((6 : ℤ) * α7))) = 2 * r7 := by
        rw [F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
      have hmid_d : dist (layerVert (zoneLayer m) hL k.1)
          (mid (layerVert (zoneLayer m) hL k.1) (layerVert (zoneLayer m) hL (k.1 + 1))) = r7 := by
        rw [dist_mid_left]
        have ha := hAdj.2 ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
        have hnext : layerVert (zoneLayer m) hL (k.1 + 1) = F (polarOrigin (2 * r7) 0) := by
          have h1 := adjFrame_origin_eq ha
          rw [hget_mod, hk_eq] at h1
          simpa [layerVert, Nat.mod_add_mod] using h1
        rw [hu_eq, hnext, F.dist_eq, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]; ring
      rw [heq, ← hu_eq, hmid_d] at hd; linarith [r7_pos]
  | t2 =>
    simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
    rcases he'c with rfl | rfl
    · rw [stepFrame_origin_eq]
      have hf := isFoot_type1_child hAdj hDet k.1 huk_mem (j := 5) (Or.inr rfl)
      simp only [hget_mod, hk_eq] at hf
      apply hfoot_out hf
      intro heq
      have hd : dist (F origin) (F (polarOrigin (2 * r7) ((5 : ℤ) * α7))) = 2 * r7 := by
        rw [F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
      rw [hu_eq] at heq; rw [heq, dist_self] at hd; linarith [r7_pos]
    · rw [stepFrame_origin_eq]
      have hf := isFoot_type2_child hAdj hDet k.1 hMk_mem
      simp only [hget_mod, hk_eq] at hf
      apply hfoot_out hf
      intro heq
      have hd : dist (F origin) (F (polarOrigin (2 * r7) ((6 : ℤ) * α7))) = 2 * r7 := by
        rw [F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
      have hmid_d : dist (layerVert (zoneLayer m) hL k.1)
          (mid (layerVert (zoneLayer m) hL k.1) (layerVert (zoneLayer m) hL (k.1 + 1))) = r7 := by
        rw [dist_mid_left]
        have ha := hAdj.2 ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
        have hnext : layerVert (zoneLayer m) hL (k.1 + 1) = F (polarOrigin (2 * r7) 0) := by
          have h1 := adjFrame_origin_eq ha
          rw [hget_mod, hk_eq] at h1
          simpa [layerVert, Nat.mod_add_mod] using h1
        rw [hu_eq, hnext, F.dist_eq, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]; ring
      rw [heq, ← hu_eq, hmid_d] at hd; linarith [r7_pos]

lemma zoneVert_mem_closedPoly {m : ℕ} (hm : 1 ≤ m) {v : H2} (hv : v ∈ zoneVerts m) :
    v ∈ ClosedPoly m hm := by
  simp only [zoneVerts, List.mem_map] at hv
  rcases hv with ⟨e, heL, rfl⟩
  rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
  have h1 := layerVert_mem_closedPoly (zoneConvexInv m hm) k.1
  simpa [layerVert, Nat.mod_eq_of_lt k.2] using h1

lemma zoneVerts_disjoint {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m < n)
    {v : H2} (hvm : v ∈ zoneVerts m) (hvn : v ∈ zoneVerts n) : False := by
  have hn1 : 1 ≤ n - 1 := by omega
  have heq : n = (n - 1) + 1 := by omega
  have hvn' : v ∈ zoneVerts ((n - 1) + 1) := by rwa [← heq]
  have hout := zoneVert_not_mem_closedPoly_prev hn1 v hvn'
  have hin : v ∈ ClosedPoly (n - 1) hn1 :=
    closedPoly_mono hm (by omega) (zoneVert_mem_closedPoly hm hvm)
  exact hout hin

lemma origin_not_mem_zoneVerts (m : ℕ) : origin ∉ zoneVerts m := by
  cases m with
  | zero => simp [zoneVerts, zoneLayer]
  | succ n =>
    intro ho
    simp only [zoneVerts, List.mem_map] at ho
    rcases ho with ⟨e, heL, heq⟩
    rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
    have hz := (zoneConvexInv (n + 1) (by omega)).z_ge_cosh k.1
    have hv : layerVert (zoneLayer (n + 1)) (zoneLayer_length_pos (n + 1) (by omega)) k.1 = origin := by
      simpa [layerVert, Nat.mod_eq_of_lt k.2] using heq
    rw [hv] at hz
    change Real.cosh (2 * r7) ≤ 1 at hz
    linarith [cosh_two_r7_gt_one]

end FejesTothP7.Proofs
