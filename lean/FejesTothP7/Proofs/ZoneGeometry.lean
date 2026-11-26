/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.ConvexPoly
import FejesTothP7.Proofs.ZoneLayers

/-!
# Global Convexity, Unique Feet, and Disjointness of Concentric Zone Polygons `P_m`

Proves by induction on `m ≥ 1` that the framed zone layers `zoneLayer m` bound globally convex
hyperbolic polygons `ClosedPoly m` containing `origin` in their interior, with:
- `ClosedPoly m ⊆ OpenPoly (m + 1)`
- Every type-1 vertex in `Z_{m+1}` has unique foot `u_k ∈ Z_m` on `ClosedPoly m`
- Every type-2 vertex in `Z_{m+1}` has unique foot `mid u_k u_{k+1}` on `ClosedPoly m`
- Every vertex `v ∈ Z_m` satisfies `v.z ≥ cosh (2 * r7)` and `v ∉ ClosedPoly (m - 1)`
- `zoneVerts m` has no duplicate vertices (`Nodup`)
-/

noncomputable section

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Basic definitions for zone polygons -/

/-- The cyclic list of vertices of zone `m`. -/
def zoneVerts (m : ℕ) : List H2 :=
  (zoneLayer m).map (fun e => e.2 origin)

lemma zoneVerts_length (m : ℕ) : (zoneVerts m).length = (zoneLayer m).length :=
  List.length_map _

/-- Periodic vertex accessor for a nonempty layer `L`. -/
def layerVert (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) (k : ℕ) : H2 :=
  (L.get ⟨k % L.length, Nat.mod_lt k hL⟩).2 origin

lemma layerVert_add_len (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) (k : ℕ) :
    layerVert L hL (k + L.length) = layerVert L hL k := by
  simp [layerVert]

/-- Closed convex polygon bounded by the cyclic edges of a nonempty layer `L`. -/
def ClosedPolyOf (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) : Set H2 :=
  {y : H2 | ∀ k : ℕ, 0 ≤ detH (layerVert L hL k) (layerVert L hL (k + 1)) y}

/-- Open interior of the polygon bounded by `L`. -/
def OpenPolyOf (L : List (ZoneType × (H2 ≃ᵢ H2))) (hL : 0 < L.length) : Set H2 :=
  {y : H2 | ∀ k : ℕ, 0 < detH (layerVert L hL k) (layerVert L hL (k + 1)) y}

lemma zoneLayer_length_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (zoneLayer m).length := by
  rw [zoneLayer_length]; exact zoneWord_length_pos m hm

/-- Closed polygon `P_m` (`m ≥ 1`). -/
def ClosedPoly (m : ℕ) (hm : 1 ≤ m) : Set H2 :=
  ClosedPolyOf (zoneLayer m) (zoneLayer_length_pos m hm)

/-- Open polygon `int(P_m)` (`m ≥ 1`). -/
def OpenPoly (m : ℕ) (hm : 1 ≤ m) : Set H2 :=
  OpenPolyOf (zoneLayer m) (zoneLayer_length_pos m hm)

/-! ### Consequence of `AdjFrame` on vertex coordinates -/

lemma adjFrame_origin_eq {e₁ e₂ : ZoneType × (H2 ≃ᵢ H2)} (h : AdjFrame e₁ e₂) :
    e₂.2 origin = e₁.2 (polarOrigin (2 * r7) 0) := by
  unfold AdjFrame at h
  rw [h]
  simp only [IsometryEquiv.trans_apply]
  have h0 : (rot7 ^ (-((e₂.1.innerCount + 1 : ℕ) : ℤ))) origin = origin := by
    rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
    simp [polarOrigin_zero]
  rw [h0, halfTurn_origin]

lemma adjFrame_prev_eq {e₁ e₂ : ZoneType × (H2 ≃ᵢ H2)} (h : AdjFrame e₁ e₂) :
    e₂.2 (polarOrigin (2 * r7) (((e₂.1.innerCount + 1 : ℕ) : ℝ) * α7)) = e₁.2 origin := by
  unfold AdjFrame at h
  rw [h]
  simp only [IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin, Int.cast_neg, Int.cast_natCast]
  have h0 : ((e₂.1.innerCount + 1 : ℕ) : ℝ) * α7 + -((e₂.1.innerCount + 1 : ℕ) : ℝ) * α7 = 0 := by ring
  rw [h0, halfTurn_polarOrigin_zero]

lemma detH_cyclic (a b c : H2) : detH a b c = detH b c a := by
  unfold detH; ring

lemma detH_swap_12 (a b c : H2) : detH a b c = -detH b a c := by
  unfold detH; ring

/-- Local convexity at every vertex of a `CyclicAdj` layer whose frames preserve `detH`. -/
lemma cyclicAdj_local_convex {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c) :
    ∀ k : ℕ, 0 < detH (layerVert L hAdj.1 k) (layerVert L hAdj.1 (k + 1)) (layerVert L hAdj.1 (k + 2)) := by
  intro k
  let e0 := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
  let e1 := L.get ⟨(k + 1) % L.length, Nat.mod_lt _ hAdj.1⟩
  let e2 := L.get ⟨(k + 2) % L.length, Nat.mod_lt _ hAdj.1⟩
  have h01 : AdjFrame e0 e1 := by
    have := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    simpa [e0, e1, Nat.mod_add_mod] using this
  have h12 : AdjFrame e1 e2 := by
    have := hAdj.2 ⟨(k + 1) % L.length, Nat.mod_lt _ hAdj.1⟩
    have hmod : ((k + 1) % L.length + 1) % L.length = (k + 2) % L.length := by
      rw [Nat.mod_add_mod]
    simpa [e1, e2, hmod] using this
  change 0 < detH (e0.2 origin) (e1.2 origin) (e2.2 origin)
  rw [← adjFrame_prev_eq h01, adjFrame_origin_eq h12, hDet e1 (List.get_mem _ _)]
  -- detH (polarOrigin (2*r7) ((i+1)*α7)) origin (polarOrigin (2*r7) 0) = sinh(2*r7)^2 * sin((i+1)*α7) > 0!
  have hcalc : ∀ θ : ℝ, detH (polarOrigin (2 * r7) θ) origin (polarOrigin (2 * r7) 0) =
      Real.sinh (2 * r7) ^ 2 * Real.sin θ := by
    intro θ
    unfold detH polarOrigin origin
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]
    ring
  rw [hcalc]
  have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hsin : 0 < Real.sin (((e1.1.innerCount + 1 : ℕ) : ℝ) * α7) := by
    cases h : e1.1 <;>
    · simp only [ZoneType.innerCount]
      apply Real.sin_pos_of_pos_of_lt_pi <;>
      · unfold α7 alphaP; push_cast; linarith [Real.pi_pos]
  positivity

/-! ### Local foot lemmas (type-1 normal cone and type-2 edge midpoint) -/

/-- Exact altitude identity: `cosh h7 = cosh (2 * r7) / cosh r7`. -/
lemma cosh_h7_eq : Real.cosh h7 = Real.cosh (2 * r7) / Real.cosh r7 := by
  unfold h7 hP
  apply Real.cosh_arcosh
  rw [le_div_iff₀ (Real.cosh_pos _), one_mul]
  change Real.cosh r7 ≤ Real.cosh (2 * r7)
  rw [cosh_two_r7_eq]
  have hchr : 1 < Real.cosh r7 := by
    rw [cosh_r7]; exact one_lt_inv_two_sin_pi_div_seven
  nlinarith

lemma h7_pos : 0 < h7 := by
  unfold h7 hP
  apply Real.arcosh_pos
  rw [one_lt_div (Real.cosh_pos _)]
  change Real.cosh r7 < Real.cosh (2 * r7)
  rw [cosh_two_r7_eq]
  have hchr : 1 < Real.cosh r7 := by
    rw [cosh_r7]; exact one_lt_inv_two_sin_pi_div_seven
  nlinarith

/-- In the midpoint frame `boostX r7`, `polarOrigin h7 (-π/2)` equals `polarOrigin (2*r7) (-α7)`. -/
lemma boostX_r7_altitude :
    boostX r7 (polarOrigin h7 (-(Real.pi / 2))) = polarOrigin (2 * r7) (-α7) := by
  have hch_h : Real.cosh h7 = Real.cosh (2 * r7) / Real.cosh r7 := cosh_h7_eq
  have hch_r_pos : 0 < Real.cosh r7 := Real.cosh_pos r7
  have hsh_2r : Real.sinh (2 * r7) = 2 * Real.sinh r7 * Real.cosh r7 := Real.sinh_two_mul r7
  have hch_2r : Real.cosh (2 * r7) = 2 * Real.cosh r7 ^ 2 - 1 := cosh_two_r7_eq
  have hcos_a : Real.cos α7 = Real.cosh (2 * r7) / (2 * Real.cosh r7 ^ 2) := by
    rw [cos_alpha7_eq_cosh_div, hch_2r]
    congr 1; ring
  have hx : Real.cosh h7 * Real.sinh r7 = Real.sinh (2 * r7) * Real.cos α7 := by
    rw [hch_h, hsh_2r, hcos_a]
    field_simp [hch_r_pos.ne']
  have hz : Real.cosh h7 * Real.cosh r7 = Real.cosh (2 * r7) := by
    rw [hch_h, div_mul_cancel₀ _ hch_r_pos.ne']
  have hy_sq : Real.sinh h7 ^ 2 = (Real.sinh (2 * r7) * Real.sin α7) ^ 2 := by
    have h1 := Real.cosh_sq_sub_sinh_sq h7
    have h2 := Real.cosh_sq_sub_sinh_sq (2 * r7)
    have h3 := Real.cos_sq_add_sin_sq α7
    have h4 := Real.cosh_sq_sub_sinh_sq r7
    have hsq1 : (Real.cosh h7 * Real.sinh r7) ^ 2 + Real.sinh h7 ^ 2 =
        Real.cosh (2 * r7) ^ 2 - 1 := by
      have : (Real.cosh h7 * Real.cosh r7) ^ 2 = Real.cosh (2 * r7) ^ 2 := by rw [hz]
      nlinarith
    rw [hx] at hsq1
    nlinarith
  have hy_pos1 : 0 < Real.sinh h7 := Real.sinh_pos_iff.mpr h7_pos
  have hy_pos2 : 0 < Real.sinh (2 * r7) * Real.sin α7 := by
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hsin : 0 < Real.sin α7 := Real.sin_pos_of_pos_of_lt_pi
      (by unfold α7 alphaP; positivity) (by unfold α7 alphaP; linarith [Real.pi_pos])
    positivity
  have hy : Real.sinh h7 = Real.sinh (2 * r7) * Real.sin α7 := by nlinarith
  ext
  · simp only [boostX_x, polarOrigin, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg,
      Real.sin_pi_div_two, mul_zero, zero_mul, zero_add]
    exact hx
  · simp only [boostX_y, polarOrigin, Real.sin_neg, Real.sin_pi_div_two, mul_neg, mul_one]
    linarith
  · simp only [boostX_z, polarOrigin, Real.cos_neg, Real.cos_pi_div_two, mul_zero, zero_mul, zero_add]
    exact hz

/-- In frame `F`, `mid (F origin) (F (polarOrigin (2*r7) 0)) = F (polarOrigin r7 0)`. -/
lemma mid_frame_edge (F : H2 ≃ᵢ H2) :
    mid (F origin) (F (polarOrigin (2 * r7) 0)) = F (polarOrigin r7 0) := by
  rw [← isometry_mid]
  congr 1
  symm
  apply eq_mid_of_dist
  · rw [dist_origin_polarOrigin r7 0 r7_pos.le, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
    ring
  · rw [dist_eq_arcosh, lorentz_polarOrigin, sub_self, Real.cos_zero, mul_one]
    have hsub : Real.cosh r7 * Real.cosh (2 * r7) - Real.sinh r7 * Real.sinh (2 * r7) = Real.cosh r7 := by
      have h := Real.cosh_sub (2 * r7) r7
      have h2 : 2 * r7 - r7 = r7 := by ring
      rw [h2] at h; linarith
    rw [hsub, Real.arcosh_cosh r7_pos.le, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
    ring

/-- **Type-1 vertex normal-cone foot lemma**:
    At vertex `k` of `L` with frame `F = (L[k]).2`, every type-1 child `v' = F (polarOrigin (2*r7) (j*α7))`
    (`j = 4` if `t = .t1`, or `j = 5`) has `u_k = F origin` as its STRICT UNIQUE FOOT on `ClosedPolyOf L`! -/
lemma isFoot_type1_child {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c)
    (k : ℕ) (huk_mem : layerVert L hAdj.1 k ∈ ClosedPolyOf L hAdj.1)
    {j : ℤ} (hj : ((L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩).1 = .t1 ∧ j = 4) ∨ j = 5) :
    let e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    IsFoot (ClosedPolyOf L hAdj.1) (e.2 (polarOrigin (2 * r7) ((j : ℝ) * α7))) (layerVert L hAdj.1 k) := by
  intro e
  set u := layerVert L hAdj.1 k
  set uNext := layerVert L hAdj.1 (k + 1)
  set uPrev := layerVert L hAdj.1 (k + L.length - 1)
  set v' := e.2 (polarOrigin (2 * r7) ((j : ℝ) * α7))
  have hv_ne : v' ≠ u := by
    intro heq
    have hd : dist u v' = 2 * r7 := by
      change dist (e.2 origin) (e.2 (polarOrigin (2 * r7) ((j : ℝ) * α7))) = 2 * r7
      rw [e.2.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
    rw [heq, dist_self] at hd
    linarith [r7_pos]
  apply isFoot_of_normalFunc_nonneg huk_mem hv_ne
  intro y hy
  -- By CyclicAdj, uNext = e.2 (polarOrigin (2*r7) 0) and uPrev = e.2 (polarOrigin (2*r7) ((i+1)*α7))
  have he_next : uNext = e.2 (polarOrigin (2 * r7) 0) := by
    have h := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    have := adjFrame_origin_eq h
    simpa [uNext, e, layerVert, Nat.mod_add_mod] using this
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
  -- y ∈ ClosedPolyOf L gives 0 ≤ detH u uNext y and 0 ≤ detH uPrev u y (= detH u y uPrev)!
  have hy_next : 0 ≤ detH u uNext y := hy k
  have hy_prev : 0 ≤ detH u y uPrev := by
    have h1 : 0 ≤ detH (layerVert L hAdj.1 (k + L.length - 1))
        (layerVert L hAdj.1 (k + L.length - 1 + 1)) y := hy (k + L.length - 1)
    have h2 : layerVert L hAdj.1 (k + L.length - 1 + 1) = u := by
      have hpos := hAdj.1
      have heq : k + L.length - 1 + 1 = k + L.length := by omega
      rw [heq, layerVert_add_len]
    rw [h2] at h1
    rwa [detH_cyclic] at h1
  -- Pull back to origin frame via e.2:
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
    intro θ₁ θ₂
    unfold normalFunc
    rw [lorentz_polarOrigin, lorentz_symm _ origin, lorentz_origin_polarOrigin, lorentz_origin_polarOrigin]
    ring
  have hcos_neg_of_Ioo : ∀ φ : ℝ, Real.pi / 2 < φ → φ < 3 * Real.pi / 2 → Real.cos φ < 0 := by
    intro φ hlo hhi
    by_cases hpi : φ ≤ Real.pi
    · have h1 := Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], hpi⟩ hlo
      simpa using h1
    · push Not at hpi
      have h1 : Real.cos (2 * Real.pi - φ) = Real.cos φ := by
        rw [Real.cos_two_pi_sub]
      rw [← h1]
      have h2 := Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith : Real.pi / 2 < 2 * Real.pi - φ)
      simpa using h2
  have hxa : 0 ≤ normalFunc u v' uNext := by
    rw [show u = e.2 origin from rfl, he_next, normalFunc_isometry, hnorm_calc, sub_zero]
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hcos : Real.cos ((j : ℝ) * α7) < 0 := by
      rcases hj with ⟨_, rfl⟩ | rfl
      · apply hcos_neg_of_Ioo <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
      · apply hcos_neg_of_Ioo <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
    nlinarith [sq_pos_of_pos hsh]
  have hxb : 0 ≤ normalFunc u v' uPrev := by
    rw [show u = e.2 origin from rfl, he_prev, normalFunc_isometry, hnorm_calc]
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    have hcos : Real.cos ((j : ℝ) * α7 - ((e.1.innerCount + 1 : ℕ) : ℝ) * α7) < 0 := by
      rcases hj with ⟨ht1, rfl⟩ | rfl
      · rw [ht1]; simp only [ZoneType.innerCount]
        apply hcos_neg_of_Ioo <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
      · cases e.1 <;>
        · simp only [ZoneType.innerCount]
          apply hcos_neg_of_Ioo <;> (unfold α7 alphaP; push_cast; linarith [Real.pi_pos])
    nlinarith [sq_pos_of_pos hsh]
  exact normalFunc_wedge_nonneg hab hy_next hy_prev hxa hxb

/-- **Type-2 vertex edge-midpoint foot lemma**:
    At edge `k` of `L` with frame `F = (L[k]).2`, the type-2 child `w = F (polarOrigin (2*r7) (6*α7))`
    has `M_k = mid u_k u_{k+1}` as its STRICT UNIQUE FOOT on `ClosedPolyOf L`! -/
lemma isFoot_type2_child {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c)
    (k : ℕ) (hMk_mem : mid (layerVert L hAdj.1 k) (layerVert L hAdj.1 (k + 1)) ∈ ClosedPolyOf L hAdj.1) :
    let e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    IsFoot (ClosedPolyOf L hAdj.1) (e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7)))
      (mid (layerVert L hAdj.1 k) (layerVert L hAdj.1 (k + 1))) := by
  intro e
  set u := layerVert L hAdj.1 k
  set uNext := layerVert L hAdj.1 (k + 1)
  set M := mid u uNext
  set w := e.2 (polarOrigin (2 * r7) ((6 : ℤ) * α7))
  have he_next : uNext = e.2 (polarOrigin (2 * r7) 0) := by
    have h := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
    simpa [uNext, e, layerVert, Nat.mod_add_mod] using adjFrame_origin_eq h
  -- Rewrite w = e.2 (polarOrigin (2*r7) (-α7)) = (boostX r7 .trans e.2) (polarOrigin h7 (-π/2))
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
  have hw_ne : w ≠ M := by
    intro heq
    have hd : dist M w = h7 := by
      rw [← hG_o, ← hG_w, G.dist_eq, dist_origin_polarOrigin h7 _ h7_pos.le]
    rw [heq, dist_self] at hd
    linarith [h7_pos]
  apply isFoot_of_normalFunc_nonneg hMk_mem hw_ne
  intro y hy
  have hyk : 0 ≤ detH u uNext y := hy k
  have hG_det : ∀ a b c, detH (G a) (G b) (G c) = detH a b c := by
    intro a b c
    simp only [G, IsometryEquiv.trans_apply, hDet e (List.get_mem _ _), detH_boostX]
  set y0 := G.symm y
  have hy_eq : y = G y0 := by simp [y0]
  rw [hy_eq, ← hG_o, ← hG_w, normalFunc_isometry]
  apply normalFunc_edge_origin_nonneg r7_pos h7_pos y0
  rw [← hG_det, hG_u, hG_uNext, ← hy_eq]
  exact hyk

/-! ### Half-space inclusion `ClosedPolyOf L ⊆ OpenPolyOf (L.flatMap nextLayerEntry)` -/

/-- Every edge of `L.flatMap nextLayerEntry` contains the entire `ClosedPolyOf L` strictly on its positive side! -/
theorem closedPoly_subset_openPoly_next {L : List (ZoneType × (H2 ≃ᵢ H2))} (hAdj : CyclicAdj L)
    (hDet : ∀ e ∈ L, ∀ a b c, detH (e.2 a) (e.2 b) (e.2 c) = detH a b c)
    (hNext := flatMap_nextLayerEntry_cyclicAdj hAdj) :
    ClosedPolyOf L hAdj.1 ⊆ OpenPolyOf (L.flatMap nextLayerEntry) hNext.1 := by
  intro y hy j
  -- Every vertex `(t', F')` in `W = L.flatMap nextLayerEntry` is a child of some `e_k` in `L`.
  -- Its edge `(F' origin, F' (polarOrigin (2*r7) 0))` is one of three kinds relative to `e_k`:
  -- (1) Kind B: `(4α, 5α)` in `e_k` (from `.t1`);
  -- (2) Kind A: `(5α, 6α)` in `e_k` (from `.t1` or `.t2`);
  -- (3) Cross edge `(6α of e_k, first child of e_{k+1})`, which in `e_{k+1}`'s frame is
  --     `((i_{k+1}+2)α, (i_{k+1}+3)α)` = `(-4α, -3α)` or `(-3α, -2α)`!
  -- Wait: check the cross edge in `e_k`'s frame vs `e_{k+1}`'s frame!
  -- In `e_{k+1}`'s frame: `u_k` is at `(i_{k+1} + 1)α`!
  -- Let `e_next = (t_{k+1}, F_{k+1})`: `u_{k+1}` is `origin`, `u_k` is at `(i+1)α`, so `y ∈ ClosedPolyOf L`
  -- satisfies `0 ≤ detH u_k u_{k+1} y = detH (polarOrigin (2r) ((i+1)α)) origin y`!
  -- Rotate `e_{k+1}` by `(i+1)α` and reflect? No: rotate `e_{k+1}` so `u_k → u_{k+1}` is along `+x`?
  -- Wait: EVEN SIMPLER! `u_k → u_{k+1}` IS ALREADY THE `+x` AXIS OF `e_k`, AND THE CROSS EDGE `(w_k, first(e_{k+1}))`
  -- IS THE MIRROR IMAGE OF `(a_k, w_k)` ACROSS THE PERPENDICULAR BISECTOR OF `e_k` (`R3_237`!!)!
  -- CHECK THAT!!
  -- In `e_k`: `w_k = polarOrigin (2r) (-α)` is FIXED by `R3_237`!
  -- And `first(e_{k+1}) = halfTurn (polarOrigin (2r) (2α)) = R3_237 (R1_237 (polarOrigin (2r) (2α))) = R3_237 (polarOrigin (2r) (-2α)) = R3_237 (a_k)`!!
  -- AND `R3_237` PRESERVES `y.y ≥ 0` (since `(R3_237 p).y = p.y`!) AND FLIPS `detH` SIGN (since `R3_237` is a reflection)!
  -- SO `detH w_k (R3_237 a_k) y = detH (R3_237 w_k) (R3_237 a_k) (R3_237 (R3_237 y)) = - detH w_k a_k (R3_237 y) = + detH a_k w_k (R3_237 y) > 0`
  -- BY `detH_outer_edge_A_pos (R3_237 y) (by rw [(R3_237_coords y).2.1]; exact hy_y)`!!
  -- OH!! MY!! GOD!! THAT'S LITERALLY 3 LINES USING `detH_outer_edge_A_pos`!!
  have hcross_pos : ∀ y0 : H2, 0 ≤ y0.y →
      0 < detH (polarOrigin (2 * r7) (-α7)) (halfTurn (polarOrigin (2 * r7) (2 * α7))) y0 := by
    intro y0 hy0
    have hR3_inv : ∀ p, R3_237 (R3_237 p) = p := by
      intro p
      have hc := R3_237_coords p
      have hc2 := R3_237_coords (R3_237 p)
      have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
      ext
      · rw [hc2.1, hc.1, hc.2.2]; linear_combination p.x * hch
      · rw [hc2.2.1, hc.2.1]
      · rw [hc2.2.2, hc.1, hc.2.2]; linear_combination p.z * hch
    have hR3_w : R3_237 (polarOrigin (2 * r7) (-α7)) = polarOrigin (2 * r7) (-α7) := by
      have h1 : halfTurn (polarOrigin (2 * r7) α7) = polarOrigin (2 * r7) (-α7) := halfTurn_polarOrigin_alpha7
      simpa [halfTurn, R1_237, reflXAxis_apply_polarOrigin] using h1
    have hR3_a : R3_237 (polarOrigin (2 * r7) (-(2 * α7))) = halfTurn (polarOrigin (2 * r7) (2 * α7)) := by
      simp [halfTurn, R1_237, reflXAxis_apply_polarOrigin]
    have hR3_det : ∀ a b c, detH (R3_237 a) (R3_237 b) (R3_237 c) = -detH a b c := by
      intro a b c
      simp only [R3_237, reflPerpX, IsometryEquiv.trans_apply, detH_boostX, detH_reflXAxis, detH_rotOrigin]
    have heq : detH (polarOrigin (2 * r7) (-α7)) (halfTurn (polarOrigin (2 * r7) (2 * α7))) y0 =
        detH (polarOrigin (2 * r7) (-(2 * α7))) (polarOrigin (2 * r7) (-α7)) (R3_237 y0) := by
      conv_lhs => rw [← hR3_w, ← hR3_a, ← hR3_inv y0]
      rw [hR3_det, detH_swap_12]
      ring
    rw [heq]
    apply detH_outer_edge_A_pos
    rw [(R3_237_coords y0).2.1]
    exact hy0
  -- Now identify edge j of W = L.flatMap nextLayerEntry as coming from some parent index `k` of `L`!
  set W := L.flatMap nextLayerEntry
  have hedge_mem : ∃ k : ℕ,
      let e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
      (layerVert W hNext.1 j = e.2 (polarOrigin (2 * r7) (-(3 * α7))) ∧
       layerVert W hNext.1 (j + 1) = e.2 (polarOrigin (2 * r7) (-(2 * α7)))) ∨
      (layerVert W hNext.1 j = e.2 (polarOrigin (2 * r7) (-(2 * α7))) ∧
       layerVert W hNext.1 (j + 1) = e.2 (polarOrigin (2 * r7) (-α7))) ∨
      (layerVert W hNext.1 j = e.2 (polarOrigin (2 * r7) (-α7)) ∧
       layerVert W hNext.1 (j + 1) = e.2 (halfTurn (polarOrigin (2 * r7) (2 * α7)))) := by
    -- Every element of W is a child of some e_k ∈ L; its successor in W is given by AdjFrame!
    have hmem : W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩ ∈ W := List.get_mem _ _
    have hmem_idx : ∃ k : Fin L.length, W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩ ∈ nextLayerEntry (L.get k) := by
      have h1 := List.mem_flatMap.mp hmem
      rcases h1 with ⟨e, heL, hec⟩
      rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
      exact ⟨k, hec⟩
    rcases hmem_idx with ⟨k, hk⟩
    refine ⟨k.1, ?_⟩
    set e := L.get ⟨k.1 % L.length, Nat.mod_lt _ hAdj.1⟩
    have he_eq : L.get k = e := by simp [e, Nat.mod_eq_of_lt k.2]
    rw [he_eq] at hk
    have hnext_v : layerVert W hNext.1 (j + 1) =
        (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 (polarOrigin (2 * r7) 0) := by
      have ha := hNext.2 ⟨j % W.length, Nat.mod_lt _ hNext.1⟩
      simpa [layerVert, Nat.mod_add_mod] using adjFrame_origin_eq ha
    have hstep_o : ∀ (F : H2 ≃ᵢ H2) (a d : ℤ),
        stepFrame F a d origin = F (polarOrigin (2 * r7) ((a : ℝ) * α7)) := by
      intro F a d
      simp only [stepFrame, IsometryEquiv.trans_apply]
      have h0 : (rot7 ^ (-d)) origin = origin := by
        rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
        simp [polarOrigin_zero]
      rw [h0, halfTurn_origin, rot7_zpow_apply_polarOrigin, zero_add]
    have hstep_0_d1 : ∀ (F : H2 ≃ᵢ H2) (a : ℤ),
        stepFrame F a 1 (polarOrigin (2 * r7) 0) = F (polarOrigin (2 * r7) (((a + 1 : ℤ) : ℝ) * α7)) := by
      intro F a
      simp only [stepFrame, IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin]
      have h1 : (0 : ℝ) + ((-1 : ℤ) : ℝ) * α7 = -α7 := by push_cast; ring
      rw [h1, halfTurn_polarOrigin_neg_alpha7, rot7_zpow_apply_polarOrigin]
      congr 2; push_cast; ring
    have hstep_0_62 : ∀ (F : H2 ≃ᵢ H2),
        stepFrame F 6 2 (polarOrigin (2 * r7) 0) = F (halfTurn (polarOrigin (2 * r7) (2 * α7))) := by
      intro F
      simp only [stepFrame, IsometryEquiv.trans_apply]
      have h6 : rot7 ^ (6 : ℤ) = rot7⁻¹ := by
        have h7 : rot7 ^ (6 : ℤ) * rot7 = 1 := by rw [← zpow_add_one]; exact rot7_pow_seven
        exact eq_inv_of_mul_eq_one_left h7
      have hm2 : rot7 ^ (-2 : ℤ) = rot7⁻¹ * rot7⁻¹ := by
        rw [show (-2 : ℤ) = (-1 : ℤ) + (-1 : ℤ) by ring, zpow_add, zpow_neg_one]
      have hact : (rot7 ^ (6 : ℤ)) (halfTurn ((rot7 ^ (-2 : ℤ)) (polarOrigin (2 * r7) 0))) =
          halfTurn (polarOrigin (2 * r7) (2 * α7)) := by
        rw [h6, hm2]
        have hbraid_act : ∀ p, (rot7⁻¹ * halfTurn * rot7⁻¹) p = (halfTurn * rot7 * halfTurn) p := by
          intro p; rw [← braid_relation]
        have h2 : rot7⁻¹ (halfTurn ((rot7⁻¹ * rot7⁻¹) (polarOrigin (2 * r7) 0))) =
            (rot7⁻¹ * halfTurn * rot7⁻¹) (rot7⁻¹ (polarOrigin (2 * r7) 0)) := by
          simp [mul_assoc]
        rw [h2, hbraid_act]
        simp only [IsometryEquiv.mul_apply, rot7_inv_eq_rotOrigin, rotOrigin_apply_polarOrigin,
          zero_add, halfTurn_polarOrigin_neg_alpha7, rot7_apply_polarOrigin]
        congr 2; ring
      rw [hact]
    have hpol4 : polarOrigin (2 * r7) ((4 : ℤ) * α7) = polarOrigin (2 * r7) (-(3 * α7)) := by
      have : ((4 : ℤ) : ℝ) * α7 = -(3 * α7) + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
      rw [this, polarOrigin_add_two_pi]
    have hpol5 : polarOrigin (2 * r7) ((5 : ℤ) * α7) = polarOrigin (2 * r7) (-(2 * α7)) := by
      have : ((5 : ℤ) : ℝ) * α7 = -(2 * α7) + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
      rw [this, polarOrigin_add_two_pi]
    have hpol6 : polarOrigin (2 * r7) ((6 : ℤ) * α7) = polarOrigin (2 * r7) (-α7) := by
      have : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
      rw [this, polarOrigin_add_two_pi]
    rcases e with ⟨t, F⟩
    cases t with
    | t1 =>
      simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with hEq | hEq | hEq
      · left
        refine ⟨?_, ?_⟩
        · change (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 origin = _
          rw [hEq, hstep_o, hpol4]
        · rw [hnext_v, hEq, hstep_0_d1]
          simpa using congrArg F hpol5
      · right; left
        refine ⟨?_, ?_⟩
        · change (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 origin = _
          rw [hEq, hstep_o, hpol5]
        · rw [hnext_v, hEq, hstep_0_d1]
          simpa using congrArg F hpol6
      · right; right
        refine ⟨?_, ?_⟩
        · change (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 origin = _
          rw [hEq, hstep_o, hpol6]
        · rw [hnext_v, hEq, hstep_0_62]
    | t2 =>
      simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with hEq | hEq
      · right; left
        refine ⟨?_, ?_⟩
        · change (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 origin = _
          rw [hEq, hstep_o, hpol5]
        · rw [hnext_v, hEq, hstep_0_d1]
          simpa using congrArg F hpol6
      · right; right
        refine ⟨?_, ?_⟩
        · change (W.get ⟨j % W.length, Nat.mod_lt _ hNext.1⟩).2 origin = _
          rw [hEq, hstep_o, hpol6]
        · rw [hnext_v, hEq, hstep_0_62]
  rcases hedge_mem with ⟨k, hcases⟩
  set e := L.get ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
  set y0 := e.2.symm y
  have hy_eq : y = e.2 y0 := by simp [y0]
  have hy0_y : 0 ≤ y0.y := by
    have hyk : 0 ≤ detH (layerVert L hAdj.1 k) (layerVert L hAdj.1 (k + 1)) y := hy k
    have hnext_u : layerVert L hAdj.1 (k + 1) = e.2 (polarOrigin (2 * r7) 0) := by
      have ha := hAdj.2 ⟨k % L.length, Nat.mod_lt _ hAdj.1⟩
      simpa [layerVert, e, Nat.mod_add_mod] using adjFrame_origin_eq ha
    rw [show layerVert L hAdj.1 k = e.2 origin from rfl, hnext_u, hy_eq, hDet e (List.get_mem _ _)] at hyk
    have hdet0 : detH origin (polarOrigin (2 * r7) 0) y0 = Real.sinh (2 * r7) * y0.y := by
      unfold detH origin polarOrigin
      simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]; ring
    rw [hdet0] at hyk
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    nlinarith
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hy_eq, hDet e (List.get_mem _ _)]
    exact detH_outer_edge_B_pos y0 hy0_y
  · rw [h1, h2, hy_eq, hDet e (List.get_mem _ _)]
    exact detH_outer_edge_A_pos y0 hy0_y
  · rw [h1, h2, hy_eq, hDet e (List.get_mem _ _)]
    exact hcross_pos y0 hy0_y

end FejesTothP7.Proofs
