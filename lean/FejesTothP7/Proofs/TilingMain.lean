module

/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
public import FejesTothP7.Proofs.ZoneConvexity

@[expose] public section

/-!
# Global `{3, 7}` Tiling Certification, Rigidity, Lemma 5.1, Lemma 2.1, and Covering Radius `Rc7`

Establishes all global properties of the canonical `{7, 3}` / `{3, 7}` tiling `sites37`:
1. `V_all := {origin} ∪ ⋃_{m ≥ 1} zoneVerts m` is a radius-`r7` packing (`IsPacking r7 V_all`).
2. Every vertex `v ∈ V_all` has a direct (`detH`-preserving) `SiteFrame V_all v` in `Delta237`
   whose 7 neighbors lie in `V_all` at adjacent layers.
3. Edge-rigidity: any isometry mapping an adjacent pair of `V_all` into `V_all` preserves `V_all`.
   Applied to `R1_237, R2_237, R3_237`, this proves `V_all = sites37` and `Delta237`-transitivity.
4. Exact graph distance in `graph37`: `Zone ⟨origin, _⟩ m = zoneVerts m`, yielding **Lemma 5.1**
   (including the convex polygon `P_m` property for all `c₀ : sites37`).
5. **Lemma 2.1** (`lem_2_1_trivial_rearrangement`) and far-away cofinite rigidity.
6. **Covering radius `Rc7`** and polar-sector characterization for every `x : H2`.
-/

noncomputable section
open Classical

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Section 1: Polar cosine packing inequality and 7-neighbor uniqueness -/

/-- Exact hyperbolic identity:
    `cosh ρ * cosh(2r) - sinh ρ * sinh(2r) * cos α7 = cosh(2r) * (cosh(ρ - r) / cosh r)`. -/
lemma lorentz_polarOrigin_cos_alpha7 (ρ : ℝ) :
    Real.cosh ρ * Real.cosh (2 * r7) - Real.sinh ρ * Real.sinh (2 * r7) * Real.cos α7 =
      Real.cosh (2 * r7) * (Real.cosh (ρ - r7) / Real.cosh r7) := by
  rw [cos_alpha7_eq_cosh_div, Real.sinh_two_mul, Real.cosh_sub]
  have hch_r : Real.cosh r7 ≠ 0 := (Real.cosh_pos r7).ne'
  have h2r : Real.cosh (2 * r7) + 1 = 2 * Real.cosh r7 ^ 2 := by rw [cosh_two_r7_eq]; ring
  rw [h2r]
  field_simp [hch_r]

/-- If `0 < ρ ≤ 2 * r7` and `cos α7 ≤ cos φ`, then `lorentz (polarOrigin ρ φ) (polarOrigin (2*r7) 0) ≤ cosh (2*r7)`,
    with strict inequality whenever `ρ < 2 * r7` or `cos α7 < cos φ`. -/
lemma lorentz_polarOrigin_le_cosh_two_r7 {ρ φ : ℝ}
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * r7) (hcos : Real.cos α7 ≤ Real.cos φ) :
    lorentz (polarOrigin ρ φ) (polarOrigin (2 * r7) 0) ≤ Real.cosh (2 * r7) ∧
    ((ρ < 2 * r7 ∨ Real.cos α7 < Real.cos φ) →
      lorentz (polarOrigin ρ φ) (polarOrigin (2 * r7) 0) < Real.cosh (2 * r7)) := by
  rw [lorentz_polarOrigin, sub_zero]
  have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ0
  have hsh2 : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
  have hch2 : 0 < Real.cosh (2 * r7) := Real.cosh_pos (2 * r7)
  have hchr : 0 < Real.cosh r7 := Real.cosh_pos r7
  have h1 : Real.cosh ρ * Real.cosh (2 * r7) - Real.sinh ρ * Real.sinh (2 * r7) * Real.cos φ ≤
      Real.cosh (2 * r7) * (Real.cosh (ρ - r7) / Real.cosh r7) := by
    rw [← lorentz_polarOrigin_cos_alpha7]
    nlinarith [mul_pos hshρ hsh2]
  have hcosh_le : Real.cosh (ρ - r7) ≤ Real.cosh r7 := by
    rw [← Real.cosh_abs (ρ - r7)]
    have habs : |ρ - r7| ≤ r7 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (abs_nonneg _), abs_of_pos r7_pos]; exact habs)
  have hdiv_le : Real.cosh (ρ - r7) / Real.cosh r7 ≤ 1 := (div_le_one hchr).mpr hcosh_le
  refine ⟨by nlinarith, fun hstrict => ?_⟩
  rcases hstrict with hlt | hlt
  · have habs : |ρ - r7| < r7 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hcosh_lt : Real.cosh (ρ - r7) < Real.cosh r7 := by
      rw [← Real.cosh_abs (ρ - r7)]
      exact Real.cosh_lt_cosh.mpr (by rw [abs_of_nonneg (abs_nonneg _), abs_of_pos r7_pos]; exact habs)
    have hdiv_lt : Real.cosh (ρ - r7) / Real.cosh r7 < 1 := (div_lt_one hchr).mpr hcosh_lt
    nlinarith
  · have h1' : Real.cosh ρ * Real.cosh (2 * r7) - Real.sinh ρ * Real.sinh (2 * r7) * Real.cos φ <
        Real.cosh (2 * r7) * (Real.cosh (ρ - r7) / Real.cosh r7) := by
      rw [← lorentz_polarOrigin_cos_alpha7]
      nlinarith [mul_pos hshρ hsh2]
    nlinarith

lemma dist_lt_two_r7_iff_lorentz_lt {p q : H2} :
    dist p q < 2 * r7 ↔ lorentz p q < Real.cosh (2 * r7) := by
  constructor
  · intro h
    rw [← cosh_dist]
    exact Real.cosh_lt_cosh.mpr (by rw [abs_of_nonneg dist_nonneg, abs_of_pos (by linarith [r7_pos])]; exact h)
  · intro h
    rw [← cosh_dist] at h
    have := Real.cosh_lt_cosh.mp h
    rw [abs_of_nonneg dist_nonneg, abs_of_pos (by linarith [r7_pos])] at this
    exact this

lemma polarOrigin_add_int_two_pi (ρ θ : ℝ) (k : ℤ) :
    polarOrigin ρ (θ + (k : ℝ) * (2 * Real.pi)) = polarOrigin ρ θ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have heq : θ + (((n : ℤ) + 1 : ℤ) : ℝ) * (2 * Real.pi) =
        (θ + ((n : ℤ) : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
    rw [heq, polarOrigin_add_two_pi, ih]
  | pred n ih =>
    have heq : (θ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * (2 * Real.pi)) + 2 * Real.pi =
        θ + ((-(n : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [← polarOrigin_add_two_pi, heq, ih]

lemma detH_polarOrigin_origin_polarOrigin (r₁ θ₁ r₂ θ₂ : ℝ) :
    detH (polarOrigin r₁ θ₁) origin (polarOrigin r₂ θ₂) =
      Real.sinh r₁ * Real.sinh r₂ * Real.sin (θ₁ - θ₂) := by
  unfold detH origin polarOrigin
  dsimp only
  rw [Real.sin_sub]
  ring

/-- For any `θ : ℝ`, there exists `k : Fin 7` and `m : ℤ` with `|θ - (k * α7 + m * 2π)| ≤ α7 / 2`. -/
lemma exists_fin7_angle_close (θ : ℝ) :
    ∃ (k : Fin 7) (m : ℤ), |θ - ((k.1 : ℝ) * α7 + (m : ℝ) * (2 * Real.pi))| ≤ α7 / 2 := by
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  set t := θ / α7
  set n : ℤ := ⌊t + 1 / 2⌋
  have hlo : (n : ℝ) ≤ t + 1 / 2 := Int.floor_le (t + 1 / 2)
  have hhi : t + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one (t + 1 / 2)
  have habs : |t - (n : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  set r : ℤ := n % 7
  set m : ℤ := n / 7
  have hr0 : 0 ≤ r := Int.emod_nonneg n (by norm_num)
  have hr7 : r < 7 := Int.emod_lt_of_pos n (by norm_num)
  have hdiv : (n : ℝ) = (r.toNat : ℝ) + 7 * (m : ℝ) := by
    have h1 : n = r + 7 * m := by have := Int.emod_add_mul_ediv n 7; omega
    have h2 : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    exact_mod_cast (show n = (r.toNat : ℤ) + 7 * m by omega)
  refine ⟨⟨r.toNat, by omega⟩, m, ?_⟩
  have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; ring
  have hmul : θ - ((r.toNat : ℝ) * α7 + (m : ℝ) * (2 * Real.pi)) = (t - (n : ℝ)) * α7 := by
    have ht : t * α7 = θ := div_mul_cancel₀ θ hα_pos.ne'
    linear_combination -ht + α7 * hdiv + (m : ℝ) * h7a
  rw [hmul, abs_mul, abs_of_pos hα_pos]
  nlinarith

/-- Reduction of any integer multiple `n * α7` modulo `2π` to `k * α7` (`k : Fin 7`). -/
lemma exists_fin7_polarOrigin_int (n : ℤ) :
    ∃ k : Fin 7, polarOrigin (2 * r7) ((n : ℝ) * α7) = polarOrigin (2 * r7) ((k.1 : ℝ) * α7) := by
  set r : ℤ := n % 7
  set q : ℤ := n / 7
  have hr0 : 0 ≤ r := Int.emod_nonneg n (by norm_num)
  have hr7 : r < 7 := Int.emod_lt_of_pos n (by norm_num)
  refine ⟨⟨r.toNat, by omega⟩, ?_⟩
  have hdiv : (n : ℝ) = (r.toNat : ℝ) + 7 * (q : ℝ) := by
    have h1 : n = r + 7 * q := by have := Int.emod_add_mul_ediv n 7; omega
    have h2 : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    exact_mod_cast (show n = (r.toNat : ℤ) + 7 * q by omega)
  have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; ring
  have heq : (n : ℝ) * α7 = (r.toNat : ℝ) * α7 + (q : ℝ) * (2 * Real.pi) := by
    linear_combination α7 * hdiv + (q : ℝ) * h7a
  rw [heq, polarOrigin_add_int_two_pi]

/-- If `V` is an `r7`-packing and `F` maps `origin` to `v` and all 7 rays `(2r, k α7)` into `V`,
    then `F` is a `SiteFrame V v`! -/
def mkSiteFrameOfPacking {V : Set H2} {v : H2} (hpack : IsPacking r7 V)
    (F : H2 ≃ᵢ H2) (ho : F origin = v)
    (hnbr : ∀ k : Fin 7, F (polarOrigin (2 * r7) ((k : ℝ) * α7)) ∈ V) :
    SiteFrame V v where
  φ := F
  origin_eq := ho
  nbr_mem := hnbr
  nbr_iff := by
    intro w hw
    constructor
    · intro hadj
      rcases exists_polarOrigin (F.symm w) with ⟨θ, hθ⟩
      have hd : dist origin (F.symm w) = 2 * r7 := by
        rw [← F.dist_eq, IsometryEquiv.apply_symm_apply, ho]; exact hadj
      rw [hd] at hθ
      have hw_eq : w = F (polarOrigin (2 * r7) θ) := by
        rw [← hθ, IsometryEquiv.apply_symm_apply]
      rcases exists_fin7_angle_close θ with ⟨k, m, hclose⟩
      refine ⟨k, ?_⟩
      by_contra hne
      have hdist_ge : 2 * r7 ≤ dist w (F (polarOrigin (2 * r7) ((k.1 : ℝ) * α7))) :=
        hpack w hw _ (hnbr k) hne
      set δ := θ - ((k.1 : ℝ) * α7 + (m : ℝ) * (2 * Real.pi))
      have hcos_gt : Real.cos α7 < Real.cos δ := by
        have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
        have hα_lt : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
        rw [← Real.cos_abs δ]
        exact Real.strictAntiOn_cos ⟨abs_nonneg δ, by linarith⟩ ⟨hα_pos.le, hα_lt.le⟩ (by linarith)
      have hlt_lor : lorentz w (F (polarOrigin (2 * r7) ((k.1 : ℝ) * α7))) < Real.cosh (2 * r7) := by
        rw [hw_eq, isometry_lorentz]
        have hrot : lorentz (polarOrigin (2 * r7) θ) (polarOrigin (2 * r7) ((k.1 : ℝ) * α7)) =
            lorentz (polarOrigin (2 * r7) δ) (polarOrigin (2 * r7) 0) := by
          rw [lorentz_polarOrigin, lorentz_polarOrigin, sub_zero]
          have hcos_eq : Real.cos (θ - (k.1 : ℝ) * α7) = Real.cos δ := by
            have heq : θ - (k.1 : ℝ) * α7 = δ + (m : ℝ) * (2 * Real.pi) := by ring
            rw [heq, Real.cos_add_int_mul_two_pi]
          rw [hcos_eq]
        rw [hrot]
        exact (lorentz_polarOrigin_le_cosh_two_r7 (by linarith [r7_pos]) le_rfl hcos_gt.le).2 (Or.inr hcos_gt)
      have hlt_dist := dist_lt_two_r7_iff_lorentz_lt.mpr hlt_lor
      linarith
    · rintro ⟨k, rfl⟩
      unfold Adj37
      rw [← ho, F.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]

/-! ### Section 2: `V_upto`, `V_all`, and `IsPacking r7 V_all` -/

/-- Vertices of the first `m` zones together with `origin`. -/
def V_upto (m : ℕ) : Set H2 :=
  {origin} ∪ ⋃ k ∈ Finset.Icc 1 m, {x | x ∈ zoneVerts k}

/-- All vertices generated by the concentric zone layers together with `origin`. -/
def V_all : Set H2 :=
  {origin} ∪ ⋃ (m : ℕ) (_ : 1 ≤ m), {x | x ∈ zoneVerts m}

lemma V_upto_subset_closedPoly {m : ℕ} (hm : 1 ≤ m) :
    V_upto m ⊆ ClosedPoly m hm := by
  intro x hx
  rcases hx with rfl | hx
  · exact fun k => ((zoneConvexInv m hm).origin_open k).le
  · simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨k, ⟨hk1, hkm⟩, hxk⟩
    exact closedPoly_mono hk1 hkm (zoneVert_mem_closedPoly hk1 hxk)

lemma V_upto_succ (m : ℕ) :
    V_upto (m + 1) = V_upto m ∪ {x | x ∈ zoneVerts (m + 1)} := by
  ext x
  simp only [V_upto, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | ⟨k, ⟨hk1, hkm⟩, hxk⟩)
    · left; left; rfl
    · by_cases hlast : k = m + 1
      · right; rwa [← hlast]
      · left; right; exact ⟨k, ⟨hk1, by omega⟩, hxk⟩
  · rintro ((rfl | ⟨k, ⟨hk1, hkm⟩, hxk⟩) | hx)
    · left; rfl
    · right; exact ⟨k, ⟨hk1, by omega⟩, hxk⟩
    · right; exact ⟨m + 1, ⟨by omega, le_rfl⟩, hx⟩

lemma V_upto_zero : V_upto 0 = {origin} := by
  ext x; simp [V_upto]

lemma mem_V_upto_of_mem_zoneVerts {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) {x : H2}
    (hx : x ∈ zoneVerts k) : x ∈ V_upto m := by
  right; simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq]
  exact ⟨k, ⟨hk, hkm⟩, hx⟩

lemma layerVert_mem_zoneVerts (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    layerVert (zoneLayer m) (zoneLayer_length_pos m hm) k ∈ zoneVerts m := by
  unfold zoneVerts layerVert
  exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩

/-- Helper: `((zoneLayer 1).get i).2 origin = polarOrigin (2 * r7) (i.1 * α7)`. -/
lemma zoneLayer1_get_origin (i : Fin (zoneLayer 1).length) :
    ((zoneLayer 1).get i).2 origin = polarOrigin (2 * r7) ((i.1 : ℝ) * α7) := by
  have hi7 : i.1 < 7 := lt_of_lt_of_eq i.2 zoneLayer1_length
  have hv := zoneLayer1_layerVert i.1
  have hget : ((zoneLayer 1).get i).2 origin =
      layerVert zoneLayer1 (by rw [zoneLayer1_length]; omega) i.1 := by
    unfold layerVert
    have hmod : i.1 % zoneLayer1.length = i.1 := Nat.mod_eq_of_lt i.2
    have hfin : (i : Fin zoneLayer1.length) = ⟨i.1 % zoneLayer1.length, Nat.mod_lt _ (by rw [zoneLayer1_length]; omega)⟩ :=
      Fin.ext hmod.symm
    exact congrArg (fun x => (zoneLayer1.get x).2 origin) hfin
  rw [hget, hv]

/-- Separation between `zoneVerts (m + 1)` and `V_upto m`, assuming `IsPacking r7 (V_upto m)`. -/
lemma dist_layer_succ_prev {m : ℕ} (hm : 1 ≤ m) (hpack : IsPacking r7 (V_upto m))
    {x y : H2} (hx : x ∈ zoneVerts (m + 1)) (hy : y ∈ V_upto m) :
    2 * r7 ≤ dist x y := by
  have hy_poly : y ∈ ClosedPoly m hm := V_upto_subset_closedPoly hm hy
  have hsucc : zoneLayer (m + 1) = (zoneLayer m).flatMap nextLayerEntry := by
    cases m with | zero => omega | succ n => rfl
  simp only [zoneVerts, hsucc, List.mem_map, List.mem_flatMap] at hx
  rcases hx with ⟨e', ⟨e, heL, he'c⟩, rfl⟩
  rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
  set hL := zoneLayer_length_pos m hm
  set hAdj := zoneLayer_cyclicAdj m hm
  set hDet := fun a ha => (zoneLayer_mem_Delta237_and_detH m a ha).2
  have hInv := zoneConvexInv m hm
  have huk_mem : layerVert (zoneLayer m) hL k.1 ∈ ClosedPoly m hm := layerVert_mem_closedPoly hInv k.1
  have hget_mod : (zoneLayer m).get ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩ = (zoneLayer m).get k := by
    congr 1; ext; exact Nat.mod_eq_of_lt k.2
  rcases hk_eq : (zoneLayer m).get k with ⟨t, F⟩
  rw [hk_eq] at he'c
  have hu_eq : layerVert (zoneLayer m) hL k.1 = F origin := by unfold layerVert; rw [hget_mod, hk_eq]
  have hu_mem : F origin ∈ V_upto m := by
    rw [← hu_eq]; exact mem_V_upto_of_mem_zoneVerts hm le_rfl (layerVert_mem_zoneVerts m hm k.1)
  have htype1 : ∀ (a : ℤ), ((t = .t1 ∧ a = 4) ∨ a = 5) →
      2 * r7 ≤ dist (F (polarOrigin (2 * r7) ((a : ℝ) * α7))) y := by
    intro a ha
    have hf := isFoot_type1_child hAdj hDet k.1 huk_mem (j := a) (by
      rcases ha with ⟨ht, rfl⟩ | rfl
      · left; exact ⟨by rw [hget_mod, hk_eq]; exact ht, rfl⟩
      · right; rfl)
    simp only [hget_mod, hk_eq] at hf
    by_cases hyu : y = F origin
    · rw [hyu, F.dist_eq, dist_polarOrigin_origin (2 * r7) _ (by linarith [r7_pos])]
    · have hlt := hf.2 y hy_poly (by rw [hu_eq]; exact hyu)
      have hl : lorentz (F (polarOrigin (2 * r7) ((a : ℝ) * α7))) (F origin) = Real.cosh (2 * r7) := by
        rw [isometry_lorentz, lorentz_symm, lorentz_origin_polarOrigin]
      rw [hu_eq, hl] at hlt
      by_contra hnot
      push Not at hnot
      have := dist_lt_two_r7_iff_lorentz_lt.mp hnot
      linarith
  have htype2 : 2 * r7 ≤ dist (F (polarOrigin (2 * r7) ((6 : ℤ) * α7))) y := by
    by_contra hlt
    push Not at hlt
    set w := F (polarOrigin (2 * r7) ((6 : ℤ) * α7))
    set u := layerVert (zoneLayer m) hL k.1
    set uNext := layerVert (zoneLayer m) hL (k.1 + 1)
    set M := mid u uNext
    have he_next : uNext = F (polarOrigin (2 * r7) 0) := by
      have ha := hAdj.2 ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
      have h1 := adjFrame_origin_eq ha
      rw [hget_mod, hk_eq] at h1
      simpa [uNext, layerVert, Nat.mod_add_mod] using h1
    set G : H2 ≃ᵢ H2 := (boostX r7).trans F
    have hG_o : G origin = M := by
      simp only [G, IsometryEquiv.trans_apply, boostX_apply_origin]
      rw [show M = mid (F origin) (F (polarOrigin (2 * r7) 0)) by rw [← hu_eq, ← he_next], mid_frame_edge]
    have hG_u : G (polarOrigin (-r7) 0) = u := by
      simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, neg_add_cancel,
        polarOrigin_zero, hu_eq]
    have hG_uNext : G (polarOrigin r7 0) = uNext := by
      simp only [G, IsometryEquiv.trans_apply, boostX_apply_polarOrigin_zero, ← two_mul, he_next]
    have hG_w : G (polarOrigin h7 (-(Real.pi / 2))) = w := by
      simp only [G, IsometryEquiv.trans_apply, boostX_r7_altitude, w]
      congr 1
      have h6 : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
      rw [h6, polarOrigin_add_two_pi]
    have hG_det : ∀ a b c, detH (G a) (G b) (G c) = detH a b c := by
      intro a b c
      simp only [G, IsometryEquiv.trans_apply]
      have hF_det : ∀ p q r, detH (F p) (F q) (F r) = detH p q r :=
        hDet (t, F) (by rw [← hk_eq]; exact List.get_mem _ _)
      rw [hF_det, detH_boostX]
    set y0 := G.symm y
    have hy_eq : y = G y0 := by simp [y0]
    have hy0_y : 0 ≤ y0.y := by
      have hyk : 0 ≤ detH u uNext y := hy_poly k.1
      rw [← hG_u, ← hG_uNext, hy_eq, hG_det] at hyk
      have hdet : detH (polarOrigin (-r7) 0) (polarOrigin r7 0) y0 =
          2 * Real.sinh r7 * Real.cosh r7 * y0.y := by
        unfold detH polarOrigin
        simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, Real.sinh_neg, Real.cosh_neg]
        ring
      rw [hdet] at hyk
      have hpos : 0 < 2 * Real.sinh r7 * Real.cosh r7 :=
        mul_pos (mul_pos zero_lt_two (Real.sinh_pos_iff.mpr r7_pos)) (Real.cosh_pos r7)
      nlinarith
    have hlor : lorentz w y = Real.cosh h7 * y0.z + Real.sinh h7 * y0.y := by
      rw [← hG_w, hy_eq, isometry_lorentz]
      unfold lorentz polarOrigin
      simp only [Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
      ring
    have hlor_lt : lorentz w y < Real.cosh (2 * r7) := dist_lt_two_r7_iff_lorentz_lt.mp hlt
    have hsh_h : 0 ≤ Real.sinh h7 * y0.y := mul_nonneg (Real.sinh_pos_iff.mpr h7_pos).le hy0_y
    have hch_prod : Real.cosh h7 * Real.cosh r7 = Real.cosh (2 * r7) := by
      rw [cosh_h7_eq, div_mul_cancel₀ _ (Real.cosh_pos r7).ne']
    have hy0z_lt : y0.z < Real.cosh r7 := by
      have hch_h_pos : 0 < Real.cosh h7 := Real.cosh_pos h7
      nlinarith
    have hd_My : dist M y < r7 := by
      have hl : lorentz M y = y0.z := by
        rw [← hG_o, hy_eq, isometry_lorentz]; unfold lorentz origin; ring
      rw [← hl] at hy0z_lt
      rw [← cosh_dist] at hy0z_lt
      have := Real.cosh_lt_cosh.mp hy0z_lt
      rw [abs_of_nonneg dist_nonneg, abs_of_pos r7_pos] at this
      exact this
    have hd_uM : dist u M = r7 := by
      rw [dist_mid_left, hu_eq, he_next, F.dist_eq, dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
      ring
    have hd_uy : dist u y < 2 * r7 := by
      have htri := dist_triangle u M y
      linarith
    have hy_ne_u : y ≠ u := by
      intro heq
      rw [heq, hu_eq] at hlt
      have hd : dist w (F origin) = 2 * r7 := by
        rw [F.dist_eq, dist_polarOrigin_origin (2 * r7) _ (by linarith [r7_pos])]
      linarith
    have hpack_uy := hpack u (by rw [hu_eq]; exact hu_mem) y hy (Ne.symm hy_ne_u)
    linarith
  cases t with
  | t1 =>
    simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
    rcases he'c with rfl | rfl | rfl
    · rw [stepFrame_origin_eq]; exact htype1 4 (Or.inl ⟨rfl, rfl⟩)
    · rw [stepFrame_origin_eq]; exact htype1 5 (Or.inr rfl)
    · rw [stepFrame_origin_eq]; exact htype2
  | t2 =>
    simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
    rcases he'c with rfl | rfl
    · rw [stepFrame_origin_eq]; exact htype1 5 (Or.inr rfl)
    · rw [stepFrame_origin_eq]; exact htype2

/-- Inner neighbors of every entry `e' ∈ zoneLayer m` (`m ≥ 1`). -/
lemma zoneLayer_inner_nbrs {m : ℕ} (hm : 1 ≤ m) (k : Fin (zoneLayer m).length) :
    let e := (zoneLayer m).get k
    e.2 (polarOrigin (2 * r7) α7) ∈ (if m = 1 then ({origin} : Set H2) else {x | x ∈ zoneVerts (m - 1)}) ∧
    (e.1 = .t2 → e.2 (polarOrigin (2 * r7) (2 * α7)) ∈ {x | x ∈ zoneVerts (m - 1)}) := by
  cases m with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      dsimp only
      have hk := zoneLayer1_get k
      have he : (zoneLayer 1).get k = (.t1, (rot7 ^ (-1 : ℤ)).trans (halfTurn.trans (rot7 ^ (k.1 : ℤ)))) := hk
      rw [he]
      simp only [ite_true, Set.mem_singleton_iff, reduceCtorEq, IsEmpty.forall_iff, and_true]
      simp only [IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin]
      have h0 : α7 + ((-1 : ℤ) : ℝ) * α7 = 0 := by push_cast; ring
      rw [h0, halfTurn_polarOrigin_zero]
      rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
      simp [polarOrigin_zero]
    | succ r =>
      dsimp only
      have hne1 : r + 1 + 1 ≠ 1 := by omega
      simp only [hne1, ite_false, Nat.add_sub_cancel, Set.mem_ofPred_eq]
      have hmem : (zoneLayer (r + 2)).get k ∈ (zoneLayer (r + 1)).flatMap nextLayerEntry := List.get_mem _ _
      rcases List.mem_flatMap.mp hmem with ⟨e0, he0L, he0c⟩
      rcases List.mem_iff_get.mp he0L with ⟨p, rfl⟩
      have hAdj := zoneLayer_cyclicAdj (r + 1) (by omega)
      have hp_mem : ((zoneLayer (r + 1)).get p).2 origin ∈ zoneVerts (r + 1) :=
        List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
      have hp_next_mem : ((zoneLayer (r + 1)).get p).2 (polarOrigin (2 * r7) 0) ∈ zoneVerts (r + 1) := by
        have ha := hAdj.2 p
        rw [← adjFrame_origin_eq ha]
        exact List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
      have hstep1 : ∀ (F : H2 ≃ᵢ H2) (a : ℤ),
          stepFrame F a 1 (polarOrigin (2 * r7) α7) = F origin := by
        intro F a
        simp only [stepFrame, IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin]
        have h1 : α7 + ((-1 : ℤ) : ℝ) * α7 = 0 := by push_cast; ring
        rw [h1, halfTurn_polarOrigin_zero]
        rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
        simp [polarOrigin_zero]
      have hstep62_1 : ∀ (F : H2 ≃ᵢ H2),
          stepFrame F 6 2 (polarOrigin (2 * r7) α7) = F (polarOrigin (2 * r7) 0) := by
        intro F
        simp only [stepFrame, IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin]
        have h1 : α7 + ((-2 : ℤ) : ℝ) * α7 = -α7 := by push_cast; ring
        rw [h1, halfTurn_polarOrigin_neg_alpha7, rot7_zpow_apply_polarOrigin]
        have h2 : α7 + ((6 : ℤ) : ℝ) * α7 = 0 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
        rw [h2, polarOrigin_add_two_pi]
      have hstep62_2 : ∀ (F : H2 ≃ᵢ H2),
          stepFrame F 6 2 (polarOrigin (2 * r7) (2 * α7)) = F origin := by
        intro F
        simp only [stepFrame, IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin]
        have h1 : 2 * α7 + ((-2 : ℤ) : ℝ) * α7 = 0 := by push_cast; ring
        rw [h1, halfTurn_polarOrigin_zero]
        rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
        simp [polarOrigin_zero]
      rcases hp_eq : (zoneLayer (r + 1)).get p with ⟨t0, F0⟩
      rw [hp_eq] at he0c hp_mem hp_next_mem
      cases t0 with
      | t1 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he0c
        rcases he0c with hEq | hEq | hEq
        · rw [hEq]; exact ⟨by rw [hstep1]; exact hp_mem, fun h => by cases h⟩
        · rw [hEq]; exact ⟨by rw [hstep1]; exact hp_mem, fun h => by cases h⟩
        · rw [hEq]; exact ⟨by rw [hstep62_1]; exact hp_next_mem, fun _ => by rw [hstep62_2]; exact hp_mem⟩
      | t2 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he0c
        rcases he0c with hEq | hEq
        · rw [hEq]; exact ⟨by rw [hstep1]; exact hp_mem, fun h => by cases h⟩
        · rw [hEq]; exact ⟨by rw [hstep62_1]; exact hp_next_mem, fun _ => by rw [hstep62_2]; exact hp_mem⟩

/-- Separation within `zoneVerts (m + 1)` using convexity + inner neighbors in `V_upto m`. -/
lemma dist_layer_same {m : ℕ} (hm : 1 ≤ m) (hpack : IsPacking r7 (V_upto m))
    {x y : H2} (hx : x ∈ zoneVerts (m + 1)) (hy : y ∈ zoneVerts (m + 1)) (hne : x ≠ y) :
    2 * r7 ≤ dist x y := by
  by_contra hlt
  push Not at hlt
  set hL := zoneLayer_length_pos (m + 1) (by omega)
  have hAdj := zoneLayer_cyclicAdj (m + 1) (by omega)
  have hDet := fun a ha => (zoneLayer_mem_Delta237_and_detH (m + 1) a ha).2
  simp only [zoneVerts, List.mem_map] at hx
  rcases hx with ⟨e, heL, rfl⟩
  rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
  have hy_poly : y ∈ ClosedPoly (m + 1) (by omega) := zoneVert_mem_closedPoly (by omega) hy
  set ek := (zoneLayer (m + 1)).get k
  have hget_mod : (zoneLayer (m + 1)).get ⟨k.1 % (zoneLayer (m + 1)).length, Nat.mod_lt _ hAdj.1⟩ = ek := by
    congr 1; ext; exact Nat.mod_eq_of_lt k.2
  have hu_eq : layerVert (zoneLayer (m + 1)) hL k.1 = ek.2 origin := by unfold layerVert; rw [hget_mod]
  have he_next : layerVert (zoneLayer (m + 1)) hL (k.1 + 1) = ek.2 (polarOrigin (2 * r7) 0) := by
    have ha := hAdj.2 ⟨k.1 % (zoneLayer (m + 1)).length, Nat.mod_lt _ hAdj.1⟩
    have h1 := adjFrame_origin_eq ha
    rw [hget_mod] at h1
    simpa [layerVert, Nat.mod_add_mod] using h1
  have he_prev : layerVert (zoneLayer (m + 1)) hL (k.1 + (zoneLayer (m + 1)).length - 1) =
      ek.2 (polarOrigin (2 * r7) (((ek.1.innerCount + 1 : ℕ) : ℝ) * α7)) := by
    have hidx : ((k.1 + (zoneLayer (m + 1)).length - 1) % (zoneLayer (m + 1)).length + 1) %
        (zoneLayer (m + 1)).length = k.1 % (zoneLayer (m + 1)).length := by
      have hpos := hAdj.1
      rw [Nat.mod_add_mod]
      have heq : k.1 + (zoneLayer (m + 1)).length - 1 + 1 = k.1 + (zoneLayer (m + 1)).length := by omega
      rw [heq, Nat.add_mod_right]
    have ha := hAdj.2 ⟨(k.1 + (zoneLayer (m + 1)).length - 1) % (zoneLayer (m + 1)).length, Nat.mod_lt _ hAdj.1⟩
    have h1 := adjFrame_prev_eq ha
    have hfin : (⟨((k.1 + (zoneLayer (m + 1)).length - 1) % (zoneLayer (m + 1)).length + 1) %
        (zoneLayer (m + 1)).length, Nat.mod_lt _ hAdj.1⟩ : Fin (zoneLayer (m + 1)).length) =
        ⟨k.1 % (zoneLayer (m + 1)).length, Nat.mod_lt _ hAdj.1⟩ := Fin.ext hidx
    rw [hfin, hget_mod] at h1
    exact h1.symm
  -- Write y = ek.2 (polarOrigin ρ θ) with 0 < ρ < 2*r7 and θ ∈ [0, (i+1)*α7]!
  set q := ek.2.symm y
  have hy_eq : y = ek.2 q := by simp [q]
  set ρ := dist origin q
  have hρ_pos : 0 < ρ := by
    have hne' : origin ≠ q := fun h => hne (by rw [hy_eq, ← h])
    exact dist_pos.mpr hne'
  have hρ_lt : ρ < 2 * r7 := by
    change dist origin q < 2 * r7
    rw [← ek.2.dist_eq, ← hy_eq]; exact hlt
  have hq_y : 0 ≤ q.y := by
    have h1 : 0 ≤ detH (layerVert (zoneLayer (m + 1)) hL k.1)
        (layerVert (zoneLayer (m + 1)) hL (k.1 + 1)) y := hy_poly k.1
    rw [hu_eq, he_next, hy_eq, hDet ek (List.get_mem _ _)] at h1
    have hd : detH origin (polarOrigin (2 * r7) 0) q = Real.sinh (2 * r7) * q.y := by
      unfold detH origin polarOrigin
      simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero]; ring
    rw [hd] at h1
    have hsh : 0 < Real.sinh (2 * r7) := Real.sinh_pos_iff.mpr (by linarith [r7_pos])
    nlinarith
  have hq_prev : 0 ≤ detH (polarOrigin (2 * r7) (((ek.1.innerCount + 1 : ℕ) : ℝ) * α7)) origin q := by
    have h1 : 0 ≤ detH (layerVert (zoneLayer (m + 1)) hL (k.1 + (zoneLayer (m + 1)).length - 1))
        (layerVert (zoneLayer (m + 1)) hL (k.1 + (zoneLayer (m + 1)).length - 1 + 1)) y :=
      hy_poly (k.1 + (zoneLayer (m + 1)).length - 1)
    have h2 : layerVert (zoneLayer (m + 1)) hL (k.1 + (zoneLayer (m + 1)).length - 1 + 1) = ek.2 origin := by
      have hpos := hAdj.1
      have heq : k.1 + (zoneLayer (m + 1)).length - 1 + 1 = k.1 + (zoneLayer (m + 1)).length := by omega
      rw [heq, layerVert_add_len, hu_eq]
    rw [he_prev, h2, hy_eq, hDet ek (List.get_mem _ _)] at h1
    exact h1
  rcases exists_polarOrigin q with ⟨θ₀, hθ₀⟩
  set m2 : ℤ := ⌊θ₀ / (2 * Real.pi)⌋
  set θ : ℝ := θ₀ - (m2 : ℝ) * (2 * Real.pi)
  have hq_pol : q = polarOrigin ρ θ := by
    have heq : θ = θ₀ + ((-(m2 : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [heq, polarOrigin_add_int_two_pi]; exact hθ₀
  have hθ_lo : 0 ≤ θ := by
    have h1 : (m2 : ℝ) ≤ θ₀ / (2 * Real.pi) := Int.floor_le _
    have h2 : (m2 : ℝ) * (2 * Real.pi) ≤ θ₀ := (le_div_iff₀ (by positivity)).mp h1
    linarith
  have hθ_hi2 : θ < 2 * Real.pi := by
    have h1 : θ₀ / (2 * Real.pi) < (m2 : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : θ₀ < ((m2 : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ (by positivity)).mp h1
    linarith
  have hsin_nn : 0 ≤ Real.sin θ := by
    have hq_y' : q.y = Real.sinh ρ * Real.sin θ := by rw [hq_pol]; rfl
    have hsh : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ_pos
    nlinarith
  have hθ_le_pi : θ ≤ Real.pi := by
    by_contra hgt
    push Not at hgt
    have hneg : Real.sin θ < 0 := by
      have h1 := Real.sin_pos_of_pos_of_lt_pi (show 0 < θ - Real.pi by linarith) (show θ - Real.pi < Real.pi by linarith)
      rw [Real.sin_sub_pi] at h1; linarith
    linarith
  have hsin_prev : 0 ≤ Real.sin (((ek.1.innerCount + 1 : ℕ) : ℝ) * α7 - θ) := by
    rw [hq_pol, detH_polarOrigin_origin_polarOrigin] at hq_prev
    have hpos : 0 < Real.sinh (2 * r7) * Real.sinh ρ :=
      mul_pos (Real.sinh_pos_iff.mpr (by linarith [r7_pos])) (Real.sinh_pos_iff.mpr hρ_pos)
    nlinarith
  have hθ_le_wedge : θ ≤ ((ek.1.innerCount + 1 : ℕ) : ℝ) * α7 := by
    by_contra hgt
    push Not at hgt
    set φ := θ - ((ek.1.innerCount + 1 : ℕ) : ℝ) * α7
    have hφ_pos : 0 < φ := by linarith
    have hφ_lt : φ < Real.pi := by
      have h1 : 0 < ((ek.1.innerCount + 1 : ℕ) : ℝ) * α7 := by unfold α7 alphaP; positivity
      linarith
    have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ_pos hφ_lt
    have hneg : Real.sin (((ek.1.innerCount + 1 : ℕ) : ℝ) * α7 - θ) = -Real.sin φ := by
      rw [show ((ek.1.innerCount + 1 : ℕ) : ℝ) * α7 - θ = -φ by ring, Real.sin_neg]
    linarith
  have hinner := zoneLayer_inner_nbrs (m := m + 1) (by omega) k
  have hne1 : m + 1 ≠ 1 := by omega
  simp only [hne1, ite_false, Nat.add_sub_cancel, Set.mem_ofPred_eq] at hinner
  have hp1_mem : ek.2 (polarOrigin (2 * r7) α7) ∈ V_upto m :=
    mem_V_upto_of_mem_zoneVerts hm le_rfl hinner.1
  have hα_lt : α7 < Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
  have hα_pos : 0 < α7 := by unfold α7 alphaP; positivity
  have hcontra : ∀ (φ_p : ℝ), |θ - φ_p| ≤ α7 → ek.2 (polarOrigin (2 * r7) φ_p) ∈ V_upto m → False := by
    intro φ_p hclose hp_mem
    have hcos_ge : Real.cos α7 ≤ Real.cos (θ - φ_p) := by
      rw [← Real.cos_abs (θ - φ_p)]
      exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, by linarith⟩ ⟨hα_pos.le, hα_lt.le⟩ hclose
    have hlt_lor : lorentz y (ek.2 (polarOrigin (2 * r7) φ_p)) < Real.cosh (2 * r7) := by
      rw [hy_eq, hq_pol, isometry_lorentz]
      have hrot : lorentz (polarOrigin ρ θ) (polarOrigin (2 * r7) φ_p) =
          lorentz (polarOrigin ρ (θ - φ_p)) (polarOrigin (2 * r7) 0) := by
        rw [lorentz_polarOrigin, lorentz_polarOrigin, sub_zero]
      rw [hrot]
      exact (lorentz_polarOrigin_le_cosh_two_r7 hρ_pos hρ_lt.le hcos_ge).2 (Or.inl hρ_lt)
    have hd_lt := dist_lt_two_r7_iff_lorentz_lt.mpr hlt_lor
    have hd_ge := dist_layer_succ_prev hm hpack hy hp_mem
    linarith
  cases ht : ek.1 with
  | t1 =>
    rw [ht] at hθ_le_wedge
    simp only [ZoneType.innerCount] at hθ_le_wedge
    push_cast at hθ_le_wedge
    exact hcontra α7 (abs_le.mpr ⟨by linarith, by linarith⟩) hp1_mem
  | t2 =>
    rw [ht] at hθ_le_wedge
    simp only [ZoneType.innerCount] at hθ_le_wedge
    push_cast at hθ_le_wedge
    by_cases hmid : θ ≤ 2 * α7
    · exact hcontra α7 (abs_le.mpr ⟨by linarith, by linarith⟩) hp1_mem
    · have hp2_mem : ek.2 (polarOrigin (2 * r7) (2 * α7)) ∈ V_upto m :=
        mem_V_upto_of_mem_zoneVerts hm le_rfl (hinner.2 ht)
      exact hcontra (2 * α7) (abs_le.mpr ⟨by linarith, by linarith⟩) hp2_mem

/-- Base case `IsPacking r7 (V_upto 1)`. -/
lemma isPacking_V_upto_one : IsPacking r7 (V_upto 1) := by
  have hmem1 : ∀ x ∈ V_upto 1, x = origin ∨ ∃ k : Fin 7, x = polarOrigin (2 * r7) ((k.1 : ℝ) * α7) := by
    intro x hx
    rcases hx with rfl | hx
    · left; rfl
    · right
      simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq] at hx
      rcases hx with ⟨k, ⟨hk1, hk2⟩, hxk⟩
      have hk_eq : k = 1 := by omega
      rw [hk_eq] at hxk
      simp only [zoneVerts, List.mem_map] at hxk
      rcases hxk with ⟨e, heL, rfl⟩
      rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
      have hi7 : i.1 < 7 := lt_of_lt_of_eq i.2 zoneLayer1_length
      exact ⟨⟨i.1, hi7⟩, zoneLayer1_get_origin i⟩
  intro x hx y hy hxy
  rcases hmem1 x hx with rfl | ⟨i, rfl⟩ <;> rcases hmem1 y hy with rfl | ⟨j, rfl⟩
  · exact absurd rfl hxy
  · rw [dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
  · rw [dist_polarOrigin_origin (2 * r7) _ (by linarith [r7_pos])]
  · have hij : i.1 ≠ j.1 := fun h => hxy (by rw [h])
    by_contra hlt
    push Not at hlt
    have hlor_lt := dist_lt_two_r7_iff_lorentz_lt.mp hlt
    rw [lorentz_polarOrigin] at hlor_lt
    have hcos_le : Real.cos (((i.1 : ℝ) - (j.1 : ℝ)) * α7) ≤ Real.cos α7 := by
      set d : ℕ := if i.1 < j.1 then j.1 - i.1 else i.1 - j.1
      have hd_ge : 1 ≤ d := by simp only [d]; split_ifs <;> omega
      have hd_le : d ≤ 6 := by simp only [d]; split_ifs <;> omega
      have hcos_d : Real.cos (((i.1 : ℝ) - (j.1 : ℝ)) * α7) = Real.cos ((d : ℝ) * α7) := by
        simp only [d]; split_ifs with hlt'
        · rw [← Real.cos_neg]; congr 1
          have : ((j.1 - i.1 : ℕ) : ℝ) = (j.1 : ℝ) - (i.1 : ℝ) := Nat.cast_sub hlt'.le
          rw [this]; ring
        · have hle : j.1 ≤ i.1 := by omega
          have : ((i.1 - j.1 : ℕ) : ℝ) = (i.1 : ℝ) - (j.1 : ℝ) := Nat.cast_sub hle
          rw [this]
      rw [hcos_d]
      by_cases hd3 : d ≤ 3
      · apply Real.strictAntiOn_cos.antitoneOn
        · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
        · constructor
          · unfold α7 alphaP; positivity
          · have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
            unfold α7 alphaP; nlinarith [Real.pi_pos]
        · have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_ge
          unfold α7 alphaP; nlinarith [Real.pi_pos]
      · have hd' : 7 - d ≤ 3 ∧ 1 ≤ 7 - d := by omega
        have hcos_sym : Real.cos ((d : ℝ) * α7) = Real.cos (((7 - d : ℕ) : ℝ) * α7) := by
          rw [← Real.cos_two_pi_sub]
          congr 1
          have hsub : ((7 - d : ℕ) : ℝ) = 7 - (d : ℝ) := Nat.cast_sub (by omega)
          rw [hsub]; unfold α7 alphaP; ring
        rw [hcos_sym]
        apply Real.strictAntiOn_cos.antitoneOn
        · exact ⟨by unfold α7 alphaP; positivity, by unfold α7 alphaP; linarith [Real.pi_pos]⟩
        · constructor
          · unfold α7 alphaP; positivity
          · have : ((7 - d : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hd'.1
            unfold α7 alphaP; nlinarith [Real.pi_pos]
        · have : (1 : ℝ) ≤ ((7 - d : ℕ) : ℝ) := by exact_mod_cast hd'.2
          unfold α7 alphaP; nlinarith [Real.pi_pos]
    have hl : Real.cosh (2 * r7) * Real.cosh (2 * r7) -
        Real.sinh (2 * r7) * Real.sinh (2 * r7) * Real.cos α7 = Real.cosh (2 * r7) := by
      have h := lorentz_polarOrigin_cos_alpha7 (2 * r7)
      have hsub : 2 * r7 - r7 = r7 := by ring
      rw [hsub, div_self (Real.cosh_pos r7).ne', mul_one] at h
      exact h
    have harg : (i.1 : ℝ) * α7 - (j.1 : ℝ) * α7 = ((i.1 : ℝ) - (j.1 : ℝ)) * α7 := by ring
    rw [harg] at hlor_lt
    nlinarith [sq_nonneg (Real.sinh (2 * r7))]

lemma isPacking_V_upto (m : ℕ) : IsPacking r7 (V_upto m) := by
  induction m with
  | zero =>
    rw [V_upto_zero]; intro x hx y hy hxy
    rw [Set.mem_singleton_iff] at hx hy; exact absurd (hx.trans hy.symm) hxy
  | succ k ih =>
    cases k with
    | zero => exact isPacking_V_upto_one
    | succ n =>
      rw [V_upto_succ]
      intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact ih x hx y hy hxy
      · rw [dist_comm]; exact dist_layer_succ_prev (by omega) ih hy hx
      · exact dist_layer_succ_prev (by omega) ih hx hy
      · exact dist_layer_same (by omega) ih hx hy hxy

/-- **Global Packing Theorem for `V_all`**: `IsPacking r7 V_all`. -/
theorem isPacking_V_all : IsPacking r7 V_all := by
  have hmem : ∀ x ∈ V_all, ∃ m, x ∈ V_upto m := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, Or.inl rfl⟩
    · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
      rcases hx with ⟨m, hm, hxm⟩
      exact ⟨m, mem_V_upto_of_mem_zoneVerts hm le_rfl hxm⟩
  have hmono : ∀ {a b}, a ≤ b → V_upto a ⊆ V_upto b := by
    intro a b hab x hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq] at hx
      rcases hx with ⟨k, ⟨hk1, hka⟩, hxk⟩
      exact mem_V_upto_of_mem_zoneVerts hk1 (le_trans hka hab) hxk
  intro x hx y hy hxy
  rcases hmem x hx with ⟨m₁, hm₁⟩
  rcases hmem y hy with ⟨m₂, hm₂⟩
  exact isPacking_V_upto (max m₁ m₂) x (hmono (le_max_left _ _) hm₁) y (hmono (le_max_right _ _) hm₂) hxy

/-! ### Section 3: Exact 7-neighbor layer structure & `SiteFrame V_all v` -/

/-- Exact 7-neighbor layer classification for every entry `k` in `zoneLayer m` (`m ≥ 1`). -/
lemma zoneLayer_all_seven_nbrs {m : ℕ} (hm : 1 ≤ m) (k : Fin (zoneLayer m).length) :
    ((zoneLayer m).get k).2 (polarOrigin (2 * r7) 0) =
      layerVert (zoneLayer m) (zoneLayer_length_pos m hm) (k.1 + 1) ∧
    (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ ((zoneLayer m).get k).1.innerCount →
      ((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈
        if m = 1 then ({origin} : Set H2) else {x | x ∈ zoneVerts (m - 1)}) ∧
    ((zoneLayer m).get k).2 (polarOrigin (2 * r7) (((((zoneLayer m).get k).1.innerCount + 1 : ℕ) : ℝ) * α7)) =
      layerVert (zoneLayer m) (zoneLayer_length_pos m hm) (k.1 + (zoneLayer m).length - 1) ∧
    (∀ j : Fin 7, ((zoneLayer m).get k).1.innerCount + 2 ≤ j.1 →
      ((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈ zoneVerts (m + 1)) := by
  set hL := zoneLayer_length_pos m hm
  set hAdj := zoneLayer_cyclicAdj m hm
  have hget_mod : (zoneLayer m).get ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩ = (zoneLayer m).get k := by
    congr 1; ext; exact Nat.mod_eq_of_lt k.2
  have h0 : ((zoneLayer m).get k).2 (polarOrigin (2 * r7) 0) = layerVert (zoneLayer m) hL (k.1 + 1) := by
    have ha := hAdj.2 ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
    have h1 := adjFrame_origin_eq ha
    rw [hget_mod] at h1
    simpa [layerVert, Nat.mod_add_mod] using h1.symm
  have hprev : ((zoneLayer m).get k).2
        (polarOrigin (2 * r7) (((((zoneLayer m).get k).1.innerCount + 1 : ℕ) : ℝ) * α7)) =
      layerVert (zoneLayer m) hL (k.1 + (zoneLayer m).length - 1) := by
    have hidx : ((k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length + 1) % (zoneLayer m).length =
        k.1 % (zoneLayer m).length := by
      have hpos := hAdj.1
      rw [Nat.mod_add_mod]
      have heq : k.1 + (zoneLayer m).length - 1 + 1 = k.1 + (zoneLayer m).length := by omega
      rw [heq, Nat.add_mod_right]
    have ha := hAdj.2 ⟨(k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
    have h1 := adjFrame_prev_eq ha
    have hfin : (⟨((k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length + 1) % (zoneLayer m).length,
        Nat.mod_lt _ hAdj.1⟩ : Fin (zoneLayer m).length) =
        ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩ := Fin.ext hidx
    rw [hfin, hget_mod] at h1
    exact h1
  have hinner_all := zoneLayer_inner_nbrs hm k
  have hinner : ∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ ((zoneLayer m).get k).1.innerCount →
      ((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈
        if m = 1 then ({origin} : Set H2) else {x | x ∈ zoneVerts (m - 1)} := by
    intro j hj1 hji
    cases ht : ((zoneLayer m).get k).1 with
    | t1 =>
      rw [ht] at hji; simp only [ZoneType.innerCount] at hji
      have hj_eq : j.1 = 1 := by omega
      rw [hj_eq]; simpa using hinner_all.1
    | t2 =>
      rw [ht] at hji; simp only [ZoneType.innerCount] at hji
      have hj_cases : j.1 = 1 ∨ j.1 = 2 := by omega
      rcases hj_cases with hj1' | hj2'
      · rw [hj1']; simpa using hinner_all.1
      · have hm_ne1 : m ≠ 1 := by
          intro hm1; subst hm1
          have h1 := zoneLayer1_get k
          change (zoneLayer1.get k).1 = .t2 at ht
          rw [h1] at ht; cases ht
        rw [hj2']
        simpa [hm_ne1] using hinner_all.2 ht
  have houter : ∀ j : Fin 7, ((zoneLayer m).get k).1.innerCount + 2 ≤ j.1 →
      ((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈ zoneVerts (m + 1) := by
    intro j hj
    have hsucc : zoneLayer (m + 1) = (zoneLayer m).flatMap nextLayerEntry := by
      cases m with | zero => omega | succ n => rfl
    have hmem_succ : ∀ x, x ∈ nextLayerEntry ((zoneLayer m).get k) → x.2 origin ∈ zoneVerts (m + 1) := by
      intro x hx
      rw [zoneVerts, hsucc, List.mem_map]
      exact ⟨x, List.mem_flatMap.mpr ⟨(zoneLayer m).get k, List.get_mem _ _, hx⟩, rfl⟩
    by_cases hcross : j.1 = ((zoneLayer m).get k).1.innerCount + 2
    · set ePrev := (zoneLayer m).get ⟨(k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
      have hidx : ((k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length + 1) % (zoneLayer m).length =
          k.1 % (zoneLayer m).length := by
        have hpos := hAdj.1
        rw [Nat.mod_add_mod]
        have heq : k.1 + (zoneLayer m).length - 1 + 1 = k.1 + (zoneLayer m).length := by omega
        rw [heq, Nat.add_mod_right]
      have ha : AdjFrame ePrev ((zoneLayer m).get k) := by
        have h := hAdj.2 ⟨(k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩
        have hfin : (⟨((k.1 + (zoneLayer m).length - 1) % (zoneLayer m).length + 1) % (zoneLayer m).length,
            Nat.mod_lt _ hAdj.1⟩ : Fin (zoneLayer m).length) =
            ⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hAdj.1⟩ := Fin.ext hidx
        rw [hfin, hget_mod] at h
        exact h
      have hchild_mem : (ZoneType.t2, stepFrame ePrev.2 6 2) ∈ nextLayerEntry ePrev := by
        rcases ePrev with ⟨tP, FP⟩; cases tP <;> simp [nextLayerEntry]
      have hvert_eq : ((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) =
          stepFrame ePrev.2 6 2 origin := by
        rw [hcross, stepFrame_origin_eq]
        unfold AdjFrame at ha
        rw [ha]
        simp only [IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin, Int.cast_neg, Int.cast_natCast]
        have h1 : ((((zoneLayer m).get k).1.innerCount + 2 : ℕ) : ℝ) * α7 +
            -((((zoneLayer m).get k).1.innerCount + 1 : ℕ) : ℝ) * α7 = α7 := by
          push_cast; ring
        rw [h1, halfTurn_polarOrigin_alpha7]
        congr 1
        have h6 : ((6 : ℤ) : ℝ) * α7 = -α7 + 2 * Real.pi := by unfold α7 alphaP; push_cast; ring
        rw [h6, polarOrigin_add_two_pi]
      rw [hvert_eq, zoneVerts, hsucc, List.mem_map]
      exact ⟨(.t2, stepFrame ePrev.2 6 2), List.mem_flatMap.mpr ⟨ePrev, List.get_mem _ _, hchild_mem⟩, rfl⟩
    · rcases he_eq : (zoneLayer m).get k with ⟨t, F⟩
      cases t with
      | t1 =>
        rw [he_eq] at hj hcross
        simp only [ZoneType.innerCount] at hj hcross
        have hj_cases : j.1 = 4 ∨ j.1 = 5 ∨ j.1 = 6 := by omega
        rcases hj_cases with h4 | h5 | h6
        · have h := hmem_succ (.t1, stepFrame F 4 1) (by rw [he_eq]; simp [nextLayerEntry])
          rw [stepFrame_origin_eq] at h; simpa [he_eq, h4] using h
        · have h := hmem_succ (.t1, stepFrame F 5 1) (by rw [he_eq]; simp [nextLayerEntry])
          rw [stepFrame_origin_eq] at h; simpa [he_eq, h5] using h
        · have h := hmem_succ (.t2, stepFrame F 6 2) (by rw [he_eq]; simp [nextLayerEntry])
          rw [stepFrame_origin_eq] at h; simpa [he_eq, h6] using h
      | t2 =>
        rw [he_eq] at hj hcross
        simp only [ZoneType.innerCount] at hj hcross
        have hj_cases : j.1 = 5 ∨ j.1 = 6 := by omega
        rcases hj_cases with h5 | h6
        · have h := hmem_succ (.t1, stepFrame F 5 1) (by rw [he_eq]; simp [nextLayerEntry])
          rw [stepFrame_origin_eq] at h; simpa [he_eq, h5] using h
        · have h := hmem_succ (.t2, stepFrame F 6 2) (by rw [he_eq]; simp [nextLayerEntry])
          rw [stepFrame_origin_eq] at h; simpa [he_eq, h6] using h
  exact ⟨h0, hinner, hprev, houter⟩

lemma mem_V_all_of_mem_zoneVerts {m : ℕ} (hm : 1 ≤ m) {x : H2} (hx : x ∈ zoneVerts m) :
    x ∈ V_all := by
  right; simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨m, hm, hx⟩

/-- Every `v ∈ V_all` has a direct (`detH`-preserving) `SiteFrame V_all v` with `F.φ ∈ Delta237`! -/
theorem exists_direct_siteFrame_V_all {v : H2} (hv : v ∈ V_all) :
    ∃ F : SiteFrame V_all v,
      F.φ ∈ Delta237 ∧ ∀ a b c, detH (F.φ a) (F.φ b) (F.φ c) = detH a b c := by
  rcases hv with rfl | hv
  · refine ⟨mkSiteFrameOfPacking isPacking_V_all (IsometryEquiv.refl H2) rfl ?_, Delta237.one_mem,
      fun _ _ _ => rfl⟩
    intro k
    have h1 := zoneLayer1_layerVert k.1
    rw [← h1]
    exact mem_V_all_of_mem_zoneVerts (m := 1) (by omega) (layerVert_mem_zoneVerts 1 (by omega) k.1)
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hv
    rcases hv with ⟨m, hm, hvm⟩
    simp only [zoneVerts, List.mem_map] at hvm
    rcases hvm with ⟨e, heL, rfl⟩
    rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
    have hDelta := zoneLayer_mem_Delta237_and_detH m ((zoneLayer m).get k) (List.get_mem _ _)
    have h7 := zoneLayer_all_seven_nbrs hm k
    refine ⟨mkSiteFrameOfPacking isPacking_V_all ((zoneLayer m).get k).2 rfl ?_, hDelta.1, hDelta.2⟩
    intro j
    by_cases hj0 : j.1 = 0
    · rw [hj0]; simp only [Nat.cast_zero, zero_mul, h7.1]
      exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm (k.1 + 1))
    · by_cases hji : j.1 ≤ ((zoneLayer m).get k).1.innerCount
      · have h := h7.2.1 j (by omega) hji
        split_ifs at h with hm1
        · rw [Set.mem_singleton_iff] at h; rw [h]; exact Or.inl rfl
        · exact mem_V_all_of_mem_zoneVerts (by omega) h
      · by_cases hjprev : j.1 = ((zoneLayer m).get k).1.innerCount + 1
        · rw [hjprev, h7.2.2.1]
          exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm _)
        · exact mem_V_all_of_mem_zoneVerts (by omega) (h7.2.2.2 j (by omega))

/-! ### Section 4: Edge-Rigidity, `V_all = sites37`, and `Delta237`-Transitivity -/

lemma reflXAxis_reflXAxis (p : H2) : reflXAxis (reflXAxis p) = p :=
  H2.ext rfl (neg_neg p.y) rfl

/-- Any isometry fixing `origin` and mapping `polarOrigin (2*r7) 0` to `polarOrigin (2*r7) (j₀*α7)`
    maps every `polarOrigin (2*r7) (k*α7)` to `polarOrigin (2*r7) ((j₀ ± k)*α7)`. -/
lemma isometry_fix_origin_maps_seven {ψ : H2 ≃ᵢ H2} (h0 : ψ origin = origin)
    {j₀ : ℤ} (h1 : ψ (polarOrigin (2 * r7) 0) = polarOrigin (2 * r7) ((j₀ : ℝ) * α7)) :
    ∀ k : ℤ, ∃ k' : Fin 7, ψ (polarOrigin (2 * r7) ((k : ℝ) * α7)) =
      polarOrigin (2 * r7) ((k'.1 : ℝ) * α7) := by
  rcases isometry_detH_sign ψ with hpos | hneg
  · have hψ_eq : ψ = rotOrigin ((j₀ : ℝ) * α7) := by
      apply direct_isometry_eq_of_eq_two (ρ := 2 * r7) (θ := 0) hpos (detH_rotOrigin _)
        (by rw [h0, rotOrigin_apply_origin]) (by linarith [r7_pos])
      rw [h1, rotOrigin_apply_polarOrigin, zero_add]
    intro k
    rw [hψ_eq, rotOrigin_apply_polarOrigin]
    have heq : (k : ℝ) * α7 + (j₀ : ℝ) * α7 = ((k + j₀ : ℤ) : ℝ) * α7 := by push_cast; ring
    rw [heq]; exact exists_fin7_polarOrigin_int (k + j₀)
  · have hψ_eq : ψ = reflXAxis.trans (rotOrigin ((j₀ : ℝ) * α7)) := by
      have hdirect : reflXAxis.trans ψ = rotOrigin ((j₀ : ℝ) * α7) := by
        apply direct_isometry_eq_of_eq_two (ρ := 2 * r7) (θ := 0)
          (fun a b c => by simp [hneg, detH_reflXAxis]) (detH_rotOrigin _)
          (by simp [reflXAxis_apply_origin, h0, rotOrigin_apply_origin])
          (by linarith [r7_pos])
        simp [reflXAxis_apply_polarOrigin, h1, rotOrigin_apply_polarOrigin]
      have hpt : ∀ p, ψ p = (reflXAxis.trans (rotOrigin ((j₀ : ℝ) * α7))) p := by
        intro p
        have := congrArg (fun f => f (reflXAxis p)) hdirect
        simpa [IsometryEquiv.trans_apply, reflXAxis_reflXAxis] using this
      ext p
      · exact congrArg H2.x (hpt p)
      · exact congrArg H2.y (hpt p)
      · exact congrArg H2.z (hpt p)
    intro k
    rw [hψ_eq]
    simp only [IsometryEquiv.trans_apply, reflXAxis_apply_polarOrigin, rotOrigin_apply_polarOrigin]
    have heq : -((k : ℝ) * α7) + (j₀ : ℝ) * α7 = ((j₀ - k : ℤ) : ℝ) * α7 := by push_cast; ring
    rw [heq]; exact exists_fin7_polarOrigin_int (j₀ - k)

/-- **Local Propagation**: if `φ` maps an adjacent pair `u, w ∈ V_all` into `V_all`, then `φ` maps
    ALL 7 neighbors of `u` in `V_all` into `V_all`! -/
lemma isometry_maps_all_nbrs_V_all {φ : H2 ≃ᵢ H2} {u w : H2}
    (hu : u ∈ V_all) (hw : w ∈ V_all) (hadj : Adj37 u w)
    (hφu : φ u ∈ V_all) (hφw : φ w ∈ V_all) :
    ∀ v ∈ V_all, Adj37 u v → φ v ∈ V_all := by
  rcases exists_direct_siteFrame_V_all hu with ⟨Fu, _, _⟩
  rcases exists_direct_siteFrame_V_all hφu with ⟨F', _, _⟩
  rcases (Fu.nbr_iff w hw).mp hadj with ⟨i₁, hw_eq⟩
  have hadj' : Adj37 (φ u) (φ w) := by unfold Adj37 at *; rw [φ.dist_eq]; exact hadj
  rcases (F'.nbr_iff (φ w) hφw).mp hadj' with ⟨i₀, hφw_eq⟩
  set ψ := (rotOrigin ((i₁.1 : ℝ) * α7)).trans (Fu.φ.trans (φ.trans F'.φ.symm))
  have hψ0 : ψ origin = origin := by
    simp only [ψ, IsometryEquiv.trans_apply, rotOrigin_apply_origin, Fu.origin_eq]
    exact F'.φ.symm_apply_eq.mpr F'.origin_eq.symm
  have hψ1 : ψ (polarOrigin (2 * r7) 0) = polarOrigin (2 * r7) (((i₀.1 : ℤ) : ℝ) * α7) := by
    simp only [ψ, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin, zero_add]
    rw [← hw_eq, hφw_eq, IsometryEquiv.symm_apply_apply, Int.cast_natCast]
  intro v hv huv
  rcases (Fu.nbr_iff v hv).mp huv with ⟨k, hv_eq⟩
  rcases isometry_fix_origin_maps_seven hψ0 hψ1 ((k.1 : ℤ) - (i₁.1 : ℤ)) with ⟨k', hk'⟩
  have harg : (((k.1 : ℤ) - (i₁.1 : ℤ) : ℤ) : ℝ) * α7 + (i₁.1 : ℝ) * α7 = (k.1 : ℝ) * α7 := by
    push_cast; ring
  have hφv : φ v = F'.φ (polarOrigin (2 * r7) ((k'.1 : ℝ) * α7)) := by
    have hstep : ψ (polarOrigin (2 * r7) ((((k.1 : ℤ) - (i₁.1 : ℤ) : ℤ) : ℝ) * α7)) = F'.φ.symm (φ v) := by
      simp only [ψ, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin, harg, ← hv_eq]
    rw [hstep] at hk'
    have := congrArg F'.φ hk'
    simpa using this
  rw [hφv]
  exact F'.nbr_mem k'

/-- **Origin-Edge Rigidity**: if `φ origin ∈ V_all` and `φ (polarOrigin (2*r7) 0) ∈ V_all`,
    then `φ '' V_all ⊆ V_all`! -/
lemma isometry_maps_V_all_of_origin_edge {φ : H2 ≃ᵢ H2}
    (h0 : φ origin ∈ V_all) (h1 : φ (polarOrigin (2 * r7) 0) ∈ V_all) :
    ∀ x ∈ V_all, φ x ∈ V_all := by
  have h_upto : ∀ m : ℕ, ∀ x ∈ V_upto m, φ x ∈ V_all := by
    intro m
    induction m with
    | zero =>
      rw [V_upto_zero]; intro x hx; rw [Set.mem_singleton_iff] at hx; rwa [hx]
    | succ k ih =>
      rw [V_upto_succ]
      intro x hx
      rcases hx with hx | hx
      · exact ih x hx
      · cases k with
        | zero =>
          have ho_mem : origin ∈ V_all := Or.inl rfl
          have he1_mem : polarOrigin (2 * r7) 0 ∈ V_all := by
            have hv := zoneLayer1_layerVert 0
            simp only [Nat.cast_zero, zero_mul] at hv
            rw [← hv]
            exact mem_V_all_of_mem_zoneVerts (m := 1) (by omega) (layerVert_mem_zoneVerts 1 (by omega) 0)
          have hadj1 : Adj37 origin (polarOrigin (2 * r7) 0) := by
            unfold Adj37; rw [dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
          have hadjx : Adj37 origin x := by
            simp only [zoneVerts, List.mem_map] at hx
            rcases hx with ⟨e, heL, rfl⟩
            rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
            rw [zoneLayer1_get_origin i]
            unfold Adj37; rw [dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
          exact isometry_maps_all_nbrs_V_all ho_mem he1_mem hadj1 h0 h1 x
            (mem_V_all_of_mem_zoneVerts (by omega) hx) hadjx
        | succ n =>
          have hsucc : zoneLayer (n + 2) = (zoneLayer (n + 1)).flatMap nextLayerEntry := rfl
          simp only [zoneVerts, hsucc, List.mem_map, List.mem_flatMap] at hx
          rcases hx with ⟨e', ⟨e, heL, he'c⟩, rfl⟩
          rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
          set u := ((zoneLayer (n + 1)).get i).2 origin
          have hu_mem_z : u ∈ zoneVerts (n + 1) := List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
          have hu_upto : u ∈ V_upto (n + 1) := mem_V_upto_of_mem_zoneVerts (by omega) le_rfl hu_mem_z
          have hu_all : u ∈ V_all := mem_V_all_of_mem_zoneVerts (by omega) hu_mem_z
          set p := ((zoneLayer (n + 1)).get i).2 (polarOrigin (2 * r7) α7)
          have hp_inner := (zoneLayer_inner_nbrs (m := n + 1) (by omega) i).1
          have hp_upto : p ∈ V_upto (n + 1) := by
            dsimp only [p]
            split_ifs at hp_inner with hn1
            · rw [Set.mem_singleton_iff] at hp_inner; rw [hp_inner]; exact Or.inl rfl
            · exact mem_V_upto_of_mem_zoneVerts (by omega) (by omega) hp_inner
          have hp_all : p ∈ V_all := by
            dsimp only [p]
            split_ifs at hp_inner with hn1
            · rw [Set.mem_singleton_iff] at hp_inner; rw [hp_inner]; exact Or.inl rfl
            · exact mem_V_all_of_mem_zoneVerts (by omega) hp_inner
          have hadj_up : Adj37 u p := by
            unfold Adj37
            rw [((zoneLayer (n + 1)).get i).2.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
          have hadj_ux : Adj37 u (e'.2 origin) := by
            unfold Adj37
            rcases hi_eq : (zoneLayer (n + 1)).get i with ⟨t0, F0⟩
            rw [hi_eq] at he'c
            have hu_eq : u = F0 origin := by dsimp only [u]; rw [hi_eq]
            rw [hu_eq]
            cases t0 with
            | t1 =>
              simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
              rcases he'c with rfl | rfl | rfl <;>
                rw [stepFrame_origin_eq, F0.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
            | t2 =>
              simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at he'c
              rcases he'c with rfl | rfl <;>
                rw [stepFrame_origin_eq, F0.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
          have hx_all : e'.2 origin ∈ V_all := by
            apply mem_V_all_of_mem_zoneVerts (m := n + 2) (by omega)
            rw [zoneVerts, hsucc, List.mem_map]
            exact ⟨e', List.mem_flatMap.mpr ⟨_, List.get_mem _ _, he'c⟩, rfl⟩
          exact isometry_maps_all_nbrs_V_all hu_all hp_all hadj_up (ih u hu_upto) (ih p hp_upto) _ hx_all hadj_ux
  intro x hx
  rcases hx with rfl | hx
  · exact h0
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨m, hm, hxm⟩
    exact h_upto m x (mem_V_upto_of_mem_zoneVerts hm le_rfl hxm)

/-- Every generator of `Delta237` preserves `V_all`, hence `∀ g ∈ Delta237, g '' V_all = V_all`! -/
theorem delta237_preserves_V_all {g : H2 ≃ᵢ H2} (hg : g ∈ Delta237) :
    g '' V_all = V_all := by
  have hR1_inv : R1_237⁻¹ = R1_237 := by
    have hmul : R1_237 * R1_237 = 1 := by
      ext p
      · exact congrArg H2.x (reflXAxis_reflXAxis p)
      · exact congrArg H2.y (reflXAxis_reflXAxis p)
      · exact congrArg H2.z (reflXAxis_reflXAxis p)
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have hR2_inv : R2_237⁻¹ = R2_237 := by
    have hsq : ∀ p, R2_237 (R2_237 p) = p := by
      intro p
      rcases exists_polarOrigin p with ⟨θ, hp⟩
      rw [hp]
      simp only [R2_237, reflRay, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin,
        reflXAxis_apply_polarOrigin]
      congr 1; ring
    have hmul : R2_237 * R2_237 = 1 := by
      ext p
      · exact congrArg H2.x (hsq p)
      · exact congrArg H2.y (hsq p)
      · exact congrArg H2.z (hsq p)
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have hR3_inv : R3_237⁻¹ = R3_237 := by
    have hsq : ∀ p, R3_237 (R3_237 p) = p := by
      intro p
      have hc := R3_237_coords p
      have hc2 := R3_237_coords (R3_237 p)
      have hch := Real.cosh_sq_sub_sinh_sq (2 * r7)
      ext
      · rw [hc2.1, hc.1, hc.2.2]; linear_combination p.x * hch
      · rw [hc2.2.1, hc.2.1]
      · rw [hc2.2.2, hc.1, hc.2.2]; linear_combination p.z * hch
    have hmul : R3_237 * R3_237 = 1 := by
      ext p
      · exact congrArg H2.x (hsq p)
      · exact congrArg H2.y (hsq p)
      · exact congrArg H2.z (hsq p)
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have hsub : ∀ h ∈ Delta237, (∀ x ∈ V_all, h x ∈ V_all) ∧ (∀ x ∈ V_all, h⁻¹ x ∈ V_all) := by
    intro h hh
    refine Subgroup.closure_induction
      (p := fun k _ => (∀ x ∈ V_all, k x ∈ V_all) ∧ (∀ x ∈ V_all, k⁻¹ x ∈ V_all)) ?_ ?_ ?_ ?_ hh
    · intro k hk
      have he0 : polarOrigin (2 * r7) 0 ∈ V_all := by
        have hv := zoneLayer1_layerVert 0; simp only [Nat.cast_zero, zero_mul] at hv
        rw [← hv]; exact mem_V_all_of_mem_zoneVerts (m := 1) (by omega) (layerVert_mem_zoneVerts 1 (by omega) 0)
      have he1 : polarOrigin (2 * r7) α7 ∈ V_all := by
        have hv := zoneLayer1_layerVert 1; simp only [Nat.cast_one, one_mul] at hv
        rw [← hv]; exact mem_V_all_of_mem_zoneVerts (m := 1) (by omega) (layerVert_mem_zoneVerts 1 (by omega) 1)
      rcases hk with rfl | rfl | rfl
      · have hf : ∀ x ∈ V_all, R1_237 x ∈ V_all := by
          apply isometry_maps_V_all_of_origin_edge
          · simp [R1_237, reflXAxis_apply_origin]; exact Or.inl rfl
          · simpa [R1_237, reflXAxis_apply_polarOrigin] using he0
        exact ⟨hf, by rw [hR1_inv]; exact hf⟩
      · have hf : ∀ x ∈ V_all, R2_237 x ∈ V_all := by
          apply isometry_maps_V_all_of_origin_edge
          · simp [R2_237, reflRay, rotOrigin_apply_origin, reflXAxis_apply_origin]; exact Or.inl rfl
          · have hR2 : R2_237 (polarOrigin (2 * r7) 0) = polarOrigin (2 * r7) α7 := by
              simp only [R2_237, reflRay, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin,
                reflXAxis_apply_polarOrigin]
              congr 1; unfold α7 alphaP; ring
            rw [hR2]; exact he1
        exact ⟨hf, by rw [hR2_inv]; exact hf⟩
      · have hf : ∀ x ∈ V_all, R3_237 x ∈ V_all := by
          apply isometry_maps_V_all_of_origin_edge
          · rw [R3_237, reflPerpX_apply_origin]; exact he0
          · have hR3 : R3_237 (polarOrigin (2 * r7) 0) = origin := by
              have h := halfTurn_polarOrigin_zero
              simpa [halfTurn, R1_237, reflXAxis_apply_polarOrigin] using h
            rw [hR3]; exact Or.inl rfl
        exact ⟨hf, by rw [hR3_inv]; exact hf⟩
    · exact ⟨fun x hx => hx, fun x hx => hx⟩
    · intro a b _ _ iha ihb
      exact ⟨fun x hx => iha.1 (b x) (ihb.1 x hx),
        fun x hx => by rw [mul_inv_rev]; exact ihb.2 (a⁻¹ x) (iha.2 x hx)⟩
    · intro a _ iha
      exact ⟨iha.2, by rw [inv_inv]; exact iha.1⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (hsub g hg).1 x hx
  · intro hy
    refine ⟨g⁻¹ y, (hsub g hg).2 y hy, ?_⟩
    change (g * g⁻¹) y = y; simp

/-- **Global Equality Theorem**: `V_all = sites37`! -/
theorem V_all_eq_sites37 : V_all = sites37 := by
  ext x
  constructor
  · intro hx
    rcases exists_direct_siteFrame_V_all hx with ⟨F, hF_mem, _⟩
    exact ⟨F.φ, hF_mem, F.origin_eq⟩
  · rintro ⟨g, hg, rfl⟩
    have ho : origin ∈ V_all := Or.inl rfl
    rw [← delta237_preserves_V_all hg]
    exact ⟨origin, ho, rfl⟩

lemma origin_mem_sites37 : origin ∈ sites37 := ⟨1, Delta237.one_mem, rfl⟩

theorem isPacking_sites37 : IsPacking r7 sites37 := by
  rw [← V_all_eq_sites37]; exact isPacking_V_all

theorem delta237_preserves_sites37 {g : H2 ≃ᵢ H2} (hg : g ∈ Delta237) :
    g '' sites37 = sites37 := by
  rw [← V_all_eq_sites37]; exact delta237_preserves_V_all hg

/-- Every `v ∈ sites37` has a direct (`detH`-preserving) `SiteFrame sites37 v` in `Delta237`. -/
theorem exists_direct_siteFrame_sites37 {v : H2} (hv : v ∈ sites37) :
    ∃ F : SiteFrame sites37 v,
      F.φ ∈ Delta237 ∧ ∀ a b c, detH (F.φ a) (F.φ b) (F.φ c) = detH a b c := by
  rw [← V_all_eq_sites37] at hv ⊢
  exact exists_direct_siteFrame_V_all hv

/-- **Transitivity of `Delta237` (by direct isometries) on `sites37`**. -/
theorem delta237_direct_transitive {u v : H2} (hu : u ∈ sites37) (hv : v ∈ sites37) :
    ∃ g ∈ Delta237, g u = v ∧ g '' sites37 = sites37 ∧
      ∀ a b c, detH (g a) (g b) (g c) = detH a b c := by
  rcases exists_direct_siteFrame_sites37 hu with ⟨Fu, hFu_mem, hFu_det⟩
  rcases exists_direct_siteFrame_sites37 hv with ⟨Fv, hFv_mem, hFv_det⟩
  refine ⟨Fu.φ.symm.trans Fv.φ, ?_, ?_, ?_, ?_⟩
  · change Fv.φ * Fu.φ⁻¹ ∈ Delta237
    exact Delta237.mul_mem hFv_mem (Delta237.inv_mem hFu_mem)
  · simp only [IsometryEquiv.trans_apply]
    rw [Fu.φ.symm_apply_eq.mpr Fu.origin_eq.symm, Fv.origin_eq]
  · exact delta237_preserves_sites37 (by
      change Fv.φ * Fu.φ⁻¹ ∈ Delta237
      exact Delta237.mul_mem hFv_mem (Delta237.inv_mem hFu_mem))
  · intro a b c
    have hinv : ∀ p q r, detH (Fu.φ.symm p) (Fu.φ.symm q) (Fu.φ.symm r) = detH p q r := by
      intro p q r
      have := hFu_det (Fu.φ.symm p) (Fu.φ.symm q) (Fu.φ.symm r)
      simpa using this.symm
    simp only [IsometryEquiv.trans_apply, hFv_det, hinv]

/-- **Flag transitivity on `sites37`**: for any adjacent pair `u, w ∈ sites37`, there is `g ∈ Delta237`
    with `g origin = u` and `g (polarOrigin (2*r7) 0) = w`. -/
theorem exists_delta237_origin_edge {u w : H2} (hu : u ∈ sites37) (hw : w ∈ sites37) (hadj : Adj37 u w) :
    ∃ g ∈ Delta237, g origin = u ∧ g (polarOrigin (2 * r7) 0) = w := by
  rcases exists_direct_siteFrame_sites37 hu with ⟨Fu, hFu_mem, _⟩
  rcases (Fu.nbr_iff w hw).mp hadj with ⟨k, rfl⟩
  refine ⟨(rot7 ^ (k.1 : ℤ)).trans Fu.φ, ?_, ?_, ?_⟩
  · change Fu.φ * rot7 ^ (k.1 : ℤ) ∈ Delta237
    exact Delta237.mul_mem hFu_mem (Delta237.zpow_mem rot7_mem _)
  · simp only [IsometryEquiv.trans_apply]
    rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
    simp [polarOrigin_zero, Fu.origin_eq]
  · simp only [IsometryEquiv.trans_apply, rot7_zpow_apply_polarOrigin, zero_add, Int.cast_natCast]

/-- **Global Edge-Rigidity of `sites37`**: ANY isometry mapping an adjacent pair of `sites37`
    into `sites37` maps `sites37` bijectively onto `sites37`! -/
theorem isometry_preserves_sites37_of_edge {φ : H2 ≃ᵢ H2} {u w : H2}
    (hu : u ∈ sites37) (hw : w ∈ sites37) (hadj : Adj37 u w)
    (hφu : φ u ∈ sites37) (hφw : φ w ∈ sites37) :
    φ '' sites37 = sites37 := by
  have hfwd : ∀ (ψ : H2 ≃ᵢ H2) {a b : H2}, a ∈ sites37 → b ∈ sites37 → Adj37 a b →
      ψ a ∈ sites37 → ψ b ∈ sites37 → ∀ x ∈ sites37, ψ x ∈ sites37 := by
    intro ψ a b ha hb hab hψa hψb x hx
    rcases exists_delta237_origin_edge ha hb hab with ⟨g, hg, hgo, hg1⟩
    rw [← V_all_eq_sites37] at hψa hψb hx ⊢
    have h0 : (g.trans ψ) origin ∈ V_all := by simpa [hgo] using hψa
    have h1 : (g.trans ψ) (polarOrigin (2 * r7) 0) ∈ V_all := by simpa [hg1] using hψb
    have hgx : g⁻¹ x ∈ V_all := by
      rw [← delta237_preserves_V_all (Delta237.inv_mem hg)]
      exact ⟨x, hx, rfl⟩
    have hres := isometry_maps_V_all_of_origin_edge h0 h1 (g⁻¹ x) hgx
    simpa using hres
  have h1 := hfwd φ hu hw hadj hφu hφw
  have hadj' : Adj37 (φ u) (φ w) := by unfold Adj37 at *; rw [φ.dist_eq]; exact hadj
  have h2 := hfwd φ.symm hφu hφw hadj' (by simpa using hu) (by simpa using hw)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact h1 x hx
  · intro hy; exact ⟨φ.symm y, h2 y hy, by simp⟩

/-! ### Section 5: Exact Graph Distance `Zone` and **Lemma 5.1** -/

/-- Layer index of a site relative to `origin`: `0` for `origin`, `m ≥ 1` for `v ∈ zoneVerts m`. -/
def layerOf (v : H2) : ℕ :=
  if h : ∃ m : ℕ, 1 ≤ m ∧ v ∈ zoneVerts m then Classical.choose h else 0

lemma layerOf_origin : layerOf origin = 0 := by
  unfold layerOf
  split_ifs with h
  · rcases h with ⟨m, _, hm⟩; exact absurd hm (origin_not_mem_zoneVerts m)
  · rfl

lemma layerOf_eq_of_mem_zoneVerts {m : ℕ} (hm : 1 ≤ m) {v : H2} (hv : v ∈ zoneVerts m) :
    layerOf v = m := by
  have hex : ∃ n : ℕ, 1 ≤ n ∧ v ∈ zoneVerts n := ⟨m, hm, hv⟩
  unfold layerOf
  split_ifs
  have hspec := Classical.choose_spec hex
  set n := Classical.choose hex
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact zoneVerts_disjoint hspec.1 hm hlt hspec.2 hv
  · exact zoneVerts_disjoint hm hspec.1 hgt hv hspec.2

/-- Every edge of `graph37` changes `layerOf` by at most `1`. -/
lemma layerOf_adj_le {u v : H2} (hu : u ∈ sites37) (hv : v ∈ sites37) (hadj : Adj37 u v) :
    layerOf v ≤ layerOf u + 1 := by
  rw [← V_all_eq_sites37] at hu hv
  rcases hu with rfl | hu
  · rw [layerOf_origin]
    let F0 := mkSiteFrameOfPacking isPacking_V_all (IsometryEquiv.refl H2) rfl (fun k => by
      have h1 := zoneLayer1_layerVert k.1
      rw [← h1]
      exact mem_V_all_of_mem_zoneVerts (m := 1) (by omega) (layerVert_mem_zoneVerts 1 (by omega) k.1))
    rcases (F0.nbr_iff v hv).mp hadj with ⟨k, rfl⟩
    have hv1 : polarOrigin (2 * r7) ((k.1 : ℝ) * α7) ∈ zoneVerts 1 := by
      rw [← zoneLayer1_layerVert k.1]; exact layerVert_mem_zoneVerts 1 (by omega) k.1
    change layerOf (polarOrigin (2 * r7) ((k.1 : ℝ) * α7)) ≤ 0 + 1
    rw [layerOf_eq_of_mem_zoneVerts (by omega) hv1]
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hu
    rcases hu with ⟨m, hm, hum⟩
    rw [layerOf_eq_of_mem_zoneVerts hm hum]
    simp only [zoneVerts, List.mem_map] at hum
    rcases hum with ⟨e, heL, rfl⟩
    rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
    have h7 := zoneLayer_all_seven_nbrs hm k
    let Fk := mkSiteFrameOfPacking isPacking_V_all ((zoneLayer m).get k).2 rfl (fun j => by
      by_cases hj0 : j.1 = 0
      · rw [hj0]; simp only [Nat.cast_zero, zero_mul, h7.1]
        exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm (k.1 + 1))
      · by_cases hji : j.1 ≤ ((zoneLayer m).get k).1.innerCount
        · have h := h7.2.1 j (by omega) hji
          split_ifs at h with hm1
          · rw [Set.mem_singleton_iff] at h; rw [h]; exact Or.inl rfl
          · exact mem_V_all_of_mem_zoneVerts (by omega) h
        · by_cases hjprev : j.1 = ((zoneLayer m).get k).1.innerCount + 1
          · rw [hjprev, h7.2.2.1]; exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm _)
          · exact mem_V_all_of_mem_zoneVerts (by omega) (h7.2.2.2 j (by omega)))
    rcases (Fk.nbr_iff v hv).mp hadj with ⟨j, rfl⟩
    change layerOf (((zoneLayer m).get k).2 (polarOrigin (2 * r7) ((j.1 : ℝ) * α7))) ≤ m + 1
    by_cases hj0 : j.1 = 0
    · rw [hj0]; simp only [Nat.cast_zero, zero_mul, h7.1]
      rw [layerOf_eq_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm (k.1 + 1))]; omega
    · by_cases hji : j.1 ≤ ((zoneLayer m).get k).1.innerCount
      · have h := h7.2.1 j (by omega) hji
        split_ifs at h with hm1
        · rw [Set.mem_singleton_iff] at h; rw [h, layerOf_origin]; omega
        · rw [layerOf_eq_of_mem_zoneVerts (by omega) h]; omega
      · by_cases hjprev : j.1 = ((zoneLayer m).get k).1.innerCount + 1
        · rw [hjprev, h7.2.2.1]
          rw [layerOf_eq_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm _)]; omega
        · rw [layerOf_eq_of_mem_zoneVerts (by omega) (h7.2.2.2 j (by omega))]

/-- Any walk from `u` to `v` in `graph37` satisfies `layerOf v ≤ layerOf u + p.length`. -/
lemma layerOf_le_add_walk_length {u v : sites37} (p : graph37.Walk u v) :
    layerOf v.1 ≤ layerOf u.1 + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hadj p' ih =>
    have hstep : layerOf b.1 ≤ layerOf a.1 + 1 := layerOf_adj_le a.2 b.2 hadj
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- Every `v ∈ zoneVerts m` (`m ≥ 1`) has a walk of length `m` in `graph37` from `origin`. -/
lemma exists_walk_of_mem_zoneVerts :
    ∀ (m : ℕ), 1 ≤ m → ∀ (v : H2) (_hv : v ∈ zoneVerts m),
      ∃ (hvs : v ∈ sites37) (p : graph37.Walk ⟨v, hvs⟩ ⟨origin, origin_mem_sites37⟩), p.length = m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro v hv
    have hvs : v ∈ sites37 := by rw [← V_all_eq_sites37]; exact mem_V_all_of_mem_zoneVerts (by omega) hv
    have hadj : graph37.Adj ⟨v, hvs⟩ ⟨origin, origin_mem_sites37⟩ := by
      change Adj37 v origin
      simp only [zoneVerts, List.mem_map] at hv
      rcases hv with ⟨e, heL, rfl⟩
      rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
      rw [zoneLayer1_get_origin i]
      unfold Adj37; rw [dist_polarOrigin_origin (2 * r7) _ (by linarith [r7_pos])]
    exact ⟨hvs, SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, rfl⟩
  | succ k hk ih =>
    intro v hv
    have hvs : v ∈ sites37 := by rw [← V_all_eq_sites37]; exact mem_V_all_of_mem_zoneVerts (by omega) hv
    simp only [zoneVerts, List.mem_map] at hv
    rcases hv with ⟨e, heL, rfl⟩
    rcases List.mem_iff_get.mp heL with ⟨i, rfl⟩
    have hinner := (zoneLayer_inner_nbrs (m := k + 1) (by omega) i).1
    have hne1 : k + 1 ≠ 1 := by omega
    simp only [hne1, ite_false, Nat.add_sub_cancel, Set.mem_ofPred_eq] at hinner
    rcases ih _ hinner with ⟨hps, p, hplen⟩
    have hadj : graph37.Adj ⟨((zoneLayer (k + 1)).get i).2 origin, hvs⟩
        ⟨((zoneLayer (k + 1)).get i).2 (polarOrigin (2 * r7) α7), hps⟩ := by
      change Adj37 _ _
      unfold Adj37
      rw [((zoneLayer (k + 1)).get i).2.dist_eq, dist_origin_polarOrigin (2 * r7) _ (by linarith [r7_pos])]
    exact ⟨hvs, SimpleGraph.Walk.cons hadj p, by simp [hplen]⟩

/-- Exact `edist` in `graph37` from `origin` equals `layerOf`! -/
theorem graph37_edist_origin (v : sites37) :
    graph37.edist v ⟨origin, origin_mem_sites37⟩ = (layerOf v.1 : ENat) := by
  have hge : (layerOf v.1 : ENat) ≤ graph37.edist v ⟨origin, origin_mem_sites37⟩ := by
    rw [SimpleGraph.edist_comm]
    by_cases htop : graph37.edist ⟨origin, origin_mem_sites37⟩ v = ⊤
    · rw [htop]; exact le_top
    · rcases SimpleGraph.exists_walk_of_edist_ne_top htop with ⟨p, hp⟩
      rw [← hp]
      have h := layerOf_le_add_walk_length p
      rw [layerOf_origin, zero_add] at h
      exact_mod_cast h
  have hle : graph37.edist v ⟨origin, origin_mem_sites37⟩ ≤ (layerOf v.1 : ENat) := by
    have hvV : v.1 ∈ V_all := V_all_eq_sites37.symm ▸ v.2
    rcases hvV with hvo | hvm
    · have hveq : v = ⟨origin, origin_mem_sites37⟩ := Subtype.ext hvo
      rw [hveq, SimpleGraph.edist_self]; exact zero_le
    · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hvm
      rcases hvm with ⟨m, hm, hvm⟩
      rw [layerOf_eq_of_mem_zoneVerts hm hvm]
      rcases exists_walk_of_mem_zoneVerts m hm v.1 hvm with ⟨_, p, hplen⟩
      have h1 := SimpleGraph.edist_le p
      simpa [hplen] using h1
  exact le_antisymm hle hge

/-- Exact characterization of `Zone ⟨origin, _⟩ m`: `{origin}` for `m = 0`, `zoneVerts m` for `m ≥ 1`! -/
theorem zone_origin_eq_zoneVerts (m : ℕ) (hm : 1 ≤ m) :
    Zone ⟨origin, origin_mem_sites37⟩ m = {x | x ∈ zoneVerts m} := by
  ext x
  simp only [Zone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxs, hed⟩
    rw [graph37_edist_origin ⟨x, hxs⟩] at hed
    have hlay : layerOf x = m := Nat.cast_injective hed
    have hxV : x ∈ V_all := V_all_eq_sites37.symm ▸ hxs
    rcases hxV with rfl | hxm
    · rw [layerOf_origin] at hlay; omega
    · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hxm
      rcases hxm with ⟨n, hn, hxn⟩
      have hn_eq : n = m := by rw [layerOf_eq_of_mem_zoneVerts hn hxn] at hlay; exact hlay
      rwa [← hn_eq]
  · intro hxm
    have hxs : x ∈ sites37 := V_all_eq_sites37 ▸ mem_V_all_of_mem_zoneVerts hm hxm
    refine ⟨hxs, ?_⟩
    rw [graph37_edist_origin ⟨x, hxs⟩, layerOf_eq_of_mem_zoneVerts hm hxm]

theorem zone_origin_zero : Zone ⟨origin, origin_mem_sites37⟩ 0 = {origin} := by
  ext x
  simp only [Zone, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxs, hed⟩
    rw [graph37_edist_origin ⟨x, hxs⟩] at hed
    have hlay : layerOf x = 0 := Nat.cast_injective hed
    have hxV : x ∈ V_all := V_all_eq_sites37.symm ▸ hxs
    rcases hxV with rfl | hxm
    · rfl
    · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hxm
      rcases hxm with ⟨n, hn, hxn⟩
      rw [layerOf_eq_of_mem_zoneVerts hn hxn] at hlay; omega
  · rintro rfl
    exact ⟨origin_mem_sites37, by rw [graph37_edist_origin, layerOf_origin]⟩

lemma graph37_iso_edist (iso : graph37 ≃g graph37) (a b : sites37) :
    graph37.edist (iso a) (iso b) = graph37.edist a b := by
  have hle : ∀ (f : graph37 ≃g graph37) (u v : sites37),
      graph37.edist (f u) (f v) ≤ graph37.edist u v := by
    intro f u v
    by_cases htop : graph37.edist u v = ⊤
    · rw [htop]; exact le_top
    · rcases SimpleGraph.exists_walk_of_edist_ne_top htop with ⟨p, hp⟩
      rw [← hp]
      have h1 := SimpleGraph.edist_le (p.map f.toHom)
      simpa using h1
  apply le_antisymm (hle iso a b)
  have h2 := hle iso.symm (iso a) (iso b)
  simpa using h2

lemma delta237_apply_mem {g : H2 ≃ᵢ H2} (hg : g ∈ Delta237) {x : H2} (hx : x ∈ sites37) :
    g x ∈ sites37 := by
  rw [← delta237_preserves_sites37 hg]; exact ⟨x, hx, rfl⟩

/-- Any `g ∈ Delta237` transports `Zone` by `g '' Zone c₀ m = Zone ⟨g c₀, _⟩ m`! -/
lemma zone_image_delta237 {g : H2 ≃ᵢ H2} (hg : g ∈ Delta237) (c₀ : sites37) (m : ℕ) :
    g '' Zone c₀ m = Zone ⟨g c₀.1, delta237_apply_mem hg c₀.2⟩ m := by
  have hg_mem : ∀ x : sites37, g x.1 ∈ sites37 := fun x => delta237_apply_mem hg x.2
  have hginv_mem : ∀ x : sites37, g.symm x.1 ∈ sites37 := fun x =>
    delta237_apply_mem (Delta237.inv_mem hg) x.2
  let iso : graph37 ≃g graph37 :=
    { toFun := fun x => ⟨g x.1, hg_mem x⟩
      invFun := fun x => ⟨g.symm x.1, hginv_mem x⟩
      left_inv := fun x => Subtype.ext (g.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (g.apply_symm_apply x.1)
      map_rel_iff' := by
        intro a b
        change Adj37 (g a.1) (g b.1) ↔ Adj37 a.1 b.1
        unfold Adj37; rw [g.dist_eq] }
  ext y
  simp only [Set.mem_image, Zone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxs, hed⟩, rfl⟩
    refine ⟨hg_mem ⟨x, hxs⟩, ?_⟩
    have := graph37_iso_edist iso ⟨x, hxs⟩ c₀
    simpa [iso] using this.trans hed
  · rintro ⟨hys, hed⟩
    refine ⟨g.symm y, ⟨hginv_mem ⟨y, hys⟩, ?_⟩, g.apply_symm_apply y⟩
    have := graph37_iso_edist iso ⟨g.symm y, hginv_mem ⟨y, hys⟩⟩ c₀
    have heq : iso ⟨g.symm y, hginv_mem ⟨y, hys⟩⟩ = ⟨y, hys⟩ := Subtype.ext (g.apply_symm_apply y)
    rw [heq] at this
    exact this.symm.trans hed

/-- **Lemma 5.1 (Full geometric + combinatorial Zone Substitution Lemma, incl. convex polygon `P_m`)**! -/
theorem lem_5_1_zone_substitution_geom (c₀ : sites37) (m : ℕ) (hm : 1 ≤ m) :
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
        let i : ℕ := match (zoneWord m).get (k.cast hlen) with | .t1 => 1 | .t2 => 2
        ∃ F : SiteFrame sites37 v,
          F.nbr 0 = vPrev ∧
          (∀ j : Fin 7, 1 ≤ j.1 → j.1 ≤ i → F.nbr j ∈ Zone c₀ (m - 1)) ∧
          F.nbr (i + 1 : ℕ) = vNext ∧
          (∀ j : Fin 7, i + 2 ≤ j.1 → F.nbr j ∈ Zone c₀ (m + 1))) ∧
      (∀ (k : Fin cyc.length), ∀ x ∈ ZoneUnion c₀ m ∪ {c₀.1},
        0 ≤ detH (cyc.get k)
          (cyc.get ⟨(k.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩) x) := by
  rcases delta237_direct_transitive origin_mem_sites37 c₀.2 with ⟨g, hg_mem, hgo, hg_pres, hg_det⟩
  set cyc := (zoneVerts m).map g
  have hcyc_nodup : cyc.Nodup := (zoneVerts_nodup m).map g.injective
  have hcyc_len : cyc.length = (zoneWord m).length := by
    simp [cyc, zoneVerts_length, zoneLayer_length]
  have hzone_eq : ∀ n, g '' Zone ⟨origin, origin_mem_sites37⟩ n = Zone c₀ n := by
    intro n
    have h1 := zone_image_delta237 hg_mem ⟨origin, origin_mem_sites37⟩ n
    have hc : (⟨g origin, delta237_apply_mem hg_mem origin_mem_sites37⟩ : sites37) = c₀ :=
      Subtype.ext hgo
    simpa [hc] using h1
  have hset_eq : ({x | x ∈ cyc} : Set H2) = Zone c₀ m := by
    rw [← hzone_eq m, zone_origin_eq_zoneVerts m hm]
    ext y; simp [cyc]
  have hL := zoneLayer_length_pos m hm
  have hcyc_len_eq : cyc.length = (zoneLayer m).length := by simp [cyc, zoneVerts_length]
  have hget_cyc : ∀ idx : ℕ, (hidx : idx < cyc.length) →
      cyc.get ⟨idx, hidx⟩ = g (layerVert (zoneLayer m) hL idx) := by
    intro idx hidx
    have hlt' : idx < (zoneLayer m).length := by omega
    rw [List.get_eq_getElem]
    simp only [cyc, zoneVerts, List.getElem_map, layerVert, List.get_eq_getElem, Nat.mod_eq_of_lt hlt']
  refine ⟨cyc, hcyc_nodup, hcyc_len, hset_eq, ?_, ?_⟩
  · intro k
    have hk_lt : k.1 < (zoneLayer m).length := by omega
    let kf : Fin (zoneLayer m).length := ⟨k.1, hk_lt⟩
    have htype_eq : (zoneWord m).get (k.cast hcyc_len) = ((zoneLayer m).get kf).1 := by
      have hty := zoneLayer_types m
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [Fin.val_cast]
      have hlen_map : k.1 < ((zoneLayer m).map Prod.fst).length :=
        lt_of_lt_of_eq hk_lt (List.length_map Prod.fst).symm
      have h1 : (zoneWord m)[k.1]'(lt_of_lt_of_eq k.2 hcyc_len) =
          ((zoneLayer m).map Prod.fst)[k.1]'hlen_map := by
        simp only [hty]
      rw [h1, List.getElem_map]
    have hi_eq : (match (zoneWord m).get (k.cast hcyc_len) with | .t1 => 1 | .t2 => 2) =
        ((zoneLayer m).get kf).1.innerCount := by
      rw [htype_eq]; cases ((zoneLayer m).get kf).1 <;> rfl
    have h7 := zoneLayer_all_seven_nbrs hm kf
    have hv_eq : cyc.get k = g (((zoneLayer m).get kf).2 origin) := by
      rw [hget_cyc k.1 k.2]
      unfold layerVert
      have hfin : (⟨k.1 % (zoneLayer m).length, Nat.mod_lt _ hL⟩ : Fin (zoneLayer m).length) = kf :=
        Fin.ext (Nat.mod_eq_of_lt hk_lt)
      exact congrArg (fun x => g (((zoneLayer m).get x).2 origin)) hfin
    set ic : ℕ := ((zoneLayer m).get kf).1.innerCount
    let R : H2 ≃ᵢ H2 := reflRay (((ic + 1 : ℕ) : ℝ) * α7 / 2)
    let Fφ : H2 ≃ᵢ H2 := R.trans (((zoneLayer m).get kf).2.trans g)
    have hR_pol : ∀ θ : ℝ, R (polarOrigin (2 * r7) θ) =
        polarOrigin (2 * r7) (((ic + 1 : ℕ) : ℝ) * α7 - θ) := by
      intro θ
      simp only [R, reflRay, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin, reflXAxis_apply_polarOrigin]
      congr 1; ring
    have hR_o : R origin = origin := by
      simp [R, reflRay, rotOrigin_apply_origin, reflXAxis_apply_origin]
    have hF_o : Fφ origin = cyc.get k := by
      simp only [Fφ, IsometryEquiv.trans_apply, hR_o, hv_eq]
    have hF_mem : ∀ j : Fin 7, Fφ (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈ sites37 := by
      intro j
      simp only [Fφ, IsometryEquiv.trans_apply, hR_pol]
      rw [← hg_pres]
      refine ⟨((zoneLayer m).get kf).2 (polarOrigin (2 * r7) (((ic + 1 : ℕ) : ℝ) * α7 - (j.1 : ℝ) * α7)), ?_, rfl⟩
      rw [← V_all_eq_sites37]
      have hsub_int : ((ic + 1 : ℕ) : ℝ) * α7 - (j.1 : ℝ) * α7 =
          ((((ic + 1 : ℕ) : ℤ) - (j.1 : ℤ) : ℤ) : ℝ) * α7 := by push_cast; ring
      rw [hsub_int]
      rcases exists_fin7_polarOrigin_int (((ic + 1 : ℕ) : ℤ) - (j.1 : ℤ)) with ⟨j', hj'⟩
      rw [hj']
      by_cases hj0 : j'.1 = 0
      · rw [hj0]; simp only [Nat.cast_zero, zero_mul, h7.1]
        exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm (kf.1 + 1))
      · by_cases hji : j'.1 ≤ ((zoneLayer m).get kf).1.innerCount
        · have h := h7.2.1 j' (by omega) hji
          split_ifs at h with hm1
          · rw [Set.mem_singleton_iff] at h; rw [h]; exact Or.inl rfl
          · exact mem_V_all_of_mem_zoneVerts (by omega) h
        · by_cases hjprev : j'.1 = ((zoneLayer m).get kf).1.innerCount + 1
          · rw [hjprev, h7.2.2.1]; exact mem_V_all_of_mem_zoneVerts hm (layerVert_mem_zoneVerts m hm _)
          · exact mem_V_all_of_mem_zoneVerts (by omega) (h7.2.2.2 j' (by omega))
    let F : SiteFrame sites37 (cyc.get k) := mkSiteFrameOfPacking isPacking_sites37 Fφ hF_o hF_mem
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · -- F.nbr 0 = vPrev
      change g (((zoneLayer m).get kf).2 (R (polarOrigin (2 * r7) (((0 : ℤ) : ℝ) * α7)))) = _
      simp only [Int.cast_zero, zero_mul, hR_pol, sub_zero]
      rw [h7.2.2.1, hget_cyc ((k.1 + cyc.length - 1) % cyc.length) (Nat.mod_lt _ (Nat.zero_lt_of_lt k.2))]
      congr 1; unfold layerVert
      have hfin : (⟨(kf.1 + (zoneLayer m).length - 1) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ : Fin (zoneLayer m).length) =
          ⟨((k.1 + cyc.length - 1) % cyc.length) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ :=
        Fin.ext (by simp [kf, hcyc_len_eq])
      exact congrArg (fun x => ((zoneLayer m).get x).2 origin) hfin
    · -- 1 ≤ j ≤ i → F.nbr j ∈ Zone c₀ (m - 1)
      intro j hj1 hji
      rw [hi_eq] at hji
      have hic_le : ic ≤ 2 := by dsimp only [ic]; cases ((zoneLayer m).get kf).1 <;> decide
      have hsub_lt : ic + 1 - j.1 < 7 := by omega
      let j' : Fin 7 := ⟨ic + 1 - j.1, hsub_lt⟩
      have harg : ((ic + 1 : ℕ) : ℝ) * α7 - (j.1 : ℝ) * α7 = (j'.1 : ℝ) * α7 := by
        have hsub : ((ic + 1 - j.1 : ℕ) : ℝ) = ((ic + 1 : ℕ) : ℝ) - (j.1 : ℝ) :=
          Nat.cast_sub (by omega)
        simp only [j', hsub]; ring
      change g (((zoneLayer m).get kf).2 (R (polarOrigin (2 * r7) (((j.1 : ℤ) : ℝ) * α7)))) ∈ Zone c₀ (m - 1)
      rw [Int.cast_natCast, hR_pol, harg, ← hzone_eq (m - 1)]
      refine ⟨_, ?_, rfl⟩
      have h := h7.2.1 j' (by simp only [j']; omega) (by simp only [j']; omega)
      split_ifs at h with hm1
      · subst hm1; simpa [zone_origin_zero] using h
      · rw [zone_origin_eq_zoneVerts (m - 1) (by omega)]; exact h
    · -- F.nbr (i + 1) = vNext
      rw [hi_eq]
      change g (((zoneLayer m).get kf).2 (R (polarOrigin (2 * r7) ((((ic + 1 : ℕ) : ℤ) : ℝ) * α7)))) = _
      rw [Int.cast_natCast, hR_pol, sub_self, h7.1]
      rw [hget_cyc ((k.1 + 1) % cyc.length) (Nat.mod_lt _ (Nat.zero_lt_of_lt k.2))]
      congr 1; unfold layerVert
      have hfin : (⟨(kf.1 + 1) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ : Fin (zoneLayer m).length) =
          ⟨((k.1 + 1) % cyc.length) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ :=
        Fin.ext (by simp [kf, hcyc_len_eq])
      exact congrArg (fun x => ((zoneLayer m).get x).2 origin) hfin
    · -- i + 2 ≤ j → F.nbr j ∈ Zone c₀ (m + 1)
      intro j hj
      rw [hi_eq] at hj
      have hic_le : ic ≤ 2 := by dsimp only [ic]; cases ((zoneLayer m).get kf).1 <;> decide
      have hval_lt : 7 + ic + 1 - j.1 < 7 := by omega
      let j' : Fin 7 := ⟨7 + ic + 1 - j.1, hval_lt⟩
      have harg : ((ic + 1 : ℕ) : ℝ) * α7 - (j.1 : ℝ) * α7 + 2 * Real.pi = (j'.1 : ℝ) * α7 := by
        have hsub : ((7 + ic + 1 - j.1 : ℕ) : ℝ) =
            7 + ((ic + 1 : ℕ) : ℝ) - (j.1 : ℝ) := by
          have := Nat.cast_sub (R := ℝ) (show j.1 ≤ 7 + ic + 1 by omega)
          push_cast at this ⊢; linarith
        have h7a : 7 * α7 = 2 * Real.pi := by unfold α7 alphaP; ring
        simp only [j', hsub]; linarith
      change g (((zoneLayer m).get kf).2 (R (polarOrigin (2 * r7) (((j.1 : ℤ) : ℝ) * α7)))) ∈ Zone c₀ (m + 1)
      rw [Int.cast_natCast, hR_pol, ← polarOrigin_add_two_pi, harg, ← hzone_eq (m + 1),
        zone_origin_eq_zoneVerts (m + 1) (by omega)]
      refine ⟨_, ?_, rfl⟩
      exact h7.2.2.2 j' (by simp only [j']; omega)
  · -- Convex polygon P_m property: ∀ k, ∀ x ∈ ZoneUnion c₀ m ∪ {c₀.1}, 0 ≤ detH cyc[k] cyc[k+1] x!
    intro k x hx
    have hxk : cyc.get k = g (layerVert (zoneLayer m) hL k.1) := hget_cyc k.1 k.2
    have hxk1 : cyc.get ⟨(k.1 + 1) % cyc.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩ =
        g (layerVert (zoneLayer m) hL (k.1 + 1)) := by
      rw [hget_cyc _ (Nat.mod_lt _ (Nat.zero_lt_of_lt k.2))]
      congr 1; unfold layerVert
      have hfin : (⟨((k.1 + 1) % cyc.length) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ : Fin (zoneLayer m).length) =
          ⟨(k.1 + 1) % (zoneLayer m).length, Nat.mod_lt _ hL⟩ :=
        Fin.ext (by simp [hcyc_len_eq])
      exact congrArg (fun x => ((zoneLayer m).get x).2 origin) hfin
    have hx_pre : g.symm x ∈ V_upto m := by
      rcases hx with hxU | hxo
      · simp only [ZoneUnion, Set.mem_iUnion, Finset.mem_Icc] at hxU
        rcases hxU with ⟨r, ⟨hr1, hrm⟩, hxr⟩
        rw [← hzone_eq r, zone_origin_eq_zoneVerts r hr1] at hxr
        rcases hxr with ⟨x0, hx0, rfl⟩
        rw [g.symm_apply_apply]
        exact mem_V_upto_of_mem_zoneVerts hr1 hrm hx0
      · rw [Set.mem_singleton_iff] at hxo
        rw [hxo, ← hgo, g.symm_apply_apply]
        exact Or.inl rfl
    have hpoly : g.symm x ∈ ClosedPoly m hm := V_upto_subset_closedPoly hm hx_pre
    rw [hxk, hxk1, ← g.apply_symm_apply x, hg_det]
    exact hpoly k.1

/-! ### Section 6: Far-Away Cofinite Rigidity, **Lemma 2.1**, and Covering Radius `Rc7` -/

/-- Outside any finite set `K`, there exists an adjacent pair of sites in `sites37`! -/
theorem exists_adj_pair_outside_finset (K : Finset H2) :
    ∃ u ∈ sites37, ∃ w ∈ sites37, u ∉ K ∧ w ∉ K ∧ Adj37 u w := by
  let M : ℕ := K.sup layerOf + 1
  have hM : 1 ≤ M := by omega
  set hL := zoneLayer_length_pos M hM
  set u := layerVert (zoneLayer M) hL 0
  set w := layerVert (zoneLayer M) hL 1
  have hu_z : u ∈ zoneVerts M := layerVert_mem_zoneVerts M hM 0
  have hw_z : w ∈ zoneVerts M := layerVert_mem_zoneVerts M hM 1
  have hu_s : u ∈ sites37 := V_all_eq_sites37 ▸ mem_V_all_of_mem_zoneVerts hM hu_z
  have hw_s : w ∈ sites37 := V_all_eq_sites37 ▸ mem_V_all_of_mem_zoneVerts hM hw_z
  have hu_not : u ∉ K := by
    intro hmem
    have hle := Finset.le_sup (f := layerOf) hmem
    rw [layerOf_eq_of_mem_zoneVerts hM hu_z] at hle
    omega
  have hw_not : w ∉ K := by
    intro hmem
    have hle := Finset.le_sup (f := layerOf) hmem
    rw [layerOf_eq_of_mem_zoneVerts hM hw_z] at hle
    omega
  have hadj : Adj37 u w := by
    have hAdj := zoneLayer_cyclicAdj M hM
    have ha := hAdj.2 ⟨0, hAdj.1⟩
    have h1 := adjFrame_origin_eq ha
    have hw_eq : w = ((zoneLayer M).get ⟨0, hAdj.1⟩).2 (polarOrigin (2 * r7) 0) := by
      simpa [w, layerVert] using h1
    have hu_eq : u = ((zoneLayer M).get ⟨0, hAdj.1⟩).2 origin := by
      simp [u, layerVert]
    unfold Adj37
    rw [hu_eq, hw_eq, ((zoneLayer M).get ⟨0, hAdj.1⟩).2.dist_eq,
      dist_origin_polarOrigin (2 * r7) 0 (by linarith [r7_pos])]
  exact ⟨u, hu_s, w, hw_s, hu_not, hw_not, hadj⟩

/-- **Cofinite Rigidity of `sites37`**: if `φ` maps `sites37 \ K` (for finite `K`) into `sites37`,
    then `φ '' sites37 = sites37`! -/
theorem isometry_preserves_sites37_of_cofinite {φ : H2 ≃ᵢ H2} (K : Finset H2)
    (hsub : φ '' (sites37 \ (K : Set H2)) ⊆ sites37) :
    φ '' sites37 = sites37 := by
  rcases exists_adj_pair_outside_finset K with ⟨u, hu, w, hw, huK, hwK, hadj⟩
  have hφu : φ u ∈ sites37 := hsub ⟨u, ⟨hu, huK⟩, rfl⟩
  have hφw : φ w ∈ sites37 := hsub ⟨w, ⟨hw, hwK⟩, rfl⟩
  exact isometry_preserves_sites37_of_edge hu hw hadj hφu hφw

/-- **Lemma 2.1**: A rearrangement `X` of a finite subset `s ⊆ oneVacancy c₀` is trivial iff `X ⊆ sites37`. -/
theorem lem_2_1_trivial_rearrangement (c₀ : H2) (hc₀ : c₀ ∈ sites37)
    (s X : Finset H2) (hX : IsRearrangement r7 (oneVacancy c₀) s X) :
    IsTrivialRearrangement (oneVacancy c₀) s X ↔ (X : Set H2) ⊆ sites37 := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hK : φ '' (sites37 \ (insert c₀ s : Finset H2)) ⊆ sites37 := by
      rintro y ⟨x, ⟨hxs, hxK⟩, rfl⟩
      have hx_in : x ∈ (oneVacancy c₀ \ (s : Set H2)) ∪ (X : Set H2) := by
        left
        refine ⟨⟨hxs, ?_⟩, ?_⟩
        · intro hxc; rw [Set.mem_singleton_iff] at hxc; exact hxK (by simp [hxc])
        · intro hxs'; exact hxK (by simp [hxs'])
      have h1 : φ x ∈ oneVacancy c₀ := by rw [← hφ]; exact ⟨x, hx_in, rfl⟩
      exact h1.1
    have hpres := isometry_preserves_sites37_of_cofinite (insert c₀ s) hK
    intro x hx
    have hφx : φ x ∈ sites37 := by
      have h1 : φ x ∈ oneVacancy c₀ := by rw [← hφ]; exact ⟨x, Or.inr hx, rfl⟩
      exact h1.1
    have hx_mem : x ∈ φ.symm '' sites37 := ⟨φ x, hφx, by simp⟩
    have hsymm : φ.symm '' sites37 = sites37 := by
      ext z; constructor
      · rintro ⟨w, hw, rfl⟩; rw [← hpres] at hw; rcases hw with ⟨a, ha, rfl⟩; simpa using ha
      · intro hz; exact ⟨φ z, by rw [← hpres]; exact ⟨z, hz, rfl⟩, by simp⟩
    rwa [hsymm] at hx_mem
  · intro hX_sites
    rcases hX with ⟨hs_sub, hcard, hdisj, _⟩
    have hc0_not_s : c₀ ∉ s := fun hc => (hs_sub hc).2 rfl
    have hX_sub : X ⊆ insert c₀ s := by
      intro x hx
      by_contra hnot
      have hx_ne : x ≠ c₀ := fun h => hnot (by simp [h])
      have hx_ns : x ∉ s := fun h => hnot (by simp [h])
      have hx_fix : x ∈ oneVacancy c₀ \ (s : Set H2) := ⟨⟨hX_sites hx, hx_ne⟩, hx_ns⟩
      exact Set.disjoint_left.mp hdisj hx_fix hx
    have hdiff_card : (insert c₀ s \ X).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hX_sub, Finset.card_insert_of_notMem hc0_not_s, hcard]
      omega
    rcases Finset.card_eq_one.mp hdiff_card with ⟨c₁, hc1_eq⟩
    have hc1_mem_ins : c₁ ∈ insert c₀ s := by
      have : c₁ ∈ insert c₀ s \ X := by rw [hc1_eq]; exact Finset.mem_singleton_self c₁
      exact (Finset.mem_sdiff.mp this).1
    have hc1_sites : c₁ ∈ sites37 := by
      rcases Finset.mem_insert.mp hc1_mem_ins with rfl | h
      · exact hc₀
      · exact (hs_sub h).1
    have hset_eq : (oneVacancy c₀ \ (s : Set H2)) ∪ (X : Set H2) = oneVacancy c₁ := by
      ext y
      simp only [Set.mem_union, Set.mem_sdiff, oneVacancy, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · rintro (⟨⟨hys, hyc0⟩, hyns⟩ | hyX)
        · refine ⟨hys, ?_⟩
          intro hyc1; subst hyc1
          rcases Finset.mem_insert.mp hc1_mem_ins with rfl | h
          · exact hyc0 rfl
          · exact hyns h
        · refine ⟨hX_sites hyX, ?_⟩
          intro hyc1; subst hyc1
          have : y ∈ insert c₀ s \ X := by rw [hc1_eq]; exact Finset.mem_singleton_self y
          exact (Finset.mem_sdiff.mp this).2 hyX
      · rintro ⟨hys, hyc1⟩
        by_cases hyX : y ∈ X
        · exact Or.inr hyX
        · left
          refine ⟨⟨hys, ?_⟩, ?_⟩
          · intro hyc0
            have : y ∈ insert c₀ s \ X := Finset.mem_sdiff.mpr ⟨by rw [hyc0]; exact Finset.mem_insert_self _ _, hyX⟩
            rw [hc1_eq, Finset.mem_singleton] at this
            exact hyc1 this
          · intro hys'
            have : y ∈ insert c₀ s \ X := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hys', hyX⟩
            rw [hc1_eq, Finset.mem_singleton] at this
            exact hyc1 this
    rcases delta237_direct_transitive hc1_sites hc₀ with ⟨g, _, hgc1, hg_pres, _⟩
    refine ⟨g, ?_⟩
    rw [hset_eq]
    ext y
    simp only [Set.mem_image, oneVacancy, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxs, hxc1⟩, rfl⟩
      refine ⟨by rw [← hg_pres]; exact ⟨x, hxs, rfl⟩, ?_⟩
      intro heq; exact hxc1 (g.injective (heq.trans hgc1.symm))
    · rintro ⟨hys, hyc0⟩
      rw [← hg_pres] at hys
      rcases hys with ⟨x, hxs, rfl⟩
      refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
      intro heq; subst heq; exact hyc0 hgc1

/-! ### Covering Radius `Rc7` via Exponential Growth + Closest Site -/

/-- Exact right-triangle circumradius identity: `(sinh Rc7 / cosh Rc7) * cos (α7 / 2) = sinh r7 / cosh r7`. -/
lemma tanh_Rc7_mul_cos_half_alpha7 :
    (Real.sinh Rc7 / Real.cosh Rc7) * Real.cos (α7 / 2) = Real.sinh r7 / Real.cosh r7 := by
  have hsh_Rc : Real.sinh Rc7 = Real.sinh r7 / Real.sin (Real.pi / 3) := by
    unfold Rc7; exact Real.sinh_arsinh _
  have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hhalf : α7 / 2 = Real.pi / 7 := by unfold α7 alphaP; ring
  rw [hhalf]
  have hchr : Real.cosh r7 = 1 / (2 * Real.sin (Real.pi / 7)) := cosh_r7
  have hsin7_pos : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hcos7_pos : 0 < Real.cos (Real.pi / 7) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hch_Rc_sq : Real.cosh Rc7 ^ 2 = (4 / 3) * Real.cosh r7 ^ 2 * Real.cos (Real.pi / 7) ^ 2 := by
    have h1 := Real.cosh_sq_sub_sinh_sq Rc7
    have h2 := Real.cosh_sq_sub_sinh_sq r7
    have h3 := Real.cos_sq_add_sin_sq (Real.pi / 7)
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsh_sq : Real.sinh Rc7 ^ 2 = (4 / 3) * Real.sinh r7 ^ 2 := by
      rw [hsh_Rc, hsin3, div_pow, div_pow, hsq3]; ring
    have hsin7_sq : Real.cosh r7 ^ 2 * Real.sin (Real.pi / 7) ^ 2 = 1 / 4 := by
      rw [hchr, div_pow]; field_simp [hsin7_pos.ne']; ring
    nlinarith
  have hch_Rc_eq : Real.cosh Rc7 = (2 / Real.sqrt 3) * Real.cosh r7 * Real.cos (Real.pi / 7) := by
    have hsq_rhs : ((2 / Real.sqrt 3) * Real.cosh r7 * Real.cos (Real.pi / 7)) ^ 2 = Real.cosh Rc7 ^ 2 := by
      rw [hch_Rc_sq, mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
    have hrhs_pos : 0 < (2 / Real.sqrt 3) * Real.cosh r7 * Real.cos (Real.pi / 7) :=
      mul_pos (mul_pos (div_pos zero_lt_two (Real.sqrt_pos.mpr (by norm_num))) (Real.cosh_pos r7)) hcos7_pos
    nlinarith [Real.cosh_pos Rc7]
  rw [hsh_Rc, hsin3, hch_Rc_eq]
  have h3ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hchr_ne : Real.cosh r7 ≠ 0 := (Real.cosh_pos r7).ne'
  have hcos_ne : Real.cos (Real.pi / 7) ≠ 0 := hcos7_pos.ne'
  field_simp [h3ne, hchr_ne, hcos_ne]

/-- Every closed ball `Metric.closedBall x R` intersects `sites37` in a finite set! -/
theorem sites37_inter_closedBall_finite (x : H2) (R : ℝ) :
    (sites37 ∩ Metric.closedBall x R).Finite := by
  set B : ℝ := Real.cosh (dist origin x + max R 0)
  have hex_M : ∃ M : ℕ, B < zoneGrowthBase ^ M := by
    have hd_pos : 0 < zoneGrowthBase - 1 := by linarith [zoneGrowthBase_gt_one]
    have hbern : ∀ n : ℕ, 1 + (n : ℝ) * (zoneGrowthBase - 1) ≤ zoneGrowthBase ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ r ih =>
        rw [pow_succ]
        have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        push_cast
        nlinarith [zoneGrowthBase_gt_one, sq_nonneg (zoneGrowthBase - 1), mul_nonneg hr hd_pos.le]
    rcases exists_nat_gt (B / (zoneGrowthBase - 1)) with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    have hBM : B < (M : ℝ) * (zoneGrowthBase - 1) := (div_lt_iff₀ hd_pos).mp hM
    linarith [hbern M]
  obtain ⟨M, hM⟩ := hex_M
  have hsub : sites37 ∩ Metric.closedBall x R ⊆ V_upto M := by
    intro v ⟨hvs, hvR⟩
    have hvV : v ∈ V_all := V_all_eq_sites37.symm ▸ hvs
    rcases hvV with rfl | hvm
    · exact Or.inl rfl
    · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hvm
      rcases hvm with ⟨m, hm, hvm⟩
      by_cases hle : m ≤ M
      · exact mem_V_upto_of_mem_zoneVerts hm hle hvm
      · push Not at hle
        exfalso
        have hdv : dist origin v ≤ dist origin x + max R 0 := by
          have h1 : dist x v ≤ R := by simpa [Metric.mem_closedBall, dist_comm] using hvR
          have htri := dist_triangle origin x v
          linarith [le_max_left R 0]
        have hvz_le : v.z ≤ B := by
          have hl : lorentz origin v = v.z := by unfold lorentz origin; ring
          rw [← hl, ← cosh_dist]
          exact Real.cosh_le_cosh.mpr (by
            rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (add_nonneg dist_nonneg (le_max_right R 0))]
            exact hdv)
        have hvz_ge : zoneGrowthBase ^ m ≤ v.z := by
          simp only [zoneVerts, List.mem_map] at hvm
          rcases hvm with ⟨e, heL, rfl⟩
          rcases List.mem_iff_get.mp heL with ⟨k, rfl⟩
          have hz := (zoneConvexInv m hm).z_ge_pow k.1
          simpa [layerVert, Nat.mod_eq_of_lt k.2] using hz
        have hpow_mono : zoneGrowthBase ^ M ≤ zoneGrowthBase ^ m :=
          pow_le_pow_right₀ zoneGrowthBase_gt_one.le hle.le
        linarith
  have hV_fin : (V_upto M).Finite := by
    unfold V_upto
    apply Set.Finite.union (Set.finite_singleton origin)
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro k _
    exact (zoneVerts k).finite_toSet
  exact hV_fin.subset hsub

/-- Every point `x : H2` has a closest site `v ∈ sites37`! -/
theorem exists_closest_site (x : H2) :
    ∃ v ∈ sites37, ∀ w ∈ sites37, dist x v ≤ dist x w := by
  set S : Set H2 := sites37 ∩ Metric.closedBall x (dist x origin)
  have hfin : S.Finite := sites37_inter_closedBall_finite x (dist x origin)
  have hne : S.Nonempty := ⟨origin, origin_mem_sites37, by simp [Metric.mem_closedBall, dist_comm]⟩
  rcases Finset.exists_min_image hfin.toFinset (fun w => dist x w) (hfin.toFinset_nonempty.mpr hne) with
    ⟨v, hvS', hvmin⟩
  have hvS : v ∈ S := hfin.mem_toFinset.mp hvS'
  refine ⟨v, hvS.1, fun w hw => ?_⟩
  by_cases hwS : w ∈ S
  · exact hvmin w (hfin.mem_toFinset.mpr hwS)
  · have hgt : dist x origin < dist x w := by
      by_contra hle; push Not at hle
      exact hwS ⟨hw, by simpa [Metric.mem_closedBall, dist_comm] using hle⟩
    have hvle : dist x v ≤ dist x origin := by simpa [Metric.mem_closedBall, dist_comm] using hvS.2
    linarith

/-- **Covering Radius `Rc7` & Polar Sector Theorem**:
    Every `x : H2` lies in a fundamental sector `0 ≤ θ ≤ α7 / 2`, `0 ≤ ρ ≤ Rc7` of a `SiteFrame sites37 v`
    around a closest site `v ∈ sites37`! -/
theorem covering_radius_Rc7_sector (x : H2) :
    ∃ v ∈ sites37, ∃ F : SiteFrame sites37 v, ∃ ρ θ : ℝ,
      0 ≤ ρ ∧ ρ ≤ Rc7 ∧ 0 ≤ θ ∧ θ ≤ α7 / 2 ∧ x = F.polar ρ θ := by
  rcases exists_closest_site x with ⟨v, hv, hclosest⟩
  rcases exists_direct_siteFrame_sites37 hv with ⟨F0, _, _⟩
  set q := F0.φ.symm x
  set ρ := dist origin q
  have hρ_nn : 0 ≤ ρ := dist_nonneg
  rcases exists_polarOrigin q with ⟨θ₀, hθ₀⟩
  rcases exists_fin7_angle_close θ₀ with ⟨k, m, hclose⟩
  set δ := θ₀ - ((k.1 : ℝ) * α7 + (m : ℝ) * (2 * Real.pi))
  have hq_rot : polarOrigin ρ θ₀ = (rot7 ^ (k.1 : ℤ)) (polarOrigin ρ δ) := by
    rw [rot7_zpow_apply_polarOrigin, Int.cast_natCast]
    have heq : δ + (k.1 : ℝ) * α7 = θ₀ + ((-(m : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [heq, polarOrigin_add_int_two_pi]
  let R : H2 ≃ᵢ H2 := if 0 ≤ δ then rot7 ^ (k.1 : ℤ) else reflXAxis.trans (rot7 ^ (k.1 : ℤ))
  let Fφ : H2 ≃ᵢ H2 := R.trans F0.φ
  have hR_o : R origin = origin := by
    simp only [R]; split_ifs
    · rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
      simp [polarOrigin_zero]
    · simp only [IsometryEquiv.trans_apply, reflXAxis_apply_origin]
      rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
      simp [polarOrigin_zero]
  have hF_o : Fφ origin = v := by simp [Fφ, hR_o, F0.origin_eq]
  have hF_mem : ∀ j : Fin 7, Fφ (polarOrigin (2 * r7) ((j.1 : ℝ) * α7)) ∈ sites37 := by
    intro j
    have h7 : ∀ n : ℤ, F0.φ (polarOrigin (2 * r7) ((n : ℝ) * α7)) ∈ sites37 := by
      intro n
      rcases exists_fin7_polarOrigin_int n with ⟨r, hr⟩
      rw [hr]; exact F0.nbr_mem r
    simp only [Fφ, R, IsometryEquiv.trans_apply]
    split_ifs
    · rw [rot7_zpow_apply_polarOrigin, Int.cast_natCast]
      have heq : (j.1 : ℝ) * α7 + (k.1 : ℝ) * α7 = ((((j.1 + k.1 : ℕ) : ℤ) : ℝ)) * α7 := by push_cast; ring
      rw [heq]; exact h7 ((j.1 + k.1 : ℕ) : ℤ)
    · simp only [IsometryEquiv.trans_apply, reflXAxis_apply_polarOrigin, rot7_zpow_apply_polarOrigin,
        Int.cast_natCast]
      have heq : -((j.1 : ℝ) * α7) + (k.1 : ℝ) * α7 = ((((k.1 : ℤ) - (j.1 : ℤ) : ℤ) : ℝ)) * α7 := by push_cast; ring
      rw [heq]; exact h7 ((k.1 : ℤ) - (j.1 : ℤ))
  have hF_polar : ∀ r t, (mkSiteFrameOfPacking isPacking_sites37 Fφ hF_o hF_mem).polar r t =
      Fφ (polarOrigin r t) := fun _ _ => rfl
  have hF_nbr0 : (mkSiteFrameOfPacking isPacking_sites37 Fφ hF_o hF_mem).nbr 0 =
      Fφ (polarOrigin (2 * r7) 0) := by
    change Fφ (polarOrigin (2 * r7) (((0 : ℤ) : ℝ) * α7)) = _; simp
  let F : SiteFrame sites37 v := mkSiteFrameOfPacking isPacking_sites37 Fφ hF_o hF_mem
  have hx_eq : x = F.polar ρ |δ| := by
    rw [hF_polar]
    simp only [Fφ, R, IsometryEquiv.trans_apply]
    have hx0 : x = F0.φ q := by simp [q]
    rw [hx0, hθ₀, hq_rot]
    split_ifs with hδ
    · rw [abs_of_nonneg hδ]
    · simp only [IsometryEquiv.trans_apply, reflXAxis_apply_polarOrigin]
      rw [abs_of_neg (not_le.mp hδ), neg_neg]
  have hle_nbr0 : dist x v ≤ dist x (F.nbr 0) := hclosest (F.nbr 0) (F.nbr_mem 0)
  have hlor_le : lorentz x v ≤ lorentz x (F.nbr 0) := by
    rw [← cosh_dist, ← cosh_dist]
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]; exact hle_nbr0)
  have hl1 : lorentz x v = Real.cosh ρ := by
    rw [hx_eq, hF_polar, ← hF_o, isometry_lorentz, lorentz_symm, lorentz_origin_polarOrigin]
  have hl2 : lorentz x (F.nbr 0) = Real.cosh ρ * Real.cosh (2 * r7) -
      Real.sinh ρ * Real.sinh (2 * r7) * Real.cos |δ| := by
    rw [hx_eq, hF_polar, hF_nbr0, isometry_lorentz, lorentz_polarOrigin]
    simp
  rw [hl1, hl2] at hlor_le
  have htanh_le : (Real.sinh ρ / Real.cosh ρ) * Real.cos |δ| ≤ Real.sinh r7 / Real.cosh r7 := by
    have hch2 : Real.cosh (2 * r7) - 1 = 2 * Real.sinh r7 ^ 2 := by
      have h1 := Real.cosh_sq_sub_sinh_sq r7
      rw [cosh_two_r7_eq]; nlinarith
    have hsh2 : Real.sinh (2 * r7) = 2 * Real.sinh r7 * Real.cosh r7 := Real.sinh_two_mul r7
    have hsh_r_pos : 0 < Real.sinh r7 := Real.sinh_pos_iff.mpr r7_pos
    have hch_r_pos : 0 < Real.cosh r7 := Real.cosh_pos r7
    have hch_ρ_pos : 0 < Real.cosh ρ := Real.cosh_pos ρ
    have hstep : Real.sinh ρ * Real.sinh (2 * r7) * Real.cos |δ| ≤ Real.cosh ρ * (Real.cosh (2 * r7) - 1) := by
      linarith
    rw [hch2, hsh2] at hstep
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hch_ρ_pos hch_r_pos]
    nlinarith
  have hcos_ge : Real.cos (α7 / 2) ≤ Real.cos |δ| := by
    have hhalf_le : α7 / 2 ≤ Real.pi := by unfold α7 alphaP; linarith [Real.pi_pos]
    apply Real.strictAntiOn_cos.antitoneOn
    · exact ⟨abs_nonneg δ, le_trans hclose hhalf_le⟩
    · exact ⟨by unfold α7 alphaP; positivity, hhalf_le⟩
    · exact hclose
  have hcos_half_pos : 0 < Real.cos (α7 / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by unfold α7 alphaP; linarith [Real.pi_pos],
      by unfold α7 alphaP; linarith [Real.pi_pos]⟩
  have htanh_Rc : Real.sinh ρ / Real.cosh ρ ≤ Real.sinh Rc7 / Real.cosh Rc7 := by
    have h1 : (Real.sinh ρ / Real.cosh ρ) * Real.cos (α7 / 2) ≤ Real.sinh r7 / Real.cosh r7 := by
      have hnn : 0 ≤ Real.sinh ρ / Real.cosh ρ :=
        div_nonneg (Real.sinh_nonneg_iff.mpr hρ_nn) (Real.cosh_pos ρ).le
      nlinarith
    rw [← tanh_Rc7_mul_cos_half_alpha7] at h1
    nlinarith
  have hρ_le_Rc : ρ ≤ Rc7 := by
    by_contra hgt
    push Not at hgt
    have hsub_pos : 0 < Real.sinh (ρ - Rc7) := Real.sinh_pos_iff.mpr (by linarith)
    have hdiff : Real.sinh ρ / Real.cosh ρ - Real.sinh Rc7 / Real.cosh Rc7 =
        Real.sinh (ρ - Rc7) / (Real.cosh ρ * Real.cosh Rc7) := by
      rw [Real.sinh_sub]
      field_simp [(Real.cosh_pos ρ).ne', (Real.cosh_pos Rc7).ne']
    have hpos : 0 < Real.sinh ρ / Real.cosh ρ - Real.sinh Rc7 / Real.cosh Rc7 := by
      rw [hdiff]; exact div_pos hsub_pos (mul_pos (Real.cosh_pos ρ) (Real.cosh_pos Rc7))
    linarith
  exact ⟨v, hv, F, ρ, |δ|, hρ_nn, hρ_le_Rc, abs_nonneg δ, hclose, hx_eq⟩

theorem covering_radius_Rc7 (x : H2) : ∃ v ∈ sites37, dist x v ≤ Rc7 := by
  rcases covering_radius_Rc7_sector x with ⟨v, hv, F, ρ, θ, hρ0, hρRc, _, _, rfl⟩
  refine ⟨v, hv, ?_⟩
  have hd : dist (F.polar ρ θ) v = dist (F.φ (polarOrigin ρ θ)) (F.φ origin) := by
    rw [F.origin_eq]; rfl
  rw [hd, F.φ.dist_eq, dist_polarOrigin_origin ρ θ hρ0]
  exact hρRc

end FejesTothP7.Proofs
