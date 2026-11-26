/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import FejesTothP7.Proofs.Delta237Basic
import FejesTothP7.Proofs.ZoneWords

/-!
# Algebraic Zone-Layer Generator for `{3, 7}` in `Delta237`

Defines the recursive list of framed zone vertices `zoneLayer m : List (ZoneType × (H2 ≃ᵢ H2))`
generating the exact substitution words `zoneWord m` and proves:
1. The `(2, 3, 7)` relations: `rot7 ^ 7 = 1`, `halfTurn * halfTurn = 1`, `(rot7 * halfTurn) ^ 3 = 1`.
2. Every frame in `zoneLayer m` belongs to `Delta237` and preserves `detH`.
3. Exact cyclic adjacency transition `F_{k+1} = (rot7 ^ (-(i_{k+1} + 1))).trans (halfTurn.trans F_k)`
   around every zone `m ≥ 1`.
-/

noncomputable section

namespace FejesTothP7.Proofs

open FejesTothP7.H2

/-! ### Group relations for `rot7` and `halfTurn` -/

/-- Two direct (`detH`-preserving) isometries that agree on `origin` and on ONE point `p ≠ origin`
    are equal! -/
lemma direct_isometry_eq_of_eq_two {f g : H2 ≃ᵢ H2}
    (hf : ∀ a b c, detH (f a) (f b) (f c) = detH a b c)
    (hg : ∀ a b c, detH (g a) (g b) (g c) = detH a b c)
    (h0 : f origin = g origin)
    {ρ θ : ℝ} (hρ : 0 < ρ)
    (h1 : f (polarOrigin ρ θ) = g (polarOrigin ρ θ)) :
    f = g := by
  set ψ := f.trans g.symm
  have hψ_o : ψ origin = origin := by simp [ψ, h0]
  have hψ_p : ψ (polarOrigin ρ θ) = polarOrigin ρ θ := by simp [ψ, h1]
  have hψ_det : ∀ a b c, detH (ψ a) (ψ b) (ψ c) = detH a b c := by
    intro a b c
    have h1 := hg (ψ a) (ψ b) (ψ c)
    have h2 : g (ψ a) = f a := by simp [ψ]
    have h3 : g (ψ b) = f b := by simp [ψ]
    have h4 : g (ψ c) = f c := by simp [ψ]
    rw [h2, h3, h4, hf] at h1
    linarith
  set χ := (rotOrigin θ).trans (ψ.trans (rotOrigin (-θ)))
  have hχ_o : χ origin = origin := by simp [χ, rotOrigin_apply_origin, hψ_o]
  have hχ_p : χ (polarOrigin ρ 0) = polarOrigin ρ 0 := by
    simp only [χ, IsometryEquiv.trans_apply, rotOrigin_apply_polarOrigin, zero_add, hψ_p,
      add_neg_cancel]
  have hχ_det : ∀ a b c, detH (χ a) (χ b) (χ c) = detH a b c := by
    intro a b c
    simp only [χ, IsometryEquiv.trans_apply, detH_rotOrigin, hψ_det]
  have hshρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.mpr hρ
  have hsh1 : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  have hχ_e1 : χ (polarOrigin 1 0) = polarOrigin 1 0 := by
    set q := χ (polarOrigin 1 0)
    have hz : q.z = Real.cosh 1 := by
      have h := isometry_lorentz χ (polarOrigin 1 0) origin
      change lorentz q (χ origin) = lorentz (polarOrigin 1 0) origin at h
      rw [hχ_o] at h
      simpa [lorentz, origin, polarOrigin] using h
    have hx : q.x = Real.sinh 1 := by
      have h := isometry_lorentz χ (polarOrigin 1 0) (polarOrigin ρ 0)
      change lorentz q (χ (polarOrigin ρ 0)) = lorentz (polarOrigin 1 0) (polarOrigin ρ 0) at h
      rw [hχ_p] at h
      unfold lorentz at h
      simp only [polarOrigin, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero] at h
      rw [hz] at h
      have hmul : q.x * Real.sinh ρ = Real.sinh 1 * Real.sinh ρ := by linarith
      exact mul_right_cancel₀ hshρ.ne' hmul
    have hy : q.y = 0 := by
      have hs := q.on_sheet
      rw [hx, hz] at hs
      have hc := Real.cosh_sq_sub_sinh_sq 1
      nlinarith [sq_nonneg q.y]
    ext
    · rw [hx]; simp [polarOrigin]
    · rw [hy]; simp [polarOrigin]
    · rw [hz]; simp [polarOrigin]
  have hχ_e2 : χ (polarOrigin 1 (Real.pi / 2)) = polarOrigin 1 (Real.pi / 2) := by
    set q := χ (polarOrigin 1 (Real.pi / 2))
    have hz : q.z = Real.cosh 1 := by
      have h := isometry_lorentz χ (polarOrigin 1 (Real.pi / 2)) origin
      change lorentz q (χ origin) = lorentz (polarOrigin 1 (Real.pi / 2)) origin at h
      rw [hχ_o] at h
      simpa [lorentz, origin, polarOrigin] using h
    have hx : q.x = 0 := by
      have h := isometry_lorentz χ (polarOrigin 1 (Real.pi / 2)) (polarOrigin 1 0)
      change lorentz q (χ (polarOrigin 1 0)) = lorentz (polarOrigin 1 (Real.pi / 2)) (polarOrigin 1 0) at h
      rw [hχ_e1] at h
      unfold lorentz at h
      simp only [polarOrigin, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
        Real.sin_pi_div_two, mul_one, mul_zero, sub_zero] at h
      rw [hz] at h
      have hmul : q.x * Real.sinh 1 = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_right hsh1.ne'
    have hy : q.y = Real.sinh 1 := by
      have hd := hχ_det origin (polarOrigin 1 0) (polarOrigin 1 (Real.pi / 2))
      change detH (χ origin) (χ (polarOrigin 1 0)) q = detH origin (polarOrigin 1 0) (polarOrigin 1 (Real.pi / 2)) at hd
      rw [hχ_o, hχ_e1] at hd
      unfold detH at hd
      simp only [origin, polarOrigin, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
        Real.sin_pi_div_two, mul_one, mul_zero, sub_zero, zero_mul, zero_sub] at hd
      have hmul : Real.sinh 1 * q.y = Real.sinh 1 * Real.sinh 1 := by linarith
      exact mul_left_cancel₀ hsh1.ne' hmul
    ext
    · rw [hx]; simp [polarOrigin]
    · rw [hy]; simp [polarOrigin]
    · rw [hz]; simp [polarOrigin]
  have hχ_id := isometry_eq_refl_of_fix_basis χ hχ_o hχ_e1 hχ_e2
  have hrot_cancel : ∀ q : H2, rotOrigin θ (rotOrigin (-θ) q) = q := by
    intro q
    rcases exists_polarOrigin q with ⟨φ, hq⟩
    rw [hq, rotOrigin_apply_polarOrigin, rotOrigin_apply_polarOrigin]
    congr 1; ring
  have hψ_id : ∀ p, ψ p = p := by
    intro p
    have h1 := hχ_id (rotOrigin (-θ) p)
    simp only [χ, IsometryEquiv.trans_apply] at h1
    rw [hrot_cancel] at h1
    have h2 := congrArg (rotOrigin θ) h1
    rw [hrot_cancel, hrot_cancel] at h2
    exact h2
  ext p
  · have := congrArg g (hψ_id p); simpa [ψ] using congrArg H2.x this
  · have := congrArg g (hψ_id p); simpa [ψ] using congrArg H2.y this
  · have := congrArg g (hψ_id p); simpa [ψ] using congrArg H2.z this

lemma detH_rot7_zpow (k : ℤ) (a b c : H2) :
    detH ((rot7 ^ k) a) ((rot7 ^ k) b) ((rot7 ^ k) c) = detH a b c := by
  revert a b c
  induction k using Int.induction_on with
  | zero => intro a b c; simp
  | succ n ih =>
    intro a b c
    have hmul : rot7 ^ ((n : ℤ) + 1) = rot7 ^ (n : ℤ) * rot7 := zpow_add_one rot7 n
    rw [hmul]
    simp only [IsometryEquiv.mul_apply, ih, detH_rot7]
  | pred n ih =>
    intro a b c
    have hinv : ∀ p q r, detH ((rot7⁻¹ : H2 ≃ᵢ H2) p) ((rot7⁻¹ : H2 ≃ᵢ H2) q) ((rot7⁻¹ : H2 ≃ᵢ H2) r) =
        detH p q r := by
      intro p q r
      have := detH_rot7 ((rot7⁻¹ : H2 ≃ᵢ H2) p) ((rot7⁻¹ : H2 ≃ᵢ H2) q) ((rot7⁻¹ : H2 ≃ᵢ H2) r)
      simpa using this.symm
    have hmul : rot7 ^ (-(n : ℤ) - 1) = rot7 ^ (-(n : ℤ)) * rot7⁻¹ := zpow_sub_one rot7 (-(n : ℤ))
    rw [hmul]
    simp only [IsometryEquiv.mul_apply, ih, hinv]

lemma rot7_pow_seven : rot7 ^ (7 : ℤ) = 1 := by
  apply direct_isometry_eq_of_eq_two (detH_rot7_zpow 7) (fun _ _ _ => rfl)
  · rw [show origin = polarOrigin 0 0 from (polarOrigin_zero 0).symm, rot7_zpow_apply_polarOrigin]
    simp [polarOrigin_zero]
  · exact zero_lt_one
  · rw [rot7_zpow_apply_polarOrigin]
    have h7 : (0 : ℝ) + ((7 : ℤ) : ℝ) * α7 = 0 + 2 * Real.pi := by
      unfold α7 alphaP; push_cast; ring
    rw [h7, polarOrigin_add_two_pi]; simp

lemma halfTurn_mul_halfTurn : halfTurn * halfTurn = 1 := by
  apply direct_isometry_eq_of_eq_two (ρ := 2 * r7) (θ := 0)
  · intro a b c; simp only [IsometryEquiv.mul_apply, detH_halfTurn]
  · intro a b c; rfl
  · simp only [IsometryEquiv.mul_apply, halfTurn_origin, halfTurn_polarOrigin_zero]; rfl
  · linarith [r7_pos]
  · simp only [IsometryEquiv.mul_apply, halfTurn_polarOrigin_zero, halfTurn_origin]; rfl

/-- The fundamental `(2, 3, 7)` triangle rotation relation: `(rot7 * halfTurn) ^ 3 = 1`. -/
lemma rot7_mul_halfTurn_cube : (rot7 * halfTurn) ^ (3 : ℕ) = 1 := by
  set T := rot7 * halfTurn
  have hT_det : ∀ a b c, detH (T a) (T b) (T c) = detH a b c := by
    intro a b c; simp [T, detH_rot7, detH_halfTurn]
  have hpow3 : ∀ p, (T ^ 3) p = T (T (T p)) := by
    intro p; rw [pow_succ, pow_succ, pow_one]; rfl
  have hT3_det : ∀ a b c, detH ((T ^ 3) a) ((T ^ 3) b) ((T ^ 3) c) = detH a b c := by
    intro a b c; simp only [hpow3, hT_det]
  have hTo : T origin = polarOrigin (2 * r7) α7 := by
    simp [T, halfTurn_origin, rot7_apply_polarOrigin]
  have hTa : T (polarOrigin (2 * r7) α7) = polarOrigin (2 * r7) 0 := by
    simp [T, halfTurn_polarOrigin_alpha7, rot7_apply_polarOrigin]
  have hT0 : T (polarOrigin (2 * r7) 0) = origin := by
    simp [T, halfTurn_polarOrigin_zero, rot7_eq_rotOrigin, rotOrigin_apply_origin]
  apply direct_isometry_eq_of_eq_two (ρ := 2 * r7) (θ := 0) hT3_det (fun _ _ _ => rfl)
  · rw [hpow3, hTo, hTa, hT0]; rfl
  · linarith [r7_pos]
  · rw [hpow3, hT0, hTo, hTa]; rfl

/-- Equivalent form of `(rot7 * halfTurn)^3 = 1`: `halfTurn * rot7 * halfTurn = rot7⁻¹ * halfTurn * rot7⁻¹`. -/
lemma braid_relation :
    halfTurn * rot7 * halfTurn = rot7⁻¹ * halfTurn * rot7⁻¹ := by
  have hc : rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn = 1 := by
    have h := rot7_mul_halfTurn_cube
    rw [pow_succ, pow_succ, pow_one] at h
    simpa [mul_assoc] using h
  have hh : halfTurn * halfTurn = 1 := halfTurn_mul_halfTurn
  have h1 : rot7⁻¹ * (rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn) * (halfTurn * rot7⁻¹) =
      rot7⁻¹ * 1 * (halfTurn * rot7⁻¹) := by rw [hc]
  have hlhs : rot7⁻¹ * (rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn) * (halfTurn * rot7⁻¹) =
      halfTurn * rot7 * halfTurn := by
    calc rot7⁻¹ * (rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn) * (halfTurn * rot7⁻¹)
        = (rot7⁻¹ * rot7) * halfTurn * rot7 * halfTurn * rot7 * (halfTurn * halfTurn) * rot7⁻¹ := by
          simp [mul_assoc]
      _ = halfTurn * rot7 * halfTurn * (rot7 * rot7⁻¹) := by rw [inv_mul_cancel, hh]; simp [mul_assoc]
      _ = halfTurn * rot7 * halfTurn := by simp
  rw [hlhs, mul_one] at h1
  simpa [mul_assoc] using h1

/-- Second form of `(rot7 * halfTurn)^3 = 1`: `halfTurn * rot7⁻¹ * halfTurn = rot7 * halfTurn * rot7`. -/
lemma braid_relation_inv :
    halfTurn * rot7⁻¹ * halfTurn = rot7 * halfTurn * rot7 := by
  have hh : halfTurn * halfTurn = 1 := halfTurn_mul_halfTurn
  have hc : rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn = 1 := by
    have h := rot7_mul_halfTurn_cube
    rw [pow_succ, pow_succ, pow_one] at h
    simpa [mul_assoc] using h
  have h5 : (rot7 * halfTurn * rot7 * halfTurn) * (halfTurn * rot7⁻¹ * halfTurn) =
      (rot7 * halfTurn * rot7 * halfTurn) * (rot7 * halfTurn * rot7) := by
    calc (rot7 * halfTurn * rot7 * halfTurn) * (halfTurn * rot7⁻¹ * halfTurn)
        = rot7 * halfTurn * rot7 * (halfTurn * halfTurn) * rot7⁻¹ * halfTurn := by simp [mul_assoc]
      _ = rot7 * halfTurn * (rot7 * rot7⁻¹) * halfTurn := by rw [hh]; simp [mul_assoc]
      _ = rot7 * (halfTurn * halfTurn) := by simp [mul_assoc]
      _ = rot7 := by rw [hh, mul_one]
      _ = (rot7 * halfTurn * rot7 * halfTurn * rot7 * halfTurn) * rot7 := by rw [hc, one_mul]
      _ = (rot7 * halfTurn * rot7 * halfTurn) * (rot7 * halfTurn * rot7) := by simp [mul_assoc]
  exact mul_left_cancel h5

/-! ### Recursive zone-layer generator -/

/-- Type index `i(t) ∈ {1, 2}`: number of inner neighbors in `Z_{m-1}`. -/
def _root_.FejesTothP7.ZoneType.innerCount : ZoneType → ℕ
  | .t1 => 1
  | .t2 => 2

/-- Frame transition from `F` to its `j`-th neighbor (`j : ℤ`), rotated so `F origin` sits at angle `d * α7`. -/
def stepFrame (F : H2 ≃ᵢ H2) (j d : ℤ) : H2 ≃ᵢ H2 :=
  (rot7 ^ (-d)).trans (halfTurn.trans ((rot7 ^ j).trans F))

/-- Children emitted by one vertex `(t, F)` of `zoneLayer m` into `zoneLayer (m + 1)`. -/
def nextLayerEntry : ZoneType × (H2 ≃ᵢ H2) → List (ZoneType × (H2 ≃ᵢ H2))
  | (.t1, F) => [(.t1, stepFrame F 4 1), (.t1, stepFrame F 5 1), (.t2, stepFrame F 6 2)]
  | (.t2, F) => [(.t1, stepFrame F 5 1), (.t2, stepFrame F 6 2)]

/-- Zone 1: the 7 neighbors of `origin`, in CCW order `k = 0..6`. -/
def zoneLayer1 : List (ZoneType × (H2 ≃ᵢ H2)) :=
  (List.finRange 7).map fun k =>
    (.t1, (rot7 ^ (-1 : ℤ)).trans (halfTurn.trans (rot7 ^ (k.1 : ℤ))))

/-- Recursive framed zone layers `zoneLayer m` (`m ≥ 1`). -/
def zoneLayer : ℕ → List (ZoneType × (H2 ≃ᵢ H2))
  | 0 => []
  | 1 => zoneLayer1
  | m + 2 => (zoneLayer (m + 1)).flatMap nextLayerEntry

lemma zoneLayer_types (m : ℕ) :
    (zoneLayer m).map Prod.fst = zoneWord m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => decide
    | succ n =>
      change ((zoneLayer (n + 1)).flatMap nextLayerEntry).map Prod.fst = sigmaWord (zoneWord (n + 1))
      rw [← ih, sigmaWord, List.map_flatMap, List.flatMap_map]
      congr 1
      funext x
      rcases x with ⟨t, F⟩
      cases t <;> rfl

lemma zoneLayer_length (m : ℕ) : (zoneLayer m).length = (zoneWord m).length := by
  rw [← zoneLayer_types m, List.length_map]

lemma stepFrame_mem_Delta237 {F : H2 ≃ᵢ H2} (hF : F ∈ Delta237) (j d : ℤ) :
    stepFrame F j d ∈ Delta237 := by
  unfold stepFrame
  change F * (rot7 ^ j * (halfTurn * rot7 ^ (-d))) ∈ Delta237
  exact Delta237.mul_mem hF (Delta237.mul_mem (Delta237.zpow_mem rot7_mem j)
    (Delta237.mul_mem halfTurn_mem (Delta237.zpow_mem rot7_mem (-d))))

lemma stepFrame_detH {F : H2 ≃ᵢ H2} (hF : ∀ a b c, detH (F a) (F b) (F c) = detH a b c)
    (j d : ℤ) (a b c : H2) :
    detH (stepFrame F j d a) (stepFrame F j d b) (stepFrame F j d c) = detH a b c := by
  simp only [stepFrame, IsometryEquiv.trans_apply, hF, detH_rot7_zpow, detH_halfTurn]

lemma zoneLayer_mem_Delta237_and_detH (m : ℕ) :
    ∀ x ∈ zoneLayer m, x.2 ∈ Delta237 ∧ ∀ a b c, detH (x.2 a) (x.2 b) (x.2 c) = detH a b c := by
  induction m with
  | zero => intro x hx; cases hx
  | succ k ih =>
    cases k with
    | zero =>
      intro x hx
      simp only [zoneLayer, zoneLayer1, List.mem_map, List.mem_finRange, true_and] at hx
      rcases hx with ⟨j, rfl⟩
      refine ⟨?_, ?_⟩
      · change rot7 ^ (j.1 : ℤ) * (halfTurn * rot7 ^ (-1 : ℤ)) ∈ Delta237
        exact Delta237.mul_mem (Delta237.zpow_mem rot7_mem _)
          (Delta237.mul_mem halfTurn_mem (Delta237.zpow_mem rot7_mem _))
      · intro a b c
        simp only [IsometryEquiv.trans_apply, detH_rot7_zpow, detH_halfTurn]
    | succ n =>
      intro x hx
      simp only [zoneLayer, List.mem_flatMap] at hx
      rcases hx with ⟨⟨t, F⟩, hmem, hchild⟩
      have hF := ih (t, F) hmem
      cases t with
      | t1 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl | rfl <;>
          exact ⟨stepFrame_mem_Delta237 hF.1 _ _, stepFrame_detH hF.2 _ _⟩
      | t2 =>
        simp only [nextLayerEntry, List.mem_cons, List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl <;>
          exact ⟨stepFrame_mem_Delta237 hF.1 _ _, stepFrame_detH hF.2 _ _⟩

/-! ### Exact cyclic adjacency transition `AdjFrame` -/

/-- Two consecutive entries `(t₁, F₁)` and `(t₂, F₂)` along a zone ring satisfy `AdjFrame`. -/
def AdjFrame (e₁ e₂ : ZoneType × (H2 ≃ᵢ H2)) : Prop :=
  e₂.2 = (rot7 ^ (-((e₂.1.innerCount + 1 : ℕ) : ℤ))).trans (halfTurn.trans e₁.2)

/-- Key algebraic step: `stepFrame F j 1` and `stepFrame F (j + 1) t.innerCount` are `AdjFrame`! -/
lemma adjFrame_sibling (F : H2 ≃ᵢ H2) (j : ℤ) (t : ZoneType) :
    AdjFrame (.t1, stepFrame F j 1) (t, stepFrame F (j + 1) (t.innerCount : ℤ)) := by
  unfold AdjFrame stepFrame
  change F * (rot7 ^ (j + 1) * (halfTurn * rot7 ^ (-(t.innerCount : ℤ)))) =
    (F * (rot7 ^ j * (halfTurn * rot7 ^ (-1 : ℤ)))) *
    (halfTurn * rot7 ^ (-((t.innerCount + 1 : ℕ) : ℤ)))
  have h1 : rot7 ^ (-((t.innerCount + 1 : ℕ) : ℤ)) = rot7⁻¹ * rot7 ^ (-(t.innerCount : ℤ)) := by
    rw [← zpow_neg_one, ← zpow_add]; congr 1; push_cast; ring
  rw [zpow_add_one, h1, zpow_neg_one]
  calc F * (rot7 ^ j * rot7 * (halfTurn * rot7 ^ (-(t.innerCount : ℤ))))
      = F * rot7 ^ j * (rot7 * halfTurn * rot7) * rot7⁻¹ * rot7 ^ (-(t.innerCount : ℤ)) := by
        simp [mul_assoc]
    _ = F * rot7 ^ j * (halfTurn * rot7⁻¹ * halfTurn) * rot7⁻¹ * rot7 ^ (-(t.innerCount : ℤ)) := by
        rw [braid_relation_inv]
    _ = F * (rot7 ^ j * (halfTurn * rot7⁻¹)) * (halfTurn * (rot7⁻¹ * rot7 ^ (-(t.innerCount : ℤ)))) := by
        simp [mul_assoc]

/-- Cross-parent algebraic step: if `AdjFrame e₁ e₂`, then the LAST child of `e₁` (type `t2` at `6α`)
    and the FIRST child of `e₂` (type `t1` at `(i₂ + 3)α`) are `AdjFrame`! -/
lemma adjFrame_cross (e₁ e₂ : ZoneType × (H2 ≃ᵢ H2)) (hadj : AdjFrame e₁ e₂) :
    AdjFrame (.t2, stepFrame e₁.2 6 2)
      (.t1, stepFrame e₂.2 ((e₂.1.innerCount + 3 : ℕ) : ℤ) 1) := by
  unfold AdjFrame at hadj
  unfold AdjFrame stepFrame
  simp only [trans_eq_mul_rev] at hadj ⊢
  rw [hadj]
  have hr6 : rot7 ^ (6 : ℤ) = rot7⁻¹ := by
    have h7 : rot7 ^ (6 : ℤ) * rot7 = 1 := by
      rw [← zpow_add_one]; exact rot7_pow_seven
    exact eq_inv_of_mul_eq_one_left h7
  have hr2 : rot7 ^ (-((e₂.1.innerCount + 1 : ℕ) : ℤ)) * rot7 ^ ((e₂.1.innerCount + 3 : ℕ) : ℤ) =
      rot7 * rot7 := by
    rw [← zpow_add]
    have heq : -((e₂.1.innerCount + 1 : ℕ) : ℤ) + ((e₂.1.innerCount + 3 : ℕ) : ℤ) = 1 + 1 := by
      push_cast; ring
    rw [heq, zpow_add, zpow_one]
  have hm2 : rot7 ^ (-2 : ℤ) = rot7⁻¹ * rot7⁻¹ := by
    rw [show (-2 : ℤ) = (-1 : ℤ) + (-1 : ℤ) by ring, zpow_add, zpow_neg_one]
  have ht1 : rot7 ^ (-((ZoneType.t1.innerCount + 1 : ℕ) : ℤ)) = rot7⁻¹ * rot7⁻¹ := by
    change rot7 ^ (-2 : ℤ) = _; exact hm2
  rw [hr6, hm2, ht1, zpow_neg_one]
  simp only [mul_assoc]
  rw [← mul_assoc (rot7 ^ (-((e₂.1.innerCount + 1 : ℕ) : ℤ))), hr2]
  have hkey : halfTurn * (rot7 * (rot7 * (halfTurn * rot7⁻¹))) =
      rot7⁻¹ * (halfTurn * (rot7⁻¹ * (rot7⁻¹ * (halfTurn * (rot7⁻¹ * rot7⁻¹))))) := by
    calc halfTurn * (rot7 * (rot7 * (halfTurn * rot7⁻¹)))
        = halfTurn * rot7 * (rot7 * halfTurn * rot7) * rot7⁻¹ * rot7⁻¹ := by simp [mul_assoc]
      _ = halfTurn * rot7 * (halfTurn * rot7⁻¹ * halfTurn) * rot7⁻¹ * rot7⁻¹ := by
          rw [braid_relation_inv]
      _ = (halfTurn * rot7 * halfTurn) * rot7⁻¹ * halfTurn * rot7⁻¹ * rot7⁻¹ := by
          simp [mul_assoc]
      _ = (rot7⁻¹ * halfTurn * rot7⁻¹) * rot7⁻¹ * halfTurn * rot7⁻¹ * rot7⁻¹ := by
          rw [braid_relation]
      _ = rot7⁻¹ * (halfTurn * (rot7⁻¹ * (rot7⁻¹ * (halfTurn * (rot7⁻¹ * rot7⁻¹))))) := by
          simp [mul_assoc]
  simp only [mul_assoc]
  rw [hkey]

/-- Cyclic `AdjFrame` invariant around a nonempty list of framed vertices. -/
def CyclicAdj (L : List (ZoneType × (H2 ≃ᵢ H2))) : Prop :=
  0 < L.length ∧
  ∀ k : Fin L.length,
    AdjFrame (L.get k) (L.get ⟨(k.1 + 1) % L.length, Nat.mod_lt _ (Nat.zero_lt_of_lt k.2)⟩)

lemma zoneLayer1_length : zoneLayer1.length = 7 := by simp [zoneLayer1]

lemma zoneLayer1_get (i : Fin zoneLayer1.length) :
    zoneLayer1.get i = (.t1, (rot7 ^ (-1 : ℤ)).trans (halfTurn.trans (rot7 ^ (i.1 : ℤ)))) := by
  rw [List.get_eq_getElem]
  simp only [zoneLayer1, List.getElem_map, List.getElem_finRange, Fin.val_cast]

/-- Helper: `zoneLayer 1` satisfies `CyclicAdj`. -/
lemma zoneLayer1_cyclicAdj : CyclicAdj zoneLayer1 := by
  refine ⟨by rw [zoneLayer1_length]; omega, ?_⟩
  intro k
  have hlen : zoneLayer1.length = 7 := zoneLayer1_length
  have hk_lt : k.1 < 7 := by omega
  rw [zoneLayer1_get k, zoneLayer1_get ⟨(k.1 + 1) % zoneLayer1.length, _⟩]
  unfold AdjFrame
  simp only [trans_eq_mul_rev]
  have hmod : rot7 ^ (((k.1 + 1) % zoneLayer1.length : ℕ) : ℤ) = rot7 ^ (k.1 : ℤ) * rot7 := by
    have hmod_eq : (k.1 + 1) % zoneLayer1.length = (k.1 + 1) % 7 := congrArg ((k.1 + 1) % ·) hlen
    rw [hmod_eq]
    by_cases h6 : k.1 = 6
    · have h7 : rot7 ^ (6 : ℤ) * rot7 = 1 := by
        rw [← zpow_add_one]; exact rot7_pow_seven
      rw [h6]; simp only [Nat.reduceAdd, Nat.mod_self, Nat.cast_zero, zpow_zero]
      exact h7.symm
    · have hlt : k.1 + 1 < 7 := by omega
      rw [Nat.mod_eq_of_lt hlt, Nat.cast_add, Nat.cast_one, zpow_add_one]
  have hm2 : rot7 ^ (-((ZoneType.t1.innerCount + 1 : ℕ) : ℤ)) = rot7⁻¹ * rot7⁻¹ := by
    change rot7 ^ (-2 : ℤ) = _
    rw [show (-2 : ℤ) = (-1 : ℤ) + (-1 : ℤ) by ring, zpow_add, zpow_neg_one]
  rw [hmod, hm2, zpow_neg_one]
  calc rot7 ^ (k.1 : ℤ) * rot7 * (halfTurn * rot7⁻¹)
      = rot7 ^ (k.1 : ℤ) * (rot7 * halfTurn * rot7) * rot7⁻¹ * rot7⁻¹ := by simp [mul_assoc]
    _ = rot7 ^ (k.1 : ℤ) * (halfTurn * rot7⁻¹ * halfTurn) * rot7⁻¹ * rot7⁻¹ := by
        rw [braid_relation_inv]
    _ = rot7 ^ (k.1 : ℤ) * (halfTurn * rot7⁻¹) * (halfTurn * (rot7⁻¹ * rot7⁻¹)) := by
        simp [mul_assoc]

/-- Induction step: if `L` is `CyclicAdj`, then `L.flatMap nextLayerEntry` is `CyclicAdj`! -/
lemma flatMap_nextLayerEntry_cyclicAdj {L : List (ZoneType × (H2 ≃ᵢ H2))} (hL : CyclicAdj L) :
    CyclicAdj (L.flatMap nextLayerEntry) := by
  have hblock_adj : ∀ e : ZoneType × (H2 ≃ᵢ H2),
      ∀ j : ℕ, (hj : j + 1 < (nextLayerEntry e).length) →
        AdjFrame ((nextLayerEntry e)[j]'(by omega)) ((nextLayerEntry e)[j + 1]'hj) := by
    rintro ⟨t, F⟩ j hj
    cases t with
    | t1 =>
      simp only [nextLayerEntry, List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _
      · simpa [nextLayerEntry, ZoneType.innerCount] using adjFrame_sibling F 4 .t1
      · simpa [nextLayerEntry, ZoneType.innerCount] using adjFrame_sibling F 5 .t2
      · omega
    | t2 =>
      simp only [nextLayerEntry, List.length_cons, List.length_nil] at hj
      rcases j with _ | _
      · simpa [nextLayerEntry, ZoneType.innerCount] using adjFrame_sibling F 5 .t2
      · omega
  have hblock_pos : ∀ e : ZoneType × (H2 ≃ᵢ H2), 2 ≤ (nextLayerEntry e).length := by
    rintro ⟨t, F⟩; cases t <;> simp [nextLayerEntry]
  have hblock_first : ∀ e : ZoneType × (H2 ≃ᵢ H2),
      (nextLayerEntry e)[0]'(by have := hblock_pos e; omega) =
        (.t1, stepFrame e.2 ((e.1.innerCount + 3 : ℕ) : ℤ) 1) := by
    rintro ⟨t, F⟩; cases t <;> rfl
  have hblock_last : ∀ e : ZoneType × (H2 ≃ᵢ H2),
      (nextLayerEntry e)[(nextLayerEntry e).length - 1]'(by have := hblock_pos e; omega) =
        (.t2, stepFrame e.2 6 2) := by
    rintro ⟨t, F⟩; cases t <;> rfl
  have hlin : ∀ M : List (ZoneType × (H2 ≃ᵢ H2)),
      (∀ i : ℕ, (hi : i + 1 < M.length) → AdjFrame (M[i]'(by omega)) (M[i + 1]'hi)) →
      ∀ i : ℕ, (hi : i + 1 < (M.flatMap nextLayerEntry).length) →
        AdjFrame ((M.flatMap nextLayerEntry)[i]'(by omega)) ((M.flatMap nextLayerEntry)[i + 1]'hi) := by
    intro M
    induction M with
    | nil => intro _ i hi; simp at hi
    | cons a tl ih =>
      intro hM i hi
      simp only [List.flatMap_cons] at hi ⊢
      have hlen_app : ((nextLayerEntry a) ++ tl.flatMap nextLayerEntry).length =
          (nextLayerEntry a).length + (tl.flatMap nextLayerEntry).length := List.length_append
      have hba_pos : 2 ≤ (nextLayerEntry a).length := hblock_pos a
      by_cases hlt : i + 1 < (nextLayerEntry a).length
      · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]
        exact hblock_adj a i hlt
      · by_cases heq : i + 1 = (nextLayerEntry a).length
        · have hi_eq : i = (nextLayerEntry a).length - 1 := by omega
          rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
          have hzero : i + 1 - (nextLayerEntry a).length = 0 := by omega
          cases tl with
          | nil => simp at hi; omega
          | cons b tl' =>
            simp only [List.flatMap_cons] at hi hlen_app ⊢
            have hbb_pos : 2 ≤ (nextLayerEntry b).length := hblock_pos b
            have h1 : (nextLayerEntry b ++ tl'.flatMap nextLayerEntry)[i + 1 - (nextLayerEntry a).length]'(by omega) =
                (nextLayerEntry b)[0]'(by omega) := by
              simp only [hzero]
              exact List.getElem_append_left (by omega)
            rw [h1]
            have hlast : (nextLayerEntry a)[i]'(by omega) = (.t2, stepFrame a.2 6 2) := by
              simpa [hi_eq] using hblock_last a
            rw [hlast, hblock_first b]
            exact adjFrame_cross a b (hM 0 (by simp))
        · have hge : (nextLayerEntry a).length ≤ i := by omega
          rw [List.getElem_append_right hge, List.getElem_append_right (by omega)]
          have hsub : i + 1 - (nextLayerEntry a).length = (i - (nextLayerEntry a).length) + 1 := by omega
          have hM_tl : ∀ j : ℕ, (hj : j + 1 < tl.length) → AdjFrame (tl[j]'(by omega)) (tl[j + 1]'hj) := by
            intro j hj; exact hM (j + 1) (by simp; omega)
          have hrec := ih hM_tl (i - (nextLayerEntry a).length) (by omega)
          simpa [hsub] using hrec
  have hLL_adj : ∀ i : ℕ, (hi : i + 1 < (L ++ L).length) →
      AdjFrame ((L ++ L)[i]'(by omega)) ((L ++ L)[i + 1]'hi) := by
    intro i hi
    have hlenL : 0 < L.length := hL.1
    by_cases h1 : i < L.length
    · have g0 : (L ++ L)[i]'(by omega) = L.get ⟨i, h1⟩ := by
        rw [List.getElem_append_left h1]; rfl
      have g1 : (L ++ L)[i + 1]'hi = L.get ⟨(i + 1) % L.length, Nat.mod_lt _ hlenL⟩ := by
        simpa [List.get_eq_getElem] using getElem_append_self L hlenL i 1 h1 (by omega)
      rw [g0, g1]
      exact hL.2 ⟨i, h1⟩
    · have hi' : i - L.length < L.length := by simp at hi; omega
      have g0 : (L ++ L)[i]'(by omega) = L.get ⟨i - L.length, hi'⟩ := by
        rw [List.getElem_append_right (by omega)]; rfl
      have g1 : (L ++ L)[i + 1]'hi = L.get ⟨((i - L.length) + 1) % L.length, Nat.mod_lt _ hlenL⟩ := by
        rw [List.getElem_append_right (by omega)]
        have hlt2 : i + 1 - L.length < L.length := by simp at hi; omega
        have heq : i + 1 - L.length = (i - L.length) + 1 := by omega
        simp only [List.get_eq_getElem]
        congr 1; rw [heq, Nat.mod_eq_of_lt (by omega)]
      rw [g0, g1]
      exact hL.2 ⟨i - L.length, hi'⟩
  have hflat_pos : 0 < (L.flatMap nextLayerEntry).length := by
    cases L with
    | nil => exact absurd hL.1 (by simp)
    | cons a tl =>
      simp only [List.flatMap_cons, List.length_append]
      have := hblock_pos a; omega
  set W := L.flatMap nextLayerEntry
  refine ⟨hflat_pos, ?_⟩
  intro k
  have hWW : (L ++ L).flatMap nextLayerEntry = W ++ W := List.flatMap_append
  have hstep := hlin (L ++ L) hLL_adj k.1 (by rw [hWW]; simp; omega)
  have g0 : ((L ++ L).flatMap nextLayerEntry)[k.1]'(by rw [hWW]; simp; omega) = W.get k := by
    simp only [hWW]; rw [List.getElem_append_left k.2]; rfl
  have g1 : ((L ++ L).flatMap nextLayerEntry)[k.1 + 1]'(by rw [hWW]; simp; omega) =
      W.get ⟨(k.1 + 1) % W.length, Nat.mod_lt _ hflat_pos⟩ := by
    simp only [hWW]
    simpa [List.get_eq_getElem] using getElem_append_self W hflat_pos k.1 1 k.2 (by omega)
  rw [← g0, ← g1]
  exact hstep

/-- Every zone layer `m ≥ 1` satisfies `CyclicAdj`. -/
theorem zoneLayer_cyclicAdj (m : ℕ) (hm : 1 ≤ m) : CyclicAdj (zoneLayer m) := by
  induction m, hm using Nat.le_induction with
  | base => exact zoneLayer1_cyclicAdj
  | succ k hk ih =>
    have hsucc : zoneLayer (k + 1) = (zoneLayer k).flatMap nextLayerEntry := by
      cases k with
      | zero => omega
      | succ n => rfl
    rw [hsucc]
    exact flatMap_nextLayerEntry_cyclicAdj ih

end FejesTothP7.Proofs
