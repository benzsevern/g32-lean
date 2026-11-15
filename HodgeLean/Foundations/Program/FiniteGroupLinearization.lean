module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Convex

/-! # Finite-group averaged coordinate map
This is the coordinate averaging used before the local quotient contraction.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Average each action map after applying the inverse tangent representation.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 381–382, construction preceding Lemma 3.6. -/
def finiteGroupAveragedChart
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : G → E → E) (ρ : G →* (E ≃L[ℂ] E)) (x : E) : E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g⁻¹ (a g x)

example (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : G → E → E) (ρ : G →* (E ≃L[ℂ] E)) (x : E) :
    finiteGroupAveragedChart G a ρ x =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g⁻¹ (a g x) := rfl

/-- The averaged coordinate map has identity strict derivative at the origin.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, Jacobian calculation before Lemma 3.6. -/
theorem finiteGroupAveragedChart_hasStrictFDerivAt
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : G → E → E) (ρ : G →* (E ≃L[ℂ] E))
    (hd : ∀ g, HasStrictFDerivAt (a g) (ρ g : E →L[ℂ] E) 0) :
    HasStrictFDerivAt (finiteGroupAveragedChart G a ρ) (ContinuousLinearMap.id ℂ E) 0 := by
  have hi (g : G) : (ρ g⁻¹ : E →L[ℂ] E).comp (ρ g : E →L[ℂ] E) =
      ContinuousLinearMap.id ℂ E := by
    change (ρ g⁻¹ * ρ g).toContinuousLinearMap = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hg (g : G) : HasStrictFDerivAt (fun x => ρ g⁻¹ (a g x))
      (ContinuousLinearMap.id ℂ E) 0 := by
    have h := (ρ g⁻¹).toContinuousLinearMap.hasStrictFDerivAt.comp 0 (hd g)
    rw [hi g] at h
    exact h
  have hsum := HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun g _ => hg g)
  have h := hsum.const_smul ((Fintype.card G : ℂ)⁻¹)
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  exact h

/-- The averaged coordinate map intertwines the action with its tangent representation.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), Lemma 3.6, pp. 381–382. -/
theorem finiteGroupAveragedChart_equivariant
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : G → E → E) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (ρ : G →* (E ≃L[ℂ] E)) (h : G) (x : E) :
    finiteGroupAveragedChart G a ρ (a h x) =
      ρ h (finiteGroupAveragedChart G a ρ x) := by
  have he (g : G) : ρ g⁻¹ (a g (a h x)) = ρ h (ρ (g * h)⁻¹ (a (g * h) x)) := by
    rw [← ha]
    change _ = (ρ h * ρ (g * h)⁻¹) (a (g * h) x)
    rw [← map_mul, mul_inv_rev, mul_inv_cancel_left]
  unfold finiteGroupAveragedChart
  rw [map_smul, map_sum]
  congr 1
  calc
    (∑ g : G, ρ g⁻¹ (a g (a h x))) =
        ∑ g : G, ρ h (ρ (g * h)⁻¹ (a (g * h) x)) := Finset.sum_congr rfl (fun g _ => he g)
    _ = ∑ g : G, ρ h (ρ g⁻¹ (a g x)) :=
      Function.Bijective.sum_comp (Group.mulRight_bijective h) (fun g => ρ h (ρ g⁻¹ (a g x)))

/-- Inverse function theory makes the equivariant average locally invertible.
The displayed equivariance is an equality of the actual coordinate functions.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 381–382, construction and Lemma 3.6. -/
theorem finiteGroupAveragedChart_localHomeomorph
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : G → E → E) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (hzero : ∀ g, a g 0 = 0) (ρ : G →* (E ≃L[ℂ] E))
    (hd : ∀ g, HasStrictFDerivAt (a g) (ρ g : E →L[ℂ] E) 0) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = finiteGroupAveragedChart G a ρ ∧
      0 ∈ e.source ∧ e 0 = 0 ∧ ∀ g x, e (a g x) = ρ g (e x) := by
  have h : HasStrictFDerivAt (finiteGroupAveragedChart G a ρ)
      (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E) 0 :=
    finiteGroupAveragedChart_hasStrictFDerivAt G a ρ hd
  let e := h.toOpenPartialHomeomorph (finiteGroupAveragedChart G a ρ)
  refine ⟨e, h.toOpenPartialHomeomorph_coe,
    h.mem_toOpenPartialHomeomorph_source, ?_, ?_⟩
  · change finiteGroupAveragedChart G a ρ 0 = 0
    simp only [finiteGroupAveragedChart, hzero, map_zero, Finset.sum_const_zero, smul_zero]
  · intro g x
    exact finiteGroupAveragedChart_equivariant G a ha ρ g x

/-- Finite linear actions have arbitrarily small invariant open convex neighborhoods.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 380–381, invariant neighborhoods for the tangent action.
The neighborhood here is an intersection of inverse images of a norm ball. -/
theorem finite_linear_action_invariant_convex_nhds
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : G →* (E ≃L[ℝ] E)) (U : Set E) (hU : U ∈ nhds (0 : E)) :
    ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧ W ⊆ U ∧ Convex ℝ W ∧
      ∀ g x, x ∈ W → ρ g x ∈ W := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let W : Set E := ⋂ g : G, (ρ g) ⁻¹' Metric.ball (0 : E) r
  have hw0 : (0 : E) ∈ W := by
    apply Set.mem_iInter.mpr
    intro g
    simpa only [Set.mem_preimage, map_zero] using Metric.mem_ball_self hr
  refine ⟨W, isOpen_iInter_of_finite (fun g => Metric.isOpen_ball.preimage (ρ g).continuous),
    hw0, ?_, convex_iInter (fun g => (convex_ball (0 : E) r).linear_preimage
      (ρ g).toLinearMap), ?_⟩
  · intro x hx
    apply hball
    have h := Set.mem_iInter.mp hx (1 : G)
    rw [map_one] at h
    exact h
  · intro g x hx
    apply Set.mem_iInter.mpr
    intro h
    change ρ h (ρ g x) ∈ Metric.ball (0 : E) r
    change (ρ h * ρ g) x ∈ Metric.ball (0 : E) r
    rw [← map_mul]
    exact Set.mem_iInter.mp hx (h * g)

/-- The tangent representation is constructed from the actual derivatives of
an action fixing the origin, using the chain rule and inverse group elements.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, induced tangent action before Lemma 3.6. -/
theorem action_tangent_representation
    (G : Type*) [Group G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : G → E → E) (ha1 : ∀ x, a 1 x = x)
    (hamul : ∀ g h x, a (g * h) x = a g (a h x)) (hzero : ∀ g, a g 0 = 0)
    (hd : ∀ g, ∃ D : E →L[ℂ] E, HasStrictFDerivAt (a g) D 0) :
    ∃ ρ : G →* (E ≃L[ℂ] E),
      ∀ g, HasStrictFDerivAt (a g) (ρ g : E →L[ℂ] E) 0 := by
  choose D hD using hd
  let d : G →* (E →L[ℂ] E) := {
    toFun := D
    map_one' := by
      have h := hD 1
      have hfun : a 1 = id := funext ha1
      rw [hfun] at h
      exact h.hasFDerivAt.unique (hasFDerivAt_id 0)
    map_mul' := by
      intro g h
      have ho : HasStrictFDerivAt (a g) (D g) (a h 0) := by
        rw [hzero h]
        exact hD g
      have hc := ho.comp 0 (hD h)
      have hfun : (fun x => a g (a h x)) = a (g * h) :=
        funext fun x => (hamul g h x).symm
      rw [hfun] at hc
      exact (hD (g * h)).hasFDerivAt.unique hc.hasFDerivAt }
  let ρ := (ContinuousLinearEquiv.unitsEquiv ℂ E).toMonoidHom.comp d.toHomUnits
  refine ⟨ρ, fun g => ?_⟩
  have hρ : (ρ g : E →L[ℂ] E) = D g := by
    ext x
    rfl
  rw [hρ]
  exact hD g

/-- An equivariant local coordinate map restricts to arbitrarily small invariant
opens whose coordinate images are invariant and convex.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 380–382, invariant coordinate neighborhoods. -/
theorem equivariant_chart_invariant_convex_neighborhood
    (G : Type*) [Group G] [Fintype G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : G → E → E) (hzero : ∀ g, a g 0 = 0)
    (hc : ∀ g, ContinuousAt (a g) 0) (ρ : G →* (E ≃L[ℝ] E))
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source) (hezero : e 0 = 0)
    (hequiv : ∀ g x, e (a g x) = ρ g (e x)) (U : Set E) (hU : U ∈ nhds (0 : E)) :
    ∃ V W : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ U ∧ V ⊆ e.source ∧
      IsOpen W ∧ (0 : E) ∈ W ∧ Convex ℝ W ∧ e '' V = W ∧
      (∀ g x, x ∈ V → a g x ∈ V) ∧ (∀ g x, x ∈ W → ρ g x ∈ W) := by
  have hpre (g : G) : (a g) ⁻¹' e.source ∈ nhds (0 : E) :=
    (hc g).preimage_mem_nhds (by rw [hzero g]; exact e.open_source.mem_nhds he0)
  have hb := Filter.inter_mem hU (Filter.inter_mem (e.open_source.mem_nhds he0)
    (Filter.iInter_mem.mpr hpre))
  obtain ⟨r, hr, hOsub⟩ := Metric.mem_nhds_iff.mp hb
  let O := Metric.ball (0 : E) r
  have hOsource : O ⊆ e.source := fun _ hx => (hOsub hx).2.1
  have hO0 : (0 : E) ∈ O := Metric.mem_ball_self hr
  have himage0 : (0 : E) ∈ e '' O := ⟨0, hO0, hezero⟩
  obtain ⟨W, hWo, hW0, hWO, hWconv, hWinv⟩ :=
    finite_linear_action_invariant_convex_nhds G ρ (e '' O)
      ((e.isOpen_image_of_subset_source Metric.isOpen_ball hOsource).mem_nhds himage0)
  let V := e.source ∩ e ⁻¹' W
  have hVO : V ⊆ O := by
    intro x hx
    obtain ⟨z, hz, hez⟩ := hWO hx.2
    have hzx := e.injOn (hOsource hz) hx.1 hez
    simpa only [hzx] using hz
  refine ⟨V, W, e.isOpen_inter_preimage hWo, ⟨he0, ?_⟩,
    (fun _ hx => (hOsub (hVO hx)).1), Set.inter_subset_left,
    hWo, hW0, hWconv, ?_, ?_, hWinv⟩
  · change e 0 ∈ W
    rw [hezero]
    exact hW0
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨z, hz, hez⟩ := hWO hy
      refine ⟨z, ⟨hOsource hz, ?_⟩, hez⟩
      change e z ∈ W
      rw [hez]
      exact hy
  · intro g x hx
    refine ⟨Set.mem_iInter.mp (hOsub (hVO hx)).2.2 g, ?_⟩
    change e (a g x) ∈ W
    rw [hequiv]
    exact hWinv g (e x) hx.2

end HodgeLean.Foundations.Program
