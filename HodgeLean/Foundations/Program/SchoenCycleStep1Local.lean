import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic

/-! # Local maps into finite smooth inverse-image sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The spectrum of the generic stalk has dense image. -/
theorem s2e_step1_generic_dominant (X : Scheme) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply top_unique
  change Set.univ ⊆ _
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩)

/-- Generic pullback of sections agrees with the germ map. -/
theorem s2e_step1_generic_appLE (X : Scheme) [IsIntegral X]
    (U : X.Opens) [Nonempty U]
    (h : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) :
    (X.fromSpecStalk (genericPoint X)).appLE U ⊤ h ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField U := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp,
    homOfLE_refl, op_id]
  rw [(Spec (X.presheaf.stalk (genericPoint X))).presheaf.map_id]
  simp only [Category.id_comp]
  change X.presheaf.germ U (genericPoint X) hx ≫
    (Scheme.ΓSpecIso X.functionField).inv ≫ (Scheme.ΓSpecIso X.functionField).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

/-- Integral elements in a compatible algebra have unique regular images. -/
theorem s2e_step1_integralChartMap
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left] (U : Y.left.Opens) (hU : IsAffineOpen U)
    [Nonempty (f.left ⁻¹ᵁ U)] (A : Type) [CommRing A] [Algebra Γ(Y.left, U) A]
    (κ : A →+* X.left.functionField)
    (hκ : ∀ r : Γ(Y.left, U), κ (algebraMap Γ(Y.left, U) A r) =
      algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField ((f.left.app U).hom r)) :
    ∃! j : integralClosure Γ(Y.left, U) A →+* Γ(X.left, f.left ⁻¹ᵁ U),
      ∀ a, algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField (j a) = κ a := by
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) X.left.functionField :=
    ((algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField).comp (f.left.app U).hom).toAlgebra
  let k : A →ₐ[Γ(Y.left, U)] X.left.functionField := ⟨κ, hκ⟩
  obtain ⟨e, he⟩ := s2e_finite_smooth_sections_integralClosure_equiv X Y f U hU
  let i : integralClosure Γ(Y.left, U) A →ₐ[Γ(Y.left, U)]
      integralClosure Γ(Y.left, U) X.left.functionField :=
    (k.comp (integralClosure Γ(Y.left, U) A).val).codRestrict _
      (fun a => a.property.map k)
  let j := (e.symm.toAlgHom.comp i).toRingHom
  have hj : ∀ a, algebraMap Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField (j a) = κ a := by
    intro a
    rw [← he]
    change ((e (e.symm (i a))) : X.left.functionField) = κ a
    rw [e.apply_symm_apply]
    rfl
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  ext a
  apply X.left.germToFunctionField_injective (f.left ⁻¹ᵁ U)
  exact (hj' a).trans (hj a).symm

/-- An affine chart of an integral target receives a regular extension of its generic map. -/
theorem s2e_step1_integralTarget_chart
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (T : Scheme) (p : T ⟶ Y.left) [IsIntegralHom p]
    (v : Spec X.left.functionField ⟶ T)
    (hv : v ≫ p = X.left.fromSpecStalk (genericPoint X.left) ≫ f.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty (f.left ⁻¹ᵁ U)] :
    ∃ g : (f.left ⁻¹ᵁ U).toScheme ⟶ T,
      g ≫ p = (f.left ⁻¹ᵁ U).ι ≫ f.left ∧
      Spec.map (X.left.germToFunctionField (f.left ⁻¹ᵁ U)) ≫
        (hU.preimage f.left).isoSpec.inv ≫ g = v := by
  let F := X.left.functionField
  let W := p ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage p
  have hx : genericPoint X.left ∈ f.left ⁻¹ᵁ U :=
    ((genericPoint_spec X.left).mem_open_set_iff (f.left ⁻¹ᵁ U).isOpen).mpr
      (by simpa using ‹Nonempty (f.left ⁻¹ᵁ U)›)
  have ht : ⊤ ≤ (X.left.fromSpecStalk (genericPoint X.left)) ⁻¹ᵁ (f.left ⁻¹ᵁ U) := by
    change ∀ z : PrimeSpectrum X.left.functionField, _
    intro z
    intro _
    have hz : z = IsLocalRing.closedPoint X.left.functionField := Subsingleton.elim _ _
    change f.left (X.left.fromSpecStalk (genericPoint X.left) z) ∈ U
    rw [hz]
    change f.left (X.left.fromSpecStalk (genericPoint X.left)
      (IsLocalRing.closedPoint (X.left.presheaf.stalk (genericPoint X.left)))) ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hx
  have hvW : ⊤ ≤ v ⁻¹ᵁ W := by
    change ⊤ ≤ (v ≫ p) ⁻¹ᵁ U
    rw [hv]
    exact ht
  let k : Γ(T, W) →+* F :=
    ((v.appLE W ⊤ hvW) ≫ (Scheme.ΓSpecIso F).hom).hom
  letI : Algebra Γ(Y.left, U) Γ(T, W) := (p.app U).hom.toAlgebra
  have hk : ∀ r : Γ(Y.left, U), k (algebraMap Γ(Y.left, U) Γ(T, W) r) =
      algebraMap Γ(X.left, f.left ⁻¹ᵁ U) F ((f.left.app U).hom r) := by
    have he : p.app U ≫ v.appLE W ⊤ hvW ≫ (Scheme.ΓSpecIso F).hom =
        f.left.app U ≫ X.left.germToFunctionField (f.left ⁻¹ᵁ U) := by
      rw [Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
        ]
      have hc : (v ≫ p).appLE U ⊤ (by exact hvW) =
          (X.left.fromSpecStalk (genericPoint X.left) ≫ f.left).appLE U ⊤ ht := by
        congr 1
      rw [hc, ← Scheme.Hom.appLE_comp_appLE (X.left.fromSpecStalk (genericPoint X.left))
          f.left U (f.left ⁻¹ᵁ U) ⊤ le_rfl ht,
        Category.assoc, s2e_step1_generic_appLE]
      rw [← Scheme.Hom.app_eq_appLE]
    exact fun r => congrArg (fun t : Γ(Y.left, U) ⟶ F => t.hom r) he
  obtain ⟨j, hj, -⟩ := s2e_step1_integralChartMap X Y f U hU Γ(T, W) k hk
  let inc : Γ(T, W) →+* integralClosure Γ(Y.left, U) Γ(T, W) :=
    (RingHom.id Γ(T, W)).codRestrict _ (fun a => p.isIntegral_app U hU a)
  let r : Γ(T, W) →+* Γ(X.left, f.left ⁻¹ᵁ U) := j.comp inc
  have hr : ∀ a, algebraMap Γ(X.left, f.left ⁻¹ᵁ U) F (r a) = k a :=
    fun a => hj (inc a)
  have hrbase : p.app U ≫ CommRingCat.ofHom r = f.left.app U := by
    ext a
    apply X.left.germToFunctionField_injective (f.left ⁻¹ᵁ U)
    exact (hr ((p.app U).hom a)).trans (hk a)
  let g : (f.left ⁻¹ᵁ U).toScheme ⟶ T :=
    (f.left ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) ≫ hW.fromSpec
  refine ⟨g, ?_, ?_⟩
  · dsimp only [g]
    rw [Category.assoc, Category.assoc,
      ← hU.SpecMap_appLE_fromSpec p hW le_rfl,
      ← Spec.map_comp_assoc]
    rw [Scheme.Hom.appLE_eq_app, hrbase, Scheme.Hom.app_eq_appLE,
      hU.SpecMap_appLE_fromSpec f.left (hU.preimage f.left) le_rfl,
      ← Category.assoc, IsAffineOpen.toSpecΓ_fromSpec]
  · have he : CommRingCat.ofHom r ≫ X.left.germToFunctionField (f.left ⁻¹ᵁ U) =
        v.appLE W ⊤ hvW ≫ (Scheme.ΓSpecIso F).hom := by
      ext a
      exact hr a
    dsimp only [g]
    simp only [Category.assoc, IsAffineOpen.isoSpec_inv_toSpecΓ_assoc]
    rw [← Spec.map_comp_assoc, he,
      Spec.map_comp, Category.assoc, hW.SpecMap_appLE_fromSpec v
        (isAffineOpen_top _) hvW, ← Category.assoc,
      SpecMap_ΓSpecIso_hom, ← Scheme.isoSpec_hom,
      IsAffineOpen.fromSpec_top, Iso.hom_inv_id, Category.id_comp]

end HodgeLean.Foundations.Program
