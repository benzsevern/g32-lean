import HodgeLean.Foundations.Program.SchoenQuotientNormality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An integral ring map from a normal domain `A` into a ring `B` that embeds into the fraction
field of `A` compatibly with `A` is bijective. -/
theorem s2_bijective_of_integral_fractionRing {A B K : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K]
    [IsFractionRing A K] (φ : A →+* B) (ψ : B →+* K) (hψ : Function.Injective ψ)
    (hcomp : ψ.comp φ = algebraMap A K) (hφ : φ.IsIntegral) : Function.Bijective φ := by
  refine ⟨fun a b h ↦ IsFractionRing.injective A K ?_, fun b ↦ ?_⟩
  · rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, h]
  · let := φ.toAlgebra
    let ψ' : B →ₐ[A] K := { ψ with commutes' := fun a ↦ congr($hcomp a) }
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((show _root_.IsIntegral A b from hφ b).map ψ')
    refine ⟨a, hψ ?_⟩
    rw [← RingHom.comp_apply, hcomp, ha]
    rfl


/-- An actual integral birational morphism onto a normal integral scheme is an isomorphism. -/
theorem s2_isIso_of_integral_birational_normal
    {Z X : Scheme.{0}} (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsIntegralHom f]
    (hX : zmtiso_IsNormal X) (hf : zmtiso_IsBirational f) : IsIso f := by
  obtain ⟨hgen, hstalk⟩ := hf
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : {U : X.affineOpens // (U : Set X).Nonempty} ↦ (U.1 : X.Opens)) ?_ fun U ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) (⊤ : X.Opens).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨x, hxV⟩⟩, hxV⟩
  obtain ⟨⟨U, hU⟩, hne⟩ := U
  rw [MorphismProperty.isomorphisms.iff, isIso_morphismRestrict_iff_isIso_app f hU,
    ConcreteCategory.isIso_iff_bijective]
  have : Nonempty U := hne.to_subtype
  have hηX : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hηZ : genericPoint Z ∈ f ⁻¹ᵁ U := by
    change f (genericPoint Z) ∈ U
    rw [hgen]
    exact hηX
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hηZ⟩⟩
  have := s2_affineOpen_sections_integrallyClosed hX hU
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have hsp : genericPoint X ⤳ f (genericPoint Z) := (genericPoint_spec X).specializes trivial
  let ψ : Γ(Z, f ⁻¹ᵁ U) ⟶ X.functionField :=
    Z.presheaf.germ (f ⁻¹ᵁ U) _ hηZ ≫ inv (f.stalkMap _) ≫ X.presheaf.stalkSpecializes hsp
  have hψ : Function.Injective ψ.hom := by
    refine (IsFractionRing.injective (X.presheaf.stalk (f (genericPoint Z)))
      X.functionField).comp ((ConcreteCategory.bijective_of_isIso (inv (f.stalkMap _))).1.comp
        (germ_injective_of_isIntegral Z _ hηZ))
  have hcomp : ψ.hom.comp (f.app U).hom = algebraMap Γ(X, U) X.functionField := by
    change (f.app U ≫ ψ).hom = (X.presheaf.germ U (genericPoint X) hηX).hom
    congr 1
    simp only [ψ, ← Category.assoc]
    rw [← Scheme.Hom.germ_stalkMap f U (genericPoint Z) hηZ]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  exact s2_bijective_of_integral_fractionRing (f.app U).hom ψ.hom hψ hcomp
    (f.isIntegral_app U hU)


end HodgeLean.Foundations.Program
