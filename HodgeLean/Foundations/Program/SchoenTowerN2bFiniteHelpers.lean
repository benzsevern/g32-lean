import HodgeLean.Foundations.Program.SchoenTowerVanishingSuppliers
import HodgeLean.Foundations.Program.SchoenTowerN2a

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem n2b_stalk_finite_of_comp {L : CommRingCat} [IsLocalRing L] {X Y : Scheme}
    (f : Spec L ⟶ X) (g : X ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo (f ≫ g)).hom.Finite) :
    (Scheme.stalkClosedPointTo f).hom.Finite := by
  rw [Scheme.stalkClosedPointTo_comp] at hf
  exact RingHom.Finite.of_comp_finite hf

theorem n2b_generic_stalk_finite (X : Scheme) [IsIntegral X] :
    (Scheme.stalkClosedPointTo (X.fromSpecStalk (genericPoint X))).hom.Finite := by
  rw [Scheme.stalkClosedPointTo_fromSpecStalk]
  exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective

theorem n2b_field_generic_image {L : Type} [Field L] {Y : Scheme} [IsIntegral Y]
    (f : Spec (CommRingCat.of L) ⟶ Y) [IsDominant f] :
    f (IsLocalRing.closedPoint L) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  have hpoint : (IsLocalRing.closedPoint L : Spec (CommRingCat.of L)) =
      genericPoint (Spec (CommRingCat.of L)) := Subsingleton.elim _ _
  rw [hpoint]
  convert (genericPoint_spec (Spec (CommRingCat.of L))).image f.continuous using 1
  rw [Set.image_univ, f.denseRange.closure_range]

theorem n2b_normalization_finite {L : Type} [Field L]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (f : Spec (CommRingCat.of L) ⟶ Y.left) [QuasiCompact f] [QuasiSeparated f]
    (hg : f (IsLocalRing.closedPoint L) = genericPoint Y.left)
    (hf : (Scheme.stalkClosedPointTo f).hom.Finite) :
    IsFinite (s2b_normalizationMap Y f).left := by
  apply s2v_normalization_finite_of_field_integralClosure f
  intro U hfull
  have hU : Nonempty U.1 := by
    refine ⟨⟨f (IsLocalRing.closedPoint L), ?_⟩⟩
    have hm : IsLocalRing.closedPoint L ∈ f ⁻¹ᵁ U.1 := by rw [hfull]; trivial
    exact hm
  letI := hU
  letI : Algebra ℂ Γ(Y.left, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y.left, U.1) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    change ((Y.hom.appLE ⊤ U.1 (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
    refine RingHom.FiniteType.comp ?_ ?_
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) Y.hom inferInstance
        ⟨⊤, isAffineOpen_top _⟩ U (by simp)
    · exact RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).surjective
  let ψ : Y.left.functionField ⟶ CommRingCat.of L :=
    eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫ Scheme.stalkClosedPointTo f
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite Y.left.functionField L := by
    apply RingHom.finite_algebraMap.mp
    exact hf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (eqToHom (congrArg Y.left.presheaf.stalk hg.symm))).surjective)
  letI := (f.app U.1 ≫ (s2v_fieldSourceSectionsIso f U.1 hfull).hom).hom.toAlgebra
  have ht : Y.left.germToFunctionField U.1 ≫ ψ =
      f.app U.1 ≫ (s2v_fieldSourceSectionsIso f U.1 hfull).hom := by
    dsimp only [ψ, Scheme.germToFunctionField]
    rw [← Category.assoc, n2a_germ_transport]
    · exact Scheme.germ_stalkClosedPointTo f U.1 _
    · exact hg
  haveI : IsScalarTower Γ(Y.left, U.1) Y.left.functionField L :=
    .of_algebraMap_eq fun x => congrArg (fun g : Γ(Y.left, U.1) ⟶ CommRingCat.of L => g.hom x) ht.symm
  haveI := functionField_isFractionRing_of_isAffineOpen Y.left U.1 U.2
  exact s2v_finite_integralClosure_coveringField (k := ℂ)
    (A := Γ(Y.left, U.1)) (F := Y.left.functionField) (L := L)

end HodgeLean.Foundations.Program
