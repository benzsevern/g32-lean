import HodgeLean.Foundations.TubularEuler.AffineCompositeSectionValueHelpers

/-! # Original affine ideal sections in the composite module fibre

The canonical pullback section retains its original ideal element in scalar extension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

theorem affineIdealCompositeSection_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : IsIso (Conormal.idealModule (Spec.map φ)).fromTildeΓ :=
      s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    (affineCompositeModuleFibreIso R S φ ψ (Conormal.idealModule (Spec.map φ))).hom
      (i1_module_pointValue
        ((Scheme.Modules.pullback (Spec.map φ)).obj (Conormal.idealModule (Spec.map φ)))
        (i1_module_sectionPullback (Spec.map φ) (Conormal.idealModule (Spec.map φ))
          (affineIdealModuleSection R S φ u)) (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom]
        (show (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ)) from
          (s2e_affine_ideal_sections_equiv R S φ).symm u) := by
  letI : IsIso (Conormal.idealModule (Spec.map φ)).fromTildeΓ :=
    s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  have h := affineCompositeModuleFibreIso_section_apply R S φ ψ
    (Conormal.idealModule (Spec.map φ)) (affineIdealModuleSection R S φ u)
  have ht := congrArg
    (fun m : (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ)) =>
      (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom] m) (affineIdealModuleSection_top R S φ u)
  exact h.trans ht

#print axioms affineIdealCompositeSection_value

end HodgeLean.Foundations.TubularEuler
