import HodgeLean.Foundations.TubularEuler.AffineIdealCompositeSectionValueHelpers
import HodgeLean.Foundations.TubularEuler.AffineConormalSectionPointHelpers
import HodgeLean.Foundations.TubularEuler.AffineConormalFibreEvaluationHelpers

/-! # Original affine conormal section values in the named fibre comparison

The actual ideal section specializes to the pure tensor of its original ideal element.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

theorem affineConormalFibreIdealSectionsIso_section_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    (affineConormalFibreIdealSectionsIso R S φ ψ).hom
      (i1_module_pointValue (Conormal.sheaf (Spec.map φ))
        (affineConormalSection R S φ u) (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom]
        (show (moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ)) from
          (s2e_affine_ideal_sections_equiv R S φ).symm u) := by
  letI : IsIso (Conormal.idealModule (Spec.map φ)).fromTildeΓ :=
    s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  apply affineConormalFibreIdealSectionsIso_apply_eq R S φ ψ
  exact (congrArg
    (fun x : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))) =>
      (affineCompositeModuleFibreIso R S φ ψ (Conormal.idealModule (Spec.map φ))).hom x)
    (affineConormalSection_pointValue_eq R S φ ψ u)).trans
    (affineIdealCompositeSection_value R S φ ψ u)

#print axioms affineConormalFibreIdealSectionsIso_section_value

end HodgeLean.Foundations.TubularEuler
