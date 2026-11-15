import HodgeLean.Foundations.TubularEuler.AffineConormalTensorEvaluationHelpers
import HodgeLean.Foundations.TubularEuler.AffineConormalSectionValueHelpers
import HodgeLean.Foundations.TubularEuler.AffineIdealTensorHelpers

/-! # Original affine conormal section values in the original ideal tensor

The named fibre comparison retains the supplied ideal element under scalar extension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affineConormalFibreIdealTensorIso_section_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    (affineConormalFibreIdealTensorIso R S φ ψ).hom
      (i1_module_pointValue (Conormal.sheaf (Spec.map φ))
        (affineConormalSection R S φ u) (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R] u := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  apply affineConormalFibreIdealTensorIso_apply_eq R S φ ψ
  · exact affineConormalFibreIdealSectionsIso_section_value R S φ ψ u
  · exact affineIdealTensor_sections_value R S φ ψ u

#print axioms affineConormalFibreIdealTensorIso_section_value

end HodgeLean.Foundations.TubularEuler
