import HodgeLean.Foundations.TubularEuler.AffineConormalCotangentEvaluationHelpers
import HodgeLean.Foundations.TubularEuler.AffineConormalTensorSectionValueHelpers

/-! # Original affine conormal section values in the named cotangent fibre

The full named affine fibre comparison sends the original ideal section to its cotangent pure tensor.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affineConormalFibreCotangentIso_section_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    (affineConormalFibreCotangentIso R S φ ψ).hom
      (i1_module_pointValue (Conormal.sheaf (Spec.map φ))
        (affineConormalSection R S φ u) (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  apply affineConormalFibreCotangentIso_apply_eq R S φ ψ
  · exact affineConormalFibreIdealTensorIso_section_value R S φ ψ u
  · exact conormalFibreTensorEquiv_tmul (RingHom.ker φ.hom)
      (affineConormalScalar_killsIdeal R S φ ψ) 1 u

#print axioms affineConormalFibreCotangentIso_section_value

end HodgeLean.Foundations.TubularEuler
