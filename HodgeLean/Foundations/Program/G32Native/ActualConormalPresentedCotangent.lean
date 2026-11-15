import HodgeLean.Foundations.Program.G32Native.ModuleAffineCanonicalPresentation
import HodgeLean.Foundations.TubularEuler.ActualConormalFibreFactorHelpers

/-! # The retained cotangent comparison at its specified spectrum point -/
noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- The retained affine cotangent isomorphism factors through the
specified-point fibre transport before taking cotangent tensors.
Source: `actualConormalFibreAffineCotangentIso_eq` and
`moduleAffineFibreChartIso_eq_presented`. -/
theorem actualConormalFibreAffineCotangentIso_eq_presented
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}}
    (j : Q.left ⟶ W) [IsClosedImmersion j]
    (A : W.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    let R := W.presheaf.obj (.op A)
    let S := Q.left.presheaf.obj (.op (j ⁻¹ᵁ A))
    let φ : R ⟶ S := j.app A
    let b := ComplexPoint.liftToOpen Q (j ⁻¹ᵁ A) x hx ≫ (hA.preimage j).isoSpec.hom
    letI : Algebra R ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
    actualConormalFibreAffineCotangentIso j A hA x hx =
      moduleAffinePresentedFibreIso (Conormal.sheaf j) (j ⁻¹ᵁ A) (hA.preimage j)
        (Conormal.sheaf (Spec.map φ)) (actualConormalAffineChartIso j A hA) x hx
        (Spec.map (Spec.preimage b)) (Spec.map_preimage b).symm ≪≫
      affineConormalFibreCotangentIso R S φ (Spec.preimage b) := by
  rfl

#print axioms actualConormalFibreAffineCotangentIso_eq_presented
end HodgeLean.Foundations.TubularEuler
