import HodgeLean.Foundations.TubularEuler.AffineDifferentialInjectivityHelpers
import HodgeLean.Foundations.TubularEuler.RetainedConormalDifferentialHelpers

/-! # Faithfulness of the retained differential for general smooth dimensions -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

theorem retained_conormal_differential_injective
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    Function.Injective (retainedAffineConormalDifferential X Y j d A hA x hx z hz) := by
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth m Y.hom
  exact (affineConormalTensorDifferential_injective X Y j d A hA x hx z hz).comp
    (actualConormalFibreAffineCotangentIso j.left A hA x hx).toLinearEquiv.injective

#print axioms retained_conormal_differential_injective
end HodgeLean.Foundations.TubularEuler
