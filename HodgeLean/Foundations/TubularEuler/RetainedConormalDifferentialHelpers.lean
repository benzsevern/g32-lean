import HodgeLean.Foundations.TubularEuler.AffineIdealDifferentialHelpers
import HodgeLean.Foundations.TubularEuler.ActualConormalFibreAffineHelpers

/-! # Analytic differentiation on the retained conormal fibre

The map uses the actual affine ideal presentation of the original immersion.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters HodgeLean.Foundations.BundleThom

def retainedAffineConormalDifferential
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    i1_conormalFibre j.left x →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ) :=
  (affineConormalTensorDifferential X Y j d V hV x hx z hz).comp
    (actualConormalFibreAffineCotangentIso j.left V hV x hx).toLinearEquiv.toLinearMap

#print axioms retainedAffineConormalDifferential
end HodgeLean.Foundations.TubularEuler
