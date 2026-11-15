import HodgeLean.Foundations.Program.G32Native.OriginalRegularConormalTensor
import HodgeLean.Foundations.TubularEuler.NormalGeneratorLocalization

/-! # Differentiating an original descended regular conormal value -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

/-- On the original value of a descended ideal equation the retained
conormal differential is the derivative of that equation in the specified
ambient chart.
Source: `originalRegularConormalValue_tensor` and
`affineConormalTensorDifferential_regular_section`. -/
theorem retainedAffineConormalDifferential_regular_value
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (A : X.left.Opens) (hA : IsAffineOpen A)
    (u : RingHom.ker (j.left.app A).hom)
    (x : ComplexPoint Y) (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ A))
    (z : ComplexPoint X)
    (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    retainedAffineConormalDifferential X Y j d A hA x hx z hz
      (originalRegularConormalValue j.left A hA u x hx) =
      fderiv ℂ (fun a : Fin d → ℂ =>
        Point.evaluate A u.val ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) (Point.map j x)) := by
  have ht := originalRegularConormalValue_tensor j.left A hA u x hx
  have h := retained_conormal_generator_localization X Y j d A hA x hx z hz u 1
    (originalRegularConormalValue j.left A hA u x hx)
    ((moduleIsoValue_toLinearEquiv _ _).symm.trans ht)
  simpa only [one_smul] using h

#print axioms retainedAffineConormalDifferential_regular_value
end HodgeLean.Foundations.TubularEuler
