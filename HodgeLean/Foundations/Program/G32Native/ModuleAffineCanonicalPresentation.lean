import HodgeLean.Foundations.Program.G32Native.ModuleAffinePresentedFibre

/-! # The canonical affine presentation as a specified-point comparison -/
noncomputable section
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

/-- The original affine fibre isomorphism is the specified-point
comparison at its canonical spectrum presentation.
Source: definitions `moduleAffineFibreChartIso` and
`moduleAffinePresentedFibreIso`. -/
theorem moduleAffineFibreChartIso_eq_presented
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (N : (Spec (Q.left.presheaf.obj (.op U))).Modules)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj ((Scheme.Modules.pullback U.ι).obj M) ≅ N)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    moduleAffineFibreChartIso M U hU N e x hx =
      moduleAffinePresentedFibreIso M U hU N e x hx
        (Spec.map (Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)))
        (Spec.map_preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom)).symm := by
  rfl

#print axioms moduleAffineFibreChartIso_eq_presented
end HodgeLean.Foundations.TubularEuler
