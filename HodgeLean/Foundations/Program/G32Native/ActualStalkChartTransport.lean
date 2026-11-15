import HodgeLean.Foundations.Program.G32Native.PartialChartDifferentialTransport
import HodgeLean.Foundations.TubularEuler.AnalyticStalkDifferentialHelpers

/-! # Original local-ring covectors under the actual ambient chart transition

The representative section is chosen from the same stalk germ in both charts.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

/-- The analytic differential of an actual scheme stalk germ transforms by the
derivative of the original complex coordinate transition.
Source: `actualStalkDifferential_hasFDerivAt_section`,
`ComplexPoint.analyticAt_localChart_transition`, and the chain rule.
HC no distance; AV milestone no distance. -/
theorem actualStalkDifferential_change_chart
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z z' x : ComplexPoint X)
    (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (hx' : x ∈ (chartAt (Fin d → ℂ) z').source)
    (h : X.left.presheaf.stalk x.underlying) :
    actualStalkDifferential X d z x hx h =
      (actualStalkDifferential X d z' x hx' h).comp
        (fderiv ℂ (fun a => (chartAt (Fin d → ℂ) z')
          ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) x)) := by
  obtain ⟨A, hA, s, hs⟩ := X.left.presheaf.exists_germ_eq h
  let a := chartAt (Fin d → ℂ) z
  let b := chartAt (Fin d → ℂ) z'
  have hsource : a x ∈ (a.symm.trans b).source := by
    refine ⟨a.map_source hx, ?_⟩
    change a.symm (a x) ∈ b.source
    rwa [a.left_inv hx]
  have htrA : AnalyticAt ℂ (fun t => b (a.symm t)) (a x) :=
    ComplexPoint.analyticAt_localChart_transition X d z z' hsource
  have heq := partialChart_differential_transport a b x hx hx'
    (fun y => Point.evaluate A s y) _ _ _
    (actualStalkDifferential_hasFDerivAt_section X d z x hx A hA s)
    (actualStalkDifferential_hasFDerivAt_section X d z' x hx' A hA s)
    htrA.hasStrictFDerivAt.hasFDerivAt
  simpa only [hs, a, b] using heq

#print axioms actualStalkDifferential_change_chart

end HodgeLean.Foundations.TubularEuler
