import HodgeLean.Foundations.TubularEuler.NormalGeometryInputs

/-! # Complex multiplication and original chart transition derivatives

The complex analytic transition maps determine their real derivatives by scalar restriction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

theorem complexPoint_chart_transition_fderiv_mul_I
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z z' p : ComplexPoint X)
    (hp : p ∈ (chartAt (Fin d → ℂ) z).source)
    (hp' : p ∈ (chartAt (Fin d → ℂ) z').source) (u : Fin d → ℂ) :
    fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
        ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p)
        (Complex.I • u) =
      Complex.I • fderiv ℝ (fun a => (chartAt (Fin d → ℂ) z')
        ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p) u := by
  have ha : (chartAt (Fin d → ℂ) z) p ∈
      ((chartAt (Fin d → ℂ) z).symm.trans (chartAt (Fin d → ℂ) z')).source := by
    exact ⟨(chartAt (Fin d → ℂ) z).map_source hp, by
      change (chartAt (Fin d → ℂ) z).symm ((chartAt (Fin d → ℂ) z) p) ∈
        (chartAt (Fin d → ℂ) z').source
      simpa only [(chartAt (Fin d → ℂ) z).left_inv hp] using hp'⟩
  have hc : DifferentiableAt ℂ (fun a => (chartAt (Fin d → ℂ) z')
      ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p) :=
    (ComplexPoint.analyticAt_localChart_transition X d z z' ha).differentiableAt
  rw [(hc.hasFDerivAt.restrictScalars ℝ).fderiv]
  exact (fderiv ℂ (fun a => (chartAt (Fin d → ℂ) z')
    ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) p)).map_smul _ _

#print axioms complexPoint_chart_transition_fderiv_mul_I

end HodgeLean.Foundations.TubularEuler
