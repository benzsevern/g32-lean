import HodgeLean.Foundations.TubularEuler.AnalyticStalkDifferentialHelpers

/-! # Differentials of the original regular chart coordinates

The chosen complex chart coordinates are evaluations of specified regular
sections. Their differentials are the actual coordinate covectors.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

theorem regularChartCoordinate_hasFDerivAt
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) (i : Fin d) :
    HasFDerivAt (fun a : Fin d → ℂ =>
      Point.evaluate (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
        ((ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateSection i)
        ((chartAt (Fin d → ℂ) z).symm a))
      (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ) ((chartAt (Fin d → ℂ) z) x) := by
  let e := chartAt (Fin d → ℂ) z
  have he : (fun a : Fin d → ℂ =>
      Point.evaluate (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
        ((ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateSection i) (e.symm a))
      =ᶠ[𝓝 (e x)] fun a => a i := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with a ha
    have h := ComplexPoint.localChart_apply_component_eq_evaluate X d z
      (e.symm a) (e.map_target ha) i
    change (e (e.symm a)) i = _ at h
    rw [e.right_inv ha] at h
    exact h.symm
  exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt).congr_of_eventuallyEq
    he

#print axioms regularChartCoordinate_hasFDerivAt

end HodgeLean.Foundations.TubularEuler
