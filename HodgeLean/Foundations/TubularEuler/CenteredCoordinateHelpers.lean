import HodgeLean.Foundations.TubularEuler.AnalyticCoordinateDifferentialHelpers
import HodgeLean.Foundations.TubularEuler.AnalyticStalkDifferentialAlgebraHelpers

/-! # Actual regular parameters centered at a complex point

The sections use the selected algebraic chart and its original coordinate open.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem regularChartCoordinate_mem_open
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) :
    x.underlying ∈ (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen := by
  have h := ComplexPoint.mem_coordinateNeighborhood_of_mem_localChart_source X d z x hx
  change x.underlying ∈ (ComplexPoint.localEtaleCoordinates X d z).neighborhood at h
  simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using h

def regularChartCenteredSection
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (i : Fin d) :
    Γ(X.left, (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen) :=
  (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateSection i -
    a3b4a_gysin_sectionConst X.hom
      (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
      ((chartAt (Fin d → ℂ) z) x i)

theorem regularChartCenteredSection_evaluate
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x p : ComplexPoint X) (hp : p ∈ (chartAt (Fin d → ℂ) z).source) (i : Fin d) :
    Point.evaluate (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
      (regularChartCenteredSection X d z x i) p =
        (chartAt (Fin d → ℂ) z) p i - (chartAt (Fin d → ℂ) z) x i := by
  rw [regularChartCenteredSection, a3b4g_evaluate_sub,
    a3b4a_gysin_evaluate_sectionConst X.hom _ p (regularChartCoordinate_mem_open X d z p hp)]
  rw [← ComplexPoint.localChart_apply_component_eq_evaluate X d z p hp i]
  rfl

theorem regularChartCenteredSection_hasFDerivAt
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) (i : Fin d) :
    HasFDerivAt (fun a : Fin d → ℂ =>
      Point.evaluate (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
        (regularChartCenteredSection X d z x i) ((chartAt (Fin d → ℂ) z).symm a))
      (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ) ((chartAt (Fin d → ℂ) z) x) := by
  let e := chartAt (Fin d → ℂ) z
  have he : (fun a : Fin d → ℂ =>
      Point.evaluate (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
        (regularChartCenteredSection X d z x i) (e.symm a))
      =ᶠ[𝓝 (e x)] fun a => a i - e x i := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with a ha
    rw [regularChartCenteredSection_evaluate X d z x (e.symm a) (e.map_target ha) i]
    rw [e.right_inv ha]
  exact ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt.sub_const
    (e x i)).congr_of_eventuallyEq he

def regularChartCenteredGerm
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) (i : Fin d) :
    X.left.presheaf.stalk x.underlying :=
  X.left.presheaf.germ (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
    x.underlying (regularChartCoordinate_mem_open X d z x hx)
    (regularChartCenteredSection X d z x i)

theorem regularChartCenteredGerm_differential
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) (i : Fin d) :
    actualStalkDifferential X d z x hx (regularChartCenteredGerm X d z x hx i) =
      ContinuousLinearMap.proj i := by
  rw [regularChartCenteredGerm, actualStalkDifferential_eq_section]
  exact (regularChartCenteredSection_hasFDerivAt X d z x hx i).fderiv

theorem regularChartCenteredGerm_span
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) :
    Ideal.span (Set.range (regularChartCenteredGerm X d z x hx)) =
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  let U := (ComplexPoint.localEtaleCoordinates X d z).ambientCoordinateOpen
  let f := regularChartCenteredSection X d z x
  have hf : HasFDerivAt (fun a : Fin d → ℂ => fun i =>
      Point.evaluate U (f i) ((chartAt (Fin d → ℂ) z).symm a))
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) ((chartAt (Fin d → ℂ) z) x) := by
    apply hasFDerivAt_pi''
    intro i
    simpa only [ContinuousLinearMap.comp_id] using
      regularChartCenteredSection_hasFDerivAt X d z x hx i
  apply a3b4g_span_germ_eq_maximalIdeal_of_isUnit_fderiv X x z hx U
    (regularChartCoordinate_mem_open X d z x hx) f
  · intro i
    rw [regularChartCenteredSection_evaluate X d z x x hx i, sub_self]
  · rw [hf.fderiv]
    exact isUnit_one

#print axioms regularChartCenteredGerm_span

#print axioms regularChartCenteredGerm_differential

#print axioms regularChartCenteredSection_hasFDerivAt

#print axioms regularChartCenteredSection_evaluate

#print axioms regularChartCoordinate_mem_open

end HodgeLean.Foundations.TubularEuler
