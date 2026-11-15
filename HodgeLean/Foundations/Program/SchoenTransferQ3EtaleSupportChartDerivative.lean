import HodgeLean.Foundations.Program.SchoenTransferQ3SupportChartCoordinates
import HodgeLean.Adapters.CycleClassSmoothCharts

/-! The derivative of the actual tangential map on the canonical support section. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual etale support restriction gives an invertible tangential
coordinate derivative on the canonical zero-normal section. -/
theorem s4_q3_etale_support_tangential_derivative
    (X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    [Etale (i ≫ h).left] (z : ComplexPoint D) :
    Function.Bijective (fderiv ℂ
      (fun u => localChart T r (Point.map (i ≫ h) z)
        (Point.map h ((closedImmersionHolomorphicFlatteningChart X D i r d z).symm (u, 0))))
      (localChart D r z z)) := by
  have heq : (fun u => localChart T r (Point.map (i ≫ h) z)
        (Point.map h ((closedImmersionHolomorphicFlatteningChart X D i r d z).symm (u, 0))))
      =ᶠ[𝓝 (localChart D r z z)] inclusionInComplexCharts T D (i ≫ h) r r z := by
    filter_upwards [s4_q3_support_chart_inverse_zero_eventually X D i r d z] with u hu
    rw [hu]
    simp only [inclusionInComplexCharts, Point.map_comp_apply]
  rw [heq.fderiv_eq]
  exact ccm5_etale_chart_derivative_bijective D T (i ≫ h) r r z

/-- The actual ambient morphism, expressed in the canonical inverse normal
chart and the chosen target chart, is analytic at the support point. -/
theorem s4_q3_tangential_map_analytic_in_normal_chart
    (X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    (z : ComplexPoint D) :
    AnalyticAt ℂ (fun v => localChart T r (Point.map (i ≫ h) z)
      (Point.map h ((closedImmersionHolomorphicFlatteningChart X D i r d z).symm v)))
      (closedImmersionHolomorphicFlatteningChart X D i r d z (Point.map i z)) := by
  rw [Point.map_comp_apply]
  let x := Point.map i z
  let N := closedImmersionNormalCoordinateChange X D i r d z
  let e := closedImmersionHolomorphicFlatteningChart X D i r d z
  have hN : AnalyticAt ℂ N.symm (e x) := by
    rw [closedImmersionHolomorphicFlatteningChart_center]
    exact analyticAt_closedImmersionNormalCoordinateChange_symm X D i r d z
  have hval : N.symm (e x) = localChart X d x x := by
    rw [closedImmersionHolomorphicFlatteningChart_center,
      ← closedImmersionNormalCoordinateChange_center X D i r d z]
    exact N.left_inv (closedImmersionNormalCoordinateChange_mem_source X D i r d z)
  have hmap : AnalyticAt ℂ (inclusionInComplexCharts T X h d r x) (N.symm (e x)) := by
    rw [hval]
    exact analyticAt_inclusionInComplexCharts T X h d r x
  convert hmap.comp hN using 1
  funext v
  rw [closedImmersionHolomorphicFlatteningChart_symm_apply]
  rfl

end HodgeLean.Foundations.Program
