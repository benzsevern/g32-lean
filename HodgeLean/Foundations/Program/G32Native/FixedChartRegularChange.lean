import HodgeLean.Foundations.Program.G32Native.ChartDerivativeIdentities

/-! # Actual regular equation derivatives under a fixed change of chart -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The original point-chart derivative of a regular equation is its fixed
chart derivative composed with the actual coordinate transition derivative. -/
theorem regular_fderiv_change_to_point_chart
    (W : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (p y : ComplexPoint W) (U : W.left.Opens) (s : Γ(W.left, U))
    (hyU : y ∈ Point.overOpen U) (hyp : y ∈ (localChart W d p).source) :
    fderiv ℂ (fun v => Point.evaluate U s ((localChart W d y).symm v))
        (localChart W d y y) =
      (fderiv ℂ (fun v => Point.evaluate U s ((localChart W d p).symm v))
        (localChart W d p y)).comp
      (fderiv ℂ (fun v => localChart W d p ((localChart W d y).symm v))
        (localChart W d y y)) := by
  let ep := localChart W d p
  let ey := localChart W d y
  let F := fun v => Point.evaluate U s (ep.symm v)
  let T := fun v => ep (ey.symm v)
  have hys : y ∈ ey.source := mem_localChart_source W d y
  have ht : T (ey y) = ep y := by
    change ep (ey.symm (ey y)) = ep y
    rw [ey.left_inv hys]
  have hF : AnalyticAt ℂ F (T (ey y)) := by
    rw [ht]
    apply analyticAt_localChart_symm_evaluate W d p (ep.map_source hyp) U s
    change ep.symm (ep y) ∈ Point.overOpen U
    rw [ep.left_inv hyp]
    exact hyU
  have hT : AnalyticAt ℂ T (ey y) := by
    apply analyticAt_localChart_transition W d y p
    change ey y ∈ ey.target ∧ ey.symm (ey y) ∈ ep.source
    exact ⟨ey.map_source hys, by simpa only [ey.left_inv hys] using hyp⟩
  have hc : Tendsto ey.symm (𝓝 (ey y)) (𝓝 y) := by
    simpa only [ContinuousAt, ey.left_inv hys] using ey.continuousAt_symm (ey.map_source hys)
  have hnear : ∀ᶠ v in 𝓝 (ey y), ey.symm v ∈ ep.source := hc (ep.open_source.mem_nhds hyp)
  have heq : F ∘ T =ᶠ[𝓝 (ey y)] (fun v => Point.evaluate U s (ey.symm v)) := by
    filter_upwards [hnear] with v hv
    change Point.evaluate U s (ep.symm (ep (ey.symm v))) = _
    rw [ep.left_inv hv]
  have hd : fderiv ℂ (F ∘ T) (ey y) =
      fderiv ℂ (fun v => Point.evaluate U s (ey.symm v)) (ey y) := heq.fderiv_eq
  have hcomp := fderiv_comp (ey y) hF.differentiableAt hT.differentiableAt
  rw [ht] at hcomp
  exact hd.symm.trans hcomp

#print axioms regular_fderiv_change_to_point_chart
end HodgeLean.Foundations.Program.G32Native
