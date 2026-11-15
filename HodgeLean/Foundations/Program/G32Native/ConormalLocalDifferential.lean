import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation

/-! # Coordinate derivatives of regular equations along smooth immersions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open scoped Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- A regular equation with zero pullback has coordinate derivative zero on
all tangent vectors coming from the source. -/
theorem regularEquation_derivative_tangent
    (W Q : Over (Spec ↧ℂ)) (i : Q ⟶ W) (m d : ℕ)
    [SmoothOfRelativeDimension m Q.hom] [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (s : Γ(W.left, U))
    (hx : Point.map i x ∈ Point.overOpen U) (hs : i.left.app U s = 0)
    (v : Fin m → ℂ) :
    fderiv ℂ (fun w => Point.evaluate U s ((localChart W d (Point.map i x)).symm w))
      (localChart W d (Point.map i x) (Point.map i x))
      (fderiv ℂ (inclusionInComplexCharts W Q i m d x)
        (localChart Q m x x) v) = 0 := by
  let eQ := localChart Q m x
  let eW := localChart W d (Point.map i x)
  let g := inclusionInComplexCharts W Q i m d x
  let f := fun w => Point.evaluate U s (eW.symm w)
  have hxQ : x ∈ eQ.source := mem_localChart_source Q m x
  have hxW : Point.map i x ∈ eW.source := mem_localChart_source W d (Point.map i x)
  have hc : ContinuousAt (fun w => Point.map i (eQ.symm w)) (eQ x) :=
    (Point.continuous_map i).continuousAt.comp (eQ.continuousAt_symm (eQ.map_source hxQ))
  have hW : ∀ᶠ w in 𝓝 (eQ x), Point.map i (eQ.symm w) ∈ eW.source := by
    apply hc (eW.open_source.mem_nhds _)
    change Point.map i (eQ.symm (eQ x)) ∈ eW.source
    rw [eQ.left_inv hxQ]
    exact hxW
  have heq : (f ∘ g) =ᶠ[𝓝 (eQ x)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hW] with w hw
    change Point.evaluate U s (eW.symm (eW (Point.map i (eQ.symm w)))) = 0
    rw [eW.left_inv hw, Point.evaluate_map, hs]
    unfold Point.evaluate
    split <;> simp only [map_zero]
  have hf : AnalyticAt ℂ f (g (eQ x)) := by
    rw [show g (eQ x) = eW (Point.map i x) from
      inclusionInComplexCharts_at_center W Q i m d x]
    apply analyticAt_localChart_symm_evaluate W d (Point.map i x) (eW.map_source hxW) U s
    change eW.symm (eW (Point.map i x)) ∈ Point.overOpen U
    rw [eW.left_inv hxW]
    exact hx
  have hg : AnalyticAt ℂ g (eQ x) := analyticAt_inclusionInComplexCharts W Q i m d x
  have hz : fderiv ℂ (f ∘ g) (eQ x) = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
  rw [fderiv_comp (eQ x) hf.differentiableAt hg.differentiableAt] at hz
  have hv := DFunLike.congr_fun hz v
  change fderiv ℂ f (g (eQ x)) (fderiv ℂ g (eQ x) v) = 0 at hv
  simpa only [g, eQ, inclusionInComplexCharts_at_center] using hv

#print axioms regularEquation_derivative_tangent
end HodgeLean.Foundations.Program.G32Native
