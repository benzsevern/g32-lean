import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation

/-! # Regular equation derivatives in a fixed ambient chart -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The derivative of an actual regular function varies continuously in any
fixed ambient chart throughout its original domain of evaluation. -/
theorem continuousOn_fixedChart_regular_fderiv
    (W : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (p : ComplexPoint W) (U : W.left.Opens) (s : Γ(W.left, U)) :
    ContinuousOn
      (fun y => fderiv ℂ (fun v => Point.evaluate U s ((localChart W d p).symm v))
        (localChart W d p y))
      ((Point.overOpen U : Set (ComplexPoint W)) ∩ (localChart W d p).source) := by
  intro y hy
  let e := localChart W d p
  have ha : AnalyticAt ℂ (fun v => Point.evaluate U s (e.symm v)) (e y) := by
    apply analyticAt_localChart_symm_evaluate W d p (e.map_source hy.2) U s
    change e.symm (e y) ∈ Point.overOpen U
    rw [e.left_inv hy.2]
    exact hy.1
  have hc := (ha.contDiffAt (n := 1)).continuousAt_fderiv (by simp)
  exact (hc.comp (e.continuousAt hy.2)).continuousWithinAt

#print axioms continuousOn_fixedChart_regular_fderiv
end HodgeLean.Foundations.Program.G32Native
