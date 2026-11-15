import HodgeLean.Foundations.Program.SchoenCycleRegularChartAnalytic
import HodgeLean.Foundations.Program.SchoenCycleGermEvaluation

/-! # Exact section germs on a native chart of any smooth dimension -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The centered native chart parameter tends to its actual complex scheme point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Mathlib, OpenPartialHomeomorph.continuousAt_symm. -/
theorem s2e_centered_native_chart_tendsto
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    Tendsto (fun z : Fin d → ℂ => (ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z)) (𝓝 0) (𝓝 p) := by
  let e := ComplexPoint.localChart X d p
  have hp : p ∈ e.source := ComplexPoint.mem_localChart_source X d p
  have ht : Tendsto (fun z : Fin d → ℂ => e p + z) (𝓝 0) (𝓝 (e p)) := by
    have hc : Continuous (fun z : Fin d → ℂ => e p + z) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : Fin d → ℂ)
  have h := (e.continuousAt_symm (e.map_source hp)).tendsto.comp ht
  change Tendsto (fun z : Fin d → ℂ => e.symm (e p + z)) (𝓝 0)
    (𝓝 (e.symm (e p))) at h
  change Tendsto (fun z : Fin d → ℂ => e.symm (e p + z)) (𝓝 0) (𝓝 p)
  simpa only [e.left_inv hp] using h

/-- Equal algebraic section germs have exactly the same germ on the full native chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.1 and II.2. -/
theorem s2e_equal_germs_native_chart_evaluate
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U V : X.left.Opens)
    (hpU : p.underlying ∈ U) (hpV : p.underlying ∈ V)
    (s : Γ(X.left, U)) (t : Γ(X.left, V))
    (h : X.left.presheaf.germ U p.underlying hpU s =
      X.left.presheaf.germ V p.underlying hpV t) :
    (fun z : Fin d → ℂ => Point.evaluate U s ((ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z))) =ᶠ[𝓝 0]
    (fun z : Fin d → ℂ => Point.evaluate V t ((ComplexPoint.localChart X d p).symm
      (ComplexPoint.localChart X d p p + z))) := by
  exact (s2e_centered_native_chart_tendsto X d p).eventually
    (s2e_equal_germs_eventually_evaluate X p U V hpU hpV s t h)

end HodgeLean.Foundations.Program
