import HodgeLean.Foundations.QuotientDuality.ProperCycleManifoldChartOrientation
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.LocalOrientation

/-! # Original smooth complex orientation in every specified holomorphic chart -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical original smooth complex orientation is the exact normalized class in every chart whose coordinates satisfy the original analytification holomorphic predicate.
Source: f4_isHolFun_iff_contMDiffOn; properCycle_manifold_chart_local_class_eq; complexLocalOrientation_eq_localClassOfChart.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_holomorphic_chart_orientation
    (V : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d V.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (e : OpenPartialHomeomorph (ComplexPoint V) (Fin d → ℂ))
    (he : ∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i))
    (x : ComplexPoint V) (hx : x ∈ e.source) :
    complexLocalOrientation V d x = localClassOfChart d e x hx := by
  have hE : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e e.source := by
    apply contMDiffOn_pi_space.mpr
    intro i
    exact (f4_isHolFun_iff_contMDiffOn V d (fun z => e z i) e.open_source).mp (he i)
  rw [complexLocalOrientation_eq_localClassOfChart]
  exact properCycle_manifold_chart_local_class_eq (localChart V d x) e
    contMDiffOn_chart hE x (mem_localChart_source V d x) hx

end HodgeLean.Foundations.QuotientDuality
