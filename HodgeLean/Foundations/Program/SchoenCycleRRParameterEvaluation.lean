import HodgeLean.Foundations.Program.SchoenCycleLineChartEvaluation
import HodgeLean.Foundations.Program.HurwitzPrymRRForm

/-! # Actual regular parameters in the differential line chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The extended native curve chart has the same forward coordinate map.
Source: Mathlib, extChartAt_coe; HodgeConjecture,
AlgebraicGeometry.ComplexPoint.localChart. -/
theorem s2e_native_curve_extChart_apply
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (p q : ComplexPoint X) :
    extChartAt 𝓘(ℂ, Fin 1 → ℂ) p q = ComplexPoint.localChart X 1 p q := by
  rfl

/-- The extended native curve chart has the same inverse coordinate map.
Source: Mathlib, extChartAt_coe_symm; HodgeConjecture,
AlgebraicGeometry.ComplexPoint.localChart. -/
theorem s2e_native_curve_extChart_symm_apply
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (p : ComplexPoint X) (v : Fin 1 → ℂ) :
    (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p).symm v =
      (ComplexPoint.localChart X 1 p).symm v := by
  rfl

/-- In the exact differential line chart the actual regular parameter is a
nonzero scalar multiple of its scalar coordinate.
Source: Forster, Lectures on Riemann Surfaces, §9.4;
HodgeConjecture, AlgebraicGeometry.ComplexPoint.localChart. -/
theorem s2e_native_curve_parameter_rr_chart
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
    ∃ (U : X.left.Opens) (hp : p.underlying ∈ U) (s : Γ(X.left, U)),
      X.left.presheaf.germ U p.underlying hp s = s2e_native_curve_parameter X p ∧
      (L 1) 0 ≠ 0 ∧
      (fun z : ℂ => Point.evaluate U s
        ((extChartAt 𝓘(ℂ, Fin 1 → ℂ) p).symm
          (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p p + L z))) =ᶠ[nhds 0]
        (fun z => (L 1) 0 * z) := by
  dsimp only
  simpa only [s2e_native_curve_extChart_apply, s2e_native_curve_extChart_symm_apply] using
    s2e_native_curve_parameter_linear_chart X p
      (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ))

end HodgeLean.Foundations.Program
