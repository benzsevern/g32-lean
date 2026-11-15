import HodgeLean.Foundations.Program.SchoenCycleLineChartEvaluation
import Mathlib.Analysis.Analytic.Linear

/-! # Analytic regular sections on centered curve chart lines -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A regular section on an actual curve neighbourhood evaluates analytically
on every centered linear coordinate line.
Source: HodgeConjecture,
AlgebraicGeometry.ComplexPoint.analyticAt_localChart_symm_evaluate. -/
theorem s2e_regular_section_linear_chart_analytic
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(X.left, U)) (L : ℂ ≃L[ℂ] (Fin 1 → ℂ)) :
    AnalyticAt ℂ (fun z : ℂ => Point.evaluate U s
      ((ComplexPoint.localChart X 1 p).symm
        (ComplexPoint.localChart X 1 p p + L z))) 0 := by
  let e := ComplexPoint.localChart X 1 p
  have he : p ∈ e.source := ComplexPoint.mem_localChart_source X 1 p
  have hV : e.symm (e p) ∈ Point.overOpen U := by
    rw [e.left_inv he]
    exact hp
  have ha := ComplexPoint.analyticAt_localChart_symm_evaluate X 1 p
    (e.map_source he) U s hV
  have hb : AnalyticAt ℂ (fun z : ℂ => e p + L z) 0 :=
    analyticAt_const.add (L.analyticAt 0)
  have ha' : AnalyticAt ℂ (fun v => Point.evaluate U s (e.symm v))
      ((fun z : ℂ => e p + L z) 0) := by
    simpa only [map_zero, add_zero] using ha
  exact AnalyticAt.comp (g := fun v => Point.evaluate U s (e.symm v))
    (f := fun z : ℂ => e p + L z) ha' hb

end HodgeLean.Foundations.Program
