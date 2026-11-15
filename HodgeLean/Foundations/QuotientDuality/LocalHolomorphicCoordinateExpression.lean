import HodgeLean.Foundations.QuotientDuality.LocalHolomorphicCharts
import Mathlib.Analysis.Analytic.Constructions

/-! Holomorphic coordinate families are analytic in the canonical smooth coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality

theorem holomorphic_coordinates_localChart_analytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (g : ComplexPoint X → (Fin d → ℂ)) (U : Set (ComplexPoint X)) (hU : IsOpen U)
    (hF : ∀ j, (f4_analytification X).IsHolFun (fun y : U => g y j))
    (x : ComplexPoint X) :
    AnalyticOnNhd ℂ (fun v => g ((localChart X d x).symm v))
      ((localChart X d x).target ∩ (localChart X d x).symm ⁻¹' U) := by
  intro v hv
  apply analyticAt_pi_iff.mpr
  intro j
  let E := localChart X d x
  let q := E.symm v
  have hqE : q ∈ E.source := E.map_target hv.1
  have hqF : q ∈ U := hv.2
  have hmc := ((f4_isHolFun_iff_contMDiffOn X d (fun y => g y j) hU).mp
    (hF j)).contMDiffAt (hU.mem_nhds hqF)
  have hchart := (contMDiffAt_iff_of_mem_source
    (I := 𝓘(ℂ, Fin d → ℂ)) (I' := 𝓘(ℂ, ℂ)) (n := ω)
    (f := fun y => g y j) (x := x) (x' := q) (y := g q j)
    hqE (mem_chart_source ℂ (g q j))).mp hmc
  have hcd : ContDiffAt ℂ ω (fun w => g (E.symm w) j) (E q) := by
    have hh := hchart.2
    simp only [mfld_simps, contDiffWithinAt_univ, Function.comp_def] at hh
    convert hh using 1 <;> rfl
  have ha := hcd.analyticAt
  have heq : E q = v := E.right_inv hv.1
  rw [heq] at ha
  exact ha

#print axioms holomorphic_coordinates_localChart_analytic
end HodgeLean.Foundations.QuotientDuality
