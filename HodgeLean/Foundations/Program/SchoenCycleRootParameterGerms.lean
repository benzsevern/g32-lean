import HodgeLean.Foundations.Program.SchoenCycleSectionAlongNativeChart
import HodgeLean.Foundations.Program.SchoenCycleCurvePowerRootChart
import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

/-! # Actual marked parameters evaluated in root coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- Each actual marked stalk parameter realizes as the specified nonzero scalar times its own root coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Forster, Lectures on Riemann Surfaces, §9.4. -/
theorem s2e_root_parameter_germ
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n d : ℕ) [SmoothOfRelativeDimension d (g3_power Z n).hom]
    (x : ComplexPoint (g3_power Z n))
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart (g3_power Z n) d x
      (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) z)) 0)
    (U : (g3_power Z n).left.affineOpens) (hxU : x.underlying ∈ U.1) (i : Fin n) :
    (s2e_stalkGermAlongNativeChart (g3_power Z n) d n x
      (s2e_curvePowerRootChart Z n x
        (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)))
      (s2e_curvePowerRootChart_tendsto Z n x _) (s2e_curvePowerRootChart_zero Z n x _)
      hqa U hxU (s2e_curvePowerParameter Z n x i)).val =
      Filter.Germ.ofFun (fun z : Fin n → ℂ =>
        ((b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)) 1) 0 * z i) := by
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  let p := Point.map (g3_proj Z n i) x
  obtain ⟨V, hpV, s, hs, hL, he⟩ := s2e_native_curve_parameter_rr_chart Z p
  change (s2e_stalkGermAlongNativeChart _ d n x _ _ _ hqa U hxU
    ((g3_proj Z n i).left.stalkMap x.underlying (s2e_native_curve_parameter Z p))).val = _
  rw [← hs, s2e_stalkGermAlongNativeChart_pullback_germ]
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun z : Fin n → ℂ => z i) (𝓝 0) (𝓝 0) :=
    (continuous_apply i).tendsto 0
  filter_upwards [ht he] with z hz
  change Point.evaluate V s
    ((ComplexPoint.localChart Z 1 p).symm
      (ComplexPoint.localChart Z 1 p p + L (z i))) = (L 1) 0 * z i at hz
  simpa only [s2e_curvePowerRootChart_projection,
    s2e_native_curve_extChart_apply, s2e_native_curve_extChart_symm_apply] using hz

end HodgeLean.Foundations.Program
