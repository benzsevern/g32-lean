import HodgeLean.Foundations.Program.SchoenCycleC1ActualLocalActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleMorphismNativeCoordinates
import HodgeLean.Foundations.Program.SchoenCycleNativeParameterEvaluation
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticStalk
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticCoordinates
import HodgeLean.Foundations.Program.SchoenCycleC1LocalFieldActionHelpers

/-! # The native analytic character of the actual stalk parameter -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- The native regular parameter has exactly the native coordinate germ
under the actual algebraic-to-analytic stalk comparison. -/
theorem s2e_c1_native_parameter_analytic_germ
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    s2e_stalk_nativeAnalyticGerm X 1 p (s2e_native_curve_parameter X p) =
      s2e_nativeAnalytic_coordinate 1 0 := by
  obtain ⟨U, hp, s, hs, hf⟩ := s2e_native_curve_parameter_regular_chart X p
  rw [← hs, s2e_stalk_nativeAnalyticGerm_germ]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  let C := localChart X 1 p
  have htarget : ∀ᶠ z : Fin 1 → ℂ in 𝓝 0, C p + z ∈ C.target := by
    have ht : Tendsto (fun z : Fin 1 → ℂ => C p + z) (𝓝 0) (𝓝 (C p)) := by
      have hc : Continuous (fun z : Fin 1 → ℂ => C p + z) := continuous_const.add continuous_id
      simpa only [add_zero] using hc.tendsto (0 : Fin 1 → ℂ)
    exact ht (C.open_target.mem_nhds (C.map_source (mem_localChart_source X 1 p)))
  filter_upwards [htarget] with z hz
  change Point.evaluate U s (C.symm (C p + z)) = z 0
  rw [hf _ (C.symm.map_source hz), C.right_inv hz]
  change C p 0 + z 0 - C p 0 = z 0
  exact add_sub_cancel_left _ _

/-- Pullback of the actual native parameter realizes the actual centered
coordinate map of the fixed curve morphism. -/
theorem s2e_c1_native_parameter_pullback_analytic_germ
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom]
    (f : X ⟶ X) (p : ComplexPoint X) (hp : Point.map f p = p) :
    let hfix : f.left p.underlying = p.underlying := by
      simpa only [Point.underlying_map] using congrArg Point.underlying hp
    let C := localChart X 1 p
    (s2e_stalk_nativeAnalyticGerm X 1 p
      (s2e_fixed_point_stalkPullback X.left f.left p.underlying hfix
        (s2e_native_curve_parameter X p))).val =
      Filter.Germ.ofFun (fun z : Fin 1 → ℂ =>
        C (Point.map f (C.symm (C p + z))) 0 - C p 0) := by
  let hfix : f.left p.underlying = p.underlying := by
    simpa only [Point.underlying_map] using congrArg Point.underlying hp
  dsimp only
  obtain ⟨U, hpU, s, hs, hf⟩ := s2e_native_curve_parameter_regular_chart X p
  rw [← hs, s2e_c1_fixed_stalk_pullback_section_germ X.left f.left p.underlying hfix U hpU s,
    s2e_stalk_nativeAnalyticGerm_germ]
  apply Filter.Germ.coe_eq.mpr
  let C := localChart X 1 p
  have ht : Tendsto (fun z : Fin 1 → ℂ => Point.map f (C.symm (C p + z)))
      (𝓝 0) (𝓝 p) := by
    simpa only [hp, Function.comp_def, C] using (Point.continuous_map f).continuousAt.tendsto.comp
      (s2e_centered_localChart_tendsto X 1 p)
  filter_upwards [ht (C.open_source.mem_nhds (mem_localChart_source X 1 p))] with z hz
  change Point.evaluate (f.left ⁻¹ᵁ U) (f.left.app U s) (C.symm (C p + z)) = _
  rw [← Point.evaluate_map f U s]
  exact hf _ hz


end HodgeLean.Foundations.Program
