import HodgeLean.Foundations.Program.SchoenCycleNativeParameterEvaluation
import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Each actual power parameter has a regular section representative whose evaluations are the original centered native curve coordinate near the tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curve_power_parameter_regular_evaluation
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (i : Fin n) :
    ∃ (U : (g3_power Z n).left.Opens) (hxU : x.underlying ∈ U)
      (s : Γ((g3_power Z n).left, U)),
      (g3_power Z n).left.presheaf.germ U x.underlying hxU s = s2e_curvePowerParameter Z n x i ∧
      (∀ᶠ q in 𝓝 x, Point.evaluate U s q =
        ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) q) 0 -
          ComplexPoint.localChart Z 1 (Point.map (g3_proj Z n i) x) (Point.map (g3_proj Z n i) x) 0) := by
  let π := g3_proj Z n i
  let p := Point.map π x
  obtain ⟨V, hpV, t, ht, hev⟩ := s2e_native_curve_parameter_regular_chart Z p
  let U := π.left ⁻¹ᵁ V
  let s := π.left.app V t
  refine ⟨U, hpV, s, ?_, ?_⟩
  · change (g3_power Z n).left.presheaf.germ (π.left ⁻¹ᵁ V) x.underlying hpV (π.left.app V t) = _
    rw [← Scheme.Hom.germ_stalkMap_apply]
    exact congrArg (π.left.stalkMap x.underlying) ht
  · have hn : ∀ᶠ q in 𝓝 x, Point.map π q ∈ (ComplexPoint.localChart Z 1 p).source :=
      (Point.continuous_map π).continuousAt
        ((ComplexPoint.localChart Z 1 p).open_source.mem_nhds (ComplexPoint.mem_localChart_source Z 1 p))
    filter_upwards [hn] with q hq
    exact (Point.evaluate_map π V t q).symm.trans (hev (Point.map π q) hq)

#print axioms s2e_curve_power_parameter_regular_evaluation
end HodgeLean.Foundations.Program
