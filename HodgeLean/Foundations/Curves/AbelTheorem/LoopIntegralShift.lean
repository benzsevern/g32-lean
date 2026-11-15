import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem loop_integral_parameter_shift (γ : b3_SmoothLoop E C)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (a : ℝ) :
    b3_pathIntegral E C (fun t => γ.val (t + a)) θ = loopIntegral γ θ := by
  have hper : Function.Periodic (fun t => θ ⟨γ.val t, b3_velocity E C γ.val t⟩) 1 := by
    intro t
    have hv := b3Rest2_velocity_add_int γ.property.2 γ.property.1 t 1
    simp only [Int.cast_one] at hv
    change b3_velocity E C γ.val (t + 1) = b3_velocity E C γ.val t at hv
    apply congrArg θ
    exact Bundle.TotalSpace.ext (γ.property.1 t) (heq_of_eq hv)
  change (∫ t in (0 : ℝ)..1, θ ⟨γ.val (t + a),
      b3_velocity E C (fun u => γ.val (u + a)) t⟩) =
    ∫ t in (0 : ℝ)..1, θ ⟨γ.val t, b3_velocity E C γ.val t⟩
  have hshift (t : ℝ) : θ ⟨γ.val (t + a), b3_velocity E C (fun u => γ.val (u + a)) t⟩ =
      θ ⟨γ.val (t + a), b3_velocity E C γ.val (t + a)⟩ := by
    have hv := b3Rest2_velocity_shift γ.property.2 a t
    change b3_velocity E C (fun u => γ.val (u + a)) t = b3_velocity E C γ.val (t + a) at hv
    exact congrArg (fun v : E => θ ⟨γ.val (t + a), v⟩) hv
  rw [intervalIntegral.integral_congr (fun t _ => hshift t)]
  rw [intervalIntegral.integral_comp_add_right
    (fun t => θ ⟨γ.val t, b3_velocity E C γ.val t⟩), zero_add, add_comm 1 a]
  have he := hper.intervalIntegral_add_eq a 0
  simpa only [zero_add] using he

end HodgeLean.Foundations.Curves.AbelTheorem
