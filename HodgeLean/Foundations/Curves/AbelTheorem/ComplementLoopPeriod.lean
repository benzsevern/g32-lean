import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
attribute [local instance] b3Forms_isManifold_real

def ambient_divisor_complement_loop (D : C →₀ ℤ)
    (γ : b3_SmoothLoop E (divisorComplement D)) : b3_SmoothLoop E C :=
  ⟨fun t => (γ.val t).val, fun t => congrArg Subtype.val (γ.property.1 t), by
    have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun q : divisorComplement D => q.val) :=
      contMDiff_subtype_val
    exact hi.comp γ.property.2⟩

theorem divisor_complement_loop_period_eq (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    (γ : b3_SmoothLoop E (divisorComplement D)) :
    b3_period E (divisorComplement D) γ (divisorDifferentialRestriction h D w ha) =
      loopIntegral (ambient_divisor_complement_loop D γ) w := by
  change b3_pathIntegral E (divisorComplement D) γ.val _ = b3_pathIntegral E C
    (fun t => (γ.val t).val) w
  unfold b3_pathIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show (fun t => (γ.val t).val) = (fun q : divisorComplement D => q.val) ∘ γ.val from rfl,
    b3A_velocity_comp _ contMDiff_subtype_val γ.val γ.property.2 t]
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
