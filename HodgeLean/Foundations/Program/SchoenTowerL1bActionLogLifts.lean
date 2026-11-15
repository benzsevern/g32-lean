import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- On a connected domain, two continuous logarithmic lifts of the same
map differ by one constant integral deck translation. -/
theorem s2v_l1b_action_log_lifts_differ_int
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F G : X → ℂ) (hF : Continuous F) (hG : Continuous G)
    (he : ∀ x, Complex.exp (F x) = Complex.exp (G x)) (x₀ : X) :
    ∃ k : ℤ, ∀ x, F x = G x + k * (2 * Real.pi * Complex.I) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he x₀)
  have hv (x : X) : Complex.exp (F x - G x) = 1 := by
    rw [Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
  refine ⟨k, fun x => ?_⟩
  have hc := Complex.isCoveringMap_exp.const_of_comp (hF.sub hG)
    (fun a b => Subtype.ext ((hv a).trans (hv b).symm)) x x₀
  change F x - G x = F x₀ - G x₀ at hc
  linear_combination hc + hk

/-- Exponential equivariance of a continuous logarithmic lift gives exact
logarithmic equivariance up to one constant integer. -/
theorem s2v_l1b_action_log_lift_equivariance
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F : X → ℂ) (hF : Continuous F) (f : X → X) (hf : Continuous f)
    (a : ℂ) (he : ∀ x, Complex.exp (F (f x)) = Complex.exp a * Complex.exp (F x))
    (x₀ : X) :
    ∃ k : ℤ, ∀ x, F (f x) = F x + a + k * (2 * Real.pi * Complex.I) := by
  apply s2v_l1b_action_log_lifts_differ_int (F ∘ f) (fun x => F x + a)
    (hF.comp hf) (hF.add continuous_const) _ x₀
  intro x
  simpa only [Function.comp_apply, Complex.exp_add, mul_comm] using he x

end HodgeLean.Foundations.Program
