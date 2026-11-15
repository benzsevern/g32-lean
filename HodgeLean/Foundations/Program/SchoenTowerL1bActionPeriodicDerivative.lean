import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- A differentiable periodic complex germ has nonzero derivative when
its local period is positive. -/
theorem s2v_l1b_action_periodic_derivative_ne_zero
    (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f 0) (hfix : f 0 = 0)
    (N : ℕ) (hN : 0 < N) (hperiod : ∀ᶠ z in 𝓝 0, f^[N] z = z) :
    deriv f 0 ≠ 0 := by
  have hd := (HasDerivAt.iterate (0 : ℂ) hf.hasDerivAt hfix N).deriv
  have hi : deriv (f^[N]) 0 = 1 := by
    have he : f^[N] =ᶠ[𝓝 0] (fun z => z) := hperiod
    rw [he.deriv_eq]
    exact (hasDerivAt_id (0 : ℂ)).deriv
  have hp : (deriv f 0) ^ N = 1 := hd.symm.trans hi
  intro hz
  rw [hz, zero_pow (Nat.ne_of_gt hN)] at hp
  exact zero_ne_one hp

end HodgeLean.Foundations.Program
