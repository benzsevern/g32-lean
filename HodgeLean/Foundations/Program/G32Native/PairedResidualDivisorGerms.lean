import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleNormalization

/-! # Equality of actual form divisors under equality of punctured germs -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Equal punctured coefficient germs give equal literal finite-support divisors. -/
theorem residual_divisor_eq_of_germs (hE : Module.finrank ℂ E = 1)
    (v w : TangentBundle 𝓘(ℂ, E) C → ℂ)
    (h : ∀ p, HurwitzPrymRR_loc hE v p =ᶠ[𝓝[≠] 0] HurwitzPrymRR_loc hE w p) :
    b4c_divForm (hE := hE) v = b4c_divForm (hE := hE) w := by
  have ho : b4c_ordForm (hE := hE) v = b4c_ordForm (hE := hE) w := by
    funext p
    exact congrArg WithTop.untop₀ (meromorphicOrderAt_congr (h p))
  by_cases hv : (Function.support (b4c_ordForm (hE := hE) v)).Finite
  · have hw : (Function.support (b4c_ordForm (hE := hE) w)).Finite := by
      rw [← ho]
      exact hv
    simp only [b4c_divForm, dif_pos hv, dif_pos hw]
    ext p
    exact congrFun ho p
  · have hw : ¬ (Function.support (b4c_ordForm (hE := hE) w)).Finite := by
      rw [← ho]
      exact hv
    simp only [b4c_divForm, dif_neg hv, dif_neg hw]

#print axioms residual_divisor_eq_of_germs

/-- Pole-value normalization preserves the literal divisor used by the supplied quotient point. -/
theorem residual_normalize_poles_divisor [T1Space C]
    (hE : Module.finrank ℂ E = 1) (S : Finset C)
    (w : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    b4c_divForm (hE := hE) (residual_normalize_poles S w) =
      b4c_divForm (hE := hE) w :=
  residual_divisor_eq_of_germs hE _ _ (residual_normalize_poles_loc hE S w)

#print axioms residual_normalize_poles_divisor

end HodgeLean.Foundations.Program.G32Native
