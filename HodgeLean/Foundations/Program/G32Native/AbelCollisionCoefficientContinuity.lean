import HodgeLean.Foundations.Program.G32Native.AbelCollisionBlocks
import HodgeLean.Foundations.Program.SchoenCycleMonicRootSelection
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Continuity of the exact original collision coefficient map -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The total collision has zero lower monic coefficients in every block. -/
theorem collisionBlockCoefficients_zero {A : Type} [Fintype A] [DecidableEq A]
    (m : A → ℕ) : collisionBlockCoefficients m 0 = 0 := by
  funext ⟨a, j⟩
  change collisionMonicCoefficients (0 : Fin (m a) → ℂ) j = 0
  exact congrArg (fun v : Fin (m a) → ℂ => v j) (collisionMonicCoefficients_zero (m a))

/-- All lower monic coefficients depend continuously on the indexed roots. -/
theorem collisionBlockCoefficients_continuous {A : Type} [Fintype A] [DecidableEq A]
    (m : A → ℕ) : Continuous (collisionBlockCoefficients m) := by
  apply continuous_pi
  intro ⟨a, j⟩
  have he (z : (Σ b, Fin (m b)) → ℂ) : collisionBlockCoefficients m z ⟨a, j⟩ =
      (-1 : ℂ) ^ (m a - j.val) * MvPolynomial.eval (fun i => z ⟨a, i⟩)
        (MvPolynomial.esymm (Fin (m a)) ℂ (m a - j.val)) :=
    s2e_rootTuple_signed_coefficient (m a) (fun i => z ⟨a, i⟩) j
  simp_rw [he]
  apply continuous_const.mul
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun i : Fin (m a) => continuous_apply (⟨a, i⟩ : Σ b, Fin (m b)))

#print axioms collisionBlockCoefficients_zero
#print axioms collisionBlockCoefficients_continuous
end HodgeLean.Foundations.Program.G32Native
