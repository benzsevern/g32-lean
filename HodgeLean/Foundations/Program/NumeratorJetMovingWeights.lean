import HodgeLean.Foundations.Program.NumeratorJetMovingFirst
import HodgeLean.Foundations.Program.NumeratorJetFieldRecurrence

/-! # Geometric moving-pole weights at every order -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Tensor polynomial for a geometric coefficient of the moving-pole ratio. -/
def b65e_tensorRatioQ (e d : Fin 2) (n : ℕ) : ℚ[X][X] :=
  b65e_tensorWeightQ e d * (-b65e_tensorWeightQ e d) ^ n

/-- Tensor geometric weights evaluate to the affine pole coefficients off the diagonal. -/
theorem b65e_tensorRatioQ_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (x y : Fin 12) (hxy : x ≠ y) (n : ℕ) :
    b65e_tensorEval (b65e_tensorRatioQ (b65q_fibreIndex x) (b65q_fibreIndex y) n)
      (p x) (p y) = b65e_poleRatioCoeff p (.inr x) (.inr y) n := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hy : y ∈ b65q_fibreSet (b65q_fibreIndex y) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hp : p x ≠ p y := by
    intro h
    apply hxy
    have hi := O.poles_injective 0 (Metric.mem_ball_self O.radius_pos)
    apply Sum.inr.inj (hi (show b65p_poles p 0 (.inr x) = b65p_poles p 0 (.inr y) by
      simpa only [b65p_poles, Sum.elim_inr, zero_mul, add_zero] using h))
  have hw := b65e_tensorWeightQ_eval _ _ _ _ (b65q_fibre_root O _ hx)
    (b65q_fibre_root O _ hy) hp
  unfold b65e_tensorRatioQ b65e_tensorEval
  rw [eval₂_mul, eval₂_pow, eval₂_neg]
  change b65e_tensorEval _ _ _ * (-b65e_tensorEval _ _ _) ^ n = _
  rw [hw, b65e_fibreIndex_value, b65e_fibreIndex_value]
  simp only [b65e_poleRatioCoeff, b65p_velocity, b65p_poles, Sum.elim_inr,
    zero_mul, add_zero, neg_div]

end HodgeLean.Foundations.Program
