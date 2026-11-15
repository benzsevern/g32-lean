import HodgeLean.Foundations.Program.NumeratorJetMovingAssembly

/-! # Reduced moving-pole field contractions -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Reducing a geometric weight in both variables preserves its weighted partial trace. -/
theorem b65e_reducedTensorRatioQ_partialTrace (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e d : Fin 2) (a : ℕ) (g : ℚ[X][X]) (x : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) :
    (b65e_partialTraceQ d (b65e_reducedTensorRatioQ e d a * g)).eval₂
        (Rat.castHom ℂ) x =
      (b65e_partialTraceQ d (b65e_tensorRatioQ e d a * g)).eval₂
        (Rat.castHom ℂ) x := by
  rw [← b65e_partialTraceQ_sum p O d, ← b65e_partialTraceQ_sum p O d]
  apply Finset.sum_congr rfl
  intro y hy
  rw [b65e_tensorEval_mul, b65e_tensorEval_mul,
    b65e_reducedTensorRatioQ_eval e d a x (p y) hx (b65q_fibre_root O d hy)]

/-- Moving-pole convolution field using geometrically reduced tensor weights. -/
def b65e_reducedMovingFieldQ
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (e : Fin 2) (i j : Fin 4) : ℚ[X] :=
  (∑ k : Fin 4, ∑ a ∈ Finset.range (n + 1),
    b65e_fixedRatioQ e k a * b65e_movingFixedCommutatorQ A B (n - a) e k i j) +
  ∑ d : Fin 2, ∑ a ∈ Finset.range (n + 1),
    b65e_partialTraceQ d (b65e_reducedTensorRatioQ e d a *
      b65e_movingCommutatorQ B (n - a) e d i j)

/-- The reduced rational field gives the actual moving-pole field coefficients. -/
theorem b65e_reducedMovingFieldQ_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (x : Fin 12) (i j : Fin 4) :
    (b65e_reducedMovingFieldQ A B n (b65q_fibreIndex x) i j).eval₂
      (Rat.castHom ℂ) (p x) =
      b65e_fieldCoeff p (b65e_polynomialResidue p A B) n (.inr x) i j := by
  rw [← b65e_movingFieldQ_eval p O A B n x i j]
  unfold b65e_reducedMovingFieldQ b65e_movingFieldQ
  simp only [eval₂_add, eval₂_finsetSum]
  apply congrArg₂ (fun u v : ℂ ↦ u + v) rfl
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply b65e_reducedTensorRatioQ_partialTrace p O
  apply b65q_fibre_root O
  simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]

end HodgeLean.Foundations.Program
