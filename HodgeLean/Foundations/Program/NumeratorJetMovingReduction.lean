import HodgeLean.Foundations.Program.NumeratorJetMovingWeights

/-! # Source-reduced geometric moving-pole weights -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Successive geometric weights reduced in the source sextic quotient. -/
def b65e_sourceReducedRatioQ (e d : Fin 2) : ℕ → ℚ[X][X]
  | 0 => b65e_tensorReduce d (b65e_tensorWeightQ e d)
  | n + 1 => b65e_tensorReduce d
      (b65e_sourceReducedRatioQ e d n * (-b65e_tensorWeightQ e d))

/-- Source reduction preserves every geometric coefficient on source-fibre roots. -/
theorem b65e_sourceReducedRatioQ_eval (e d : Fin 2) (n : ℕ) (x y : ℂ)
    (hy : (b65q_fibreC d).eval y = 0) :
    b65e_tensorEval (b65e_sourceReducedRatioQ e d n) x y =
      b65e_tensorEval (b65e_tensorRatioQ e d n) x y := by
  induction n with
  | zero =>
    rw [b65e_sourceReducedRatioQ, b65e_tensorReduce_eval d _ x y hy]
    simp only [b65e_tensorRatioQ, pow_zero, mul_one]
  | succ n ih =>
    rw [b65e_sourceReducedRatioQ, b65e_tensorReduce_eval d _ x y hy,
      b65e_tensorEval_mul, ih]
    unfold b65e_tensorRatioQ b65e_tensorEval
    simp only [eval₂_mul, eval₂_pow, eval₂_neg, pow_succ]
    ring

/-- Each reduced geometric weight uses at most six source powers. -/
theorem b65e_sourceReducedRatioQ_natDegree (e d : Fin 2) (n : ℕ) :
    (b65e_sourceReducedRatioQ e d n).natDegree < 6 := by
  cases n <;> apply b65e_tensorReduce_natDegree

/-- Reduced moving-pole weights still give the actual geometric coefficients. -/
theorem b65e_sourceReducedRatioQ_poleCoeff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (x y : Fin 12) (hxy : x ≠ y) (n : ℕ) :
    b65e_tensorEval (b65e_sourceReducedRatioQ
      (b65q_fibreIndex x) (b65q_fibreIndex y) n) (p x) (p y) =
      b65e_poleRatioCoeff p (.inr x) (.inr y) n := by
  rw [b65e_sourceReducedRatioQ_eval]
  · exact b65e_tensorRatioQ_eval p O x y hxy n
  · apply b65q_fibre_root O
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]

end HodgeLean.Foundations.Program
