import HodgeLean.Foundations.Program.NumeratorJetMovingWeights
import HodgeLean.Foundations.Program.NumeratorJetFixedCertificates

/-! # Polynomial moving-pole convolution fields -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- A polynomial in the source variable evaluates independently of the target. -/
theorem b65e_tensorEval_source (g : ℚ[X]) (x y : ℂ) :
    b65e_tensorEval (g.map (C : ℚ →+* ℚ[X])) x y =
      g.eval₂ (Rat.castHom ℂ) y := by
  unfold b65e_tensorEval
  rw [eval₂_map]
  congr 1
  ext a
  simp

/-- Tensor commutator coefficients with source and target variables kept separate. -/
def b65e_movingCommutatorQ
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (e d : Fin 2) (i j : Fin 4) : ℚ[X][X] :=
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
    (B b d i t).map C * C (B (m - b) e t j)) -
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
    C (B b e i t) * (B (m - b) d t j).map C)

/-- Tensor commutator evaluation is the entrywise residue convolution. -/
theorem b65e_movingCommutatorQ_eval (p : Fin 12 → ℂ)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (x y : Fin 12) (i j : Fin 4) :
    b65e_tensorEval (b65e_movingCommutatorQ B m
      (b65q_fibreIndex x) (b65q_fibreIndex y) i j) (p x) (p y) =
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inr y) i t *
      b65e_polynomialResidue p A B (m - b) (.inr x) t j) -
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inr x) i t *
      b65e_polynomialResidue p A B (m - b) (.inr y) t j) := by
  unfold b65e_movingCommutatorQ
  simp only [b65e_tensorEval, eval₂_sub, eval₂_finsetSum, eval₂_mul]
  have hs (g : ℚ[X]) := b65e_tensorEval_source g (p x) (p y)
  unfold b65e_tensorEval at hs
  simp only [hs, eval₂_C, coe_eval₂RingHom, b65e_polynomialResidue]

/-- Partial traces give the off-diagonal moving interactions, including the removed
same-label term whose convolution commutator vanishes. -/
theorem b65e_movingInteraction_sum (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (a m : ℕ) (x : Fin 12) (d : Fin 2) (i j : Fin 4) :
    (∑ y ∈ b65q_fibreSet d, if y = x then (0 : ℂ) else
      b65e_poleRatioCoeff p (.inr x) (.inr y) a *
      ((∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
        b65e_polynomialResidue p A B b (.inr y) i t *
        b65e_polynomialResidue p A B (m - b) (.inr x) t j) -
       (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
        b65e_polynomialResidue p A B b (.inr x) i t *
        b65e_polynomialResidue p A B (m - b) (.inr y) t j))) =
    (b65e_partialTraceQ d (b65e_tensorRatioQ (b65q_fibreIndex x) d a *
      b65e_movingCommutatorQ B m (b65q_fibreIndex x) d i j)).eval₂
      (Rat.castHom ℂ) (p x) := by
  rw [← b65e_partialTraceQ_sum p O d]
  apply Finset.sum_congr rfl
  intro y hy
  have hd := (Finset.mem_filter.mp hy).2
  rw [b65e_tensorEval_mul, ← hd]
  by_cases he : y = x
  · subst y
    rw [ite_eq_left rfl, b65e_movingCommutatorQ_eval p A B]
    simp only [sub_self, mul_zero]
  · rw [ite_eq_right he, b65e_tensorRatioQ_eval p O x y (Ne.symm he),
      b65e_movingCommutatorQ_eval p A B]

end HodgeLean.Foundations.Program
