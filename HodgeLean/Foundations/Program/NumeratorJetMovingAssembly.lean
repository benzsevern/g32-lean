import HodgeLean.Foundations.Program.NumeratorJetMovingField
import HodgeLean.Foundations.Program.NumeratorJetTensorReduction

/-! # Assembly of the polynomial moving-pole fields -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Swapping the pole pair preserves each geometric coefficient. -/
theorem b65e_poleRatioCoeff_symm (p : Fin 12 → ℂ)
    (q r : Fin 4 ⊕ Fin 12) (n : ℕ) :
    b65e_poleRatioCoeff p q r n = b65e_poleRatioCoeff p r q n := by
  unfold b65e_poleRatioCoeff
  rw [← neg_sub (b65p_velocity p q) (b65p_velocity p r),
    ← neg_sub (b65p_poles p 0 q) (b65p_poles p 0 r)]
  simp only [neg_neg, div_neg, neg_div]

/-- Polynomial commutator coefficients with a fixed source and moving target. -/
def b65e_movingFixedCommutatorQ
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (e : Fin 2) (k : Fin 4) (i j : Fin 4) : ℚ[X] :=
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1), C (A b k i t) * B (m - b) e t j) -
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1), B b e i t * C (A (m - b) k t j))

/-- Evaluating the fixed-source commutator gives the actual convolution. -/
theorem b65e_movingFixedCommutatorQ_eval (p : Fin 12 → ℂ)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (x : Fin 12) (k : Fin 4) (i j : Fin 4) :
    (b65e_movingFixedCommutatorQ A B m (b65q_fibreIndex x) k i j).eval₂
      (Rat.castHom ℂ) (p x) =
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inl k) i t *
      b65e_polynomialResidue p A B (m - b) (.inr x) t j) -
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inr x) i t *
      b65e_polynomialResidue p A B (m - b) (.inl k) t j) := by
  simp only [b65e_movingFixedCommutatorQ, eval₂_sub, eval₂_finsetSum, eval₂_mul,
    eval₂_C, b65e_polynomialResidue, Matrix.map_apply, Rat.coe_castHom]

/-- Polynomial moving-pole field with the source labels summed by partial traces. -/
def b65e_movingFieldQ
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (e : Fin 2) (i j : Fin 4) : ℚ[X] :=
  (∑ k : Fin 4, ∑ a ∈ Finset.range (n + 1),
    b65e_fixedRatioQ e k a * b65e_movingFixedCommutatorQ A B (n - a) e k i j) +
  ∑ d : Fin 2, ∑ a ∈ Finset.range (n + 1),
    b65e_partialTraceQ d (b65e_tensorRatioQ e d a *
      b65e_movingCommutatorQ B (n - a) e d i j)

/-- The polynomial field evaluates to the finite Schlesinger field at every moving pole. -/
theorem b65e_movingFieldQ_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (x : Fin 12) (i j : Fin 4) :
    (b65e_movingFieldQ A B n (b65q_fibreIndex x) i j).eval₂
      (Rat.castHom ℂ) (p x) =
      b65e_fieldCoeff p (b65e_polynomialResidue p A B) n (.inr x) i j := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold b65e_fieldCoeff b65e_movingFieldQ
  rw [Fintype.sum_sum_type]
  simp only [eval₂_add, eval₂_finsetSum, Sum.inl_ne_inr, ite_false, Sum.inr.injEq]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro a _
    rw [eval₂_mul, b65e_fixedRatioQ_eval p O _ k x hx a,
      b65e_poleRatioCoeff_symm, b65e_movingFixedCommutatorQ_eval]
  · rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
    apply Finset.sum_congr rfl
    intro d _
    have hi (y : Fin 12) (f : ℕ → ℂ) :
        (if y = x then 0 else ∑ a ∈ Finset.range (n + 1), f a) =
        ∑ a ∈ Finset.range (n + 1), if y = x then 0 else f a := by
      by_cases h : y = x <;> simp only [h, ite_true, ite_false, Finset.sum_const_zero]
    simp_rw [hi]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact (b65e_movingInteraction_sum p O A B a (n - a) x d i j).symm

end HodgeLean.Foundations.Program
