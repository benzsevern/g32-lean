import HodgeLean.Foundations.Program.NumeratorJetFieldRecurrence
import HodgeLean.Foundations.Program.NumeratorJetFixedInverse
import HodgeLean.Foundations.Program.NumeratorJetDividedDifference

/-! # Fixed-pole convolution fields in rational sextic quotients -/

noncomputable section
open Matrix Polynomial
namespace HodgeLean.Foundations.Program

/-- Polynomial coefficient arrays evaluated on the labelled moving poles. -/
def b65e_polynomialResidue (p : Fin 12 → ℂ)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ
  | .inl k => (A n k).map (Rat.castHom ℂ)
  | .inr x => fun i j ↦ (B n (b65q_fibreIndex x) i j).eval₂ (Rat.castHom ℂ) (p x)

/-- The geometric pole coefficients in a fixed-to-moving interaction. -/
def b65e_fixedRatioQ (e : Fin 2) (k : Fin 4) (n : ℕ) : ℚ[X] :=
  (b65e_velocityPolynomialQ e * b65e_fixedInverseQ e k) *
    (-(b65e_velocityPolynomialQ e * b65e_fixedInverseQ e k)) ^ n

/-- Evaluation of the rational geometric coefficient gives the actual pole coefficient. -/
theorem b65e_fixedRatioQ_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (e : Fin 2) (k : Fin 4) (x : Fin 12) (hx : x ∈ b65q_fibreSet e) (n : ℕ) :
    (b65e_fixedRatioQ e k n).eval₂ (Rat.castHom ℂ) (p x) =
      b65e_poleRatioCoeff p (.inl k) (.inr x) n := by
  have he := (Finset.mem_filter.mp hx).2
  have hf : b65q_fibreValue (b65q_fibreIndex x) = b65p_fibre x := by
    fin_cases x <;> decide +kernel
  rw [he] at hf
  simp only [b65e_fixedRatioQ, eval₂_mul, eval₂_pow, eval₂_neg,
    b65e_velocityPolynomialQ_eval, b65e_fixedInverseQ_eval e k (p x)
      (b65q_fibre_root O e hx), hf]
  simp only [b65e_poleRatioCoeff, b65p_velocity, b65p_poles, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, zero_mul, add_zero, zero_sub]
  rw [← neg_sub (p x) (b65p_fixedPole k), neg_div_neg_eq]
  simp only [div_eq_mul_inv, neg_mul, inv_neg, mul_neg, neg_neg]

/-- Rational polynomial commutator coefficient for a moving and a fixed residue. -/
def b65e_fixedCommutatorQ
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (e : Fin 2) (k : Fin 4) (i j : Fin 4) : ℚ[X] :=
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1), B b e i t * C (A (m - b) k t j)) -
  (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1), C (A b k i t) * B (m - b) e t j)

/-- Fixed-pole field coefficients computed by rational quotient traces. -/
def b65e_fixedFieldQ
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (k : Fin 4) (i j : Fin 4) : ℚ :=
  ∑ e : Fin 2, ∑ a ∈ Finset.range (n + 1),
    b65e_fibreTraceQ e (b65e_fixedRatioQ e k a * b65e_fixedCommutatorQ A B (n - a) e k i j)

/-- Evaluating the polynomial commutator gives the entrywise convolution. -/
theorem b65e_fixedCommutatorQ_eval (p : Fin 12 → ℂ)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (m : ℕ) (x : Fin 12) (k : Fin 4) (i j : Fin 4) :
    (b65e_fixedCommutatorQ A B m (b65q_fibreIndex x) k i j).eval₂
      (Rat.castHom ℂ) (p x) =
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inr x) i t *
      b65e_polynomialResidue p A B (m - b) (.inl k) t j) -
    (∑ t : Fin 4, ∑ b ∈ Finset.range (m + 1),
      b65e_polynomialResidue p A B b (.inl k) i t *
      b65e_polynomialResidue p A B (m - b) (.inr x) t j) := by
  simp only [b65e_fixedCommutatorQ, eval₂_sub, eval₂_finsetSum, eval₂_mul,
    eval₂_C, b65e_polynomialResidue, Matrix.map_apply, Rat.coe_castHom]

/-- The rational trace formula evaluates to the actual fixed-pole convolution field. -/
theorem b65e_fixedFieldQ_cast (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (A : ℕ → Fin 4 → Matrix (Fin 4) (Fin 4) ℚ)
    (B : ℕ → Fin 2 → Matrix (Fin 4) (Fin 4) ℚ[X])
    (n : ℕ) (k : Fin 4) (i j : Fin 4) :
    (b65e_fixedFieldQ A B n k i j : ℂ) =
      b65e_fieldCoeff p (b65e_polynomialResidue p A B) n (.inl k) i j := by
  unfold b65e_fieldCoeff
  rw [Fintype.sum_sum_type]
  have hz : (∑ r : Fin 4, if (Sum.inl r : Fin 4 ⊕ Fin 12) = .inl k then (0 : ℂ) else
      ∑ a ∈ Finset.range (n + 1), b65e_poleRatioCoeff p (.inl k) (.inl r) a *
      ((∑ t : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        b65e_polynomialResidue p A B b (.inl r) i t *
        b65e_polynomialResidue p A B (n - a - b) (.inl k) t j) -
       (∑ t : Fin 4, ∑ b ∈ Finset.range (n - a + 1),
        b65e_polynomialResidue p A B b (.inl k) i t *
        b65e_polynomialResidue p A B (n - a - b) (.inl r) t j))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    split_ifs
    · rfl
    · apply Finset.sum_eq_zero
      intro a _
      simp only [b65e_poleRatioCoeff, b65p_velocity, Sum.elim_inl,
        Pi.zero_apply, sub_self, zero_div, zero_mul]
  rw [hz, zero_add]
  simp only [reduceCtorEq, ite_false]
  rw [← Finset.sum_fiberwise Finset.univ b65q_fibreIndex]
  unfold b65e_fixedFieldQ
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← b65e_fibreTraceQ_sum p O e]
  apply Finset.sum_congr rfl
  intro x hx
  have he := (Finset.mem_filter.mp hx).2
  rw [eval₂_mul, b65e_fixedRatioQ_eval p O e k x hx a, ← he,
    b65e_fixedCommutatorQ_eval]

end HodgeLean.Foundations.Program
