import Mathlib.Algebra.MvPolynomial.Equiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Splitting the variable set retains the independent actions on the first block and the coefficient blocks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_sum_polynomial_rename_blocks
    {R σ τ : Type*} [CommRing R] (f : σ → σ) (g : τ → τ)
    (p : MvPolynomial (σ ⊕ τ) R) :
    sumAlgEquiv R σ τ (rename (Sum.map f g) p) =
      rename f (map (rename g).toRingHom (sumAlgEquiv R σ τ p)) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C, sumAlgEquiv_C_inl, map_C]
    exact congrArg C (rename_C g r).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    cases i with
    | inl i =>
      simp only [map_mul, hp, rename_X, Sum.map_inl, sumAlgEquiv_X_inl, map_X]
    | inr i =>
      simp only [map_mul, hp, rename_X, Sum.map_inr, sumAlgEquiv_X_inr, map_C, rename_C]
      congr 1
      exact congrArg C (rename_X g i).symm

end HodgeLean.Foundations.Program
