import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Abdulali
open MvPolynomial

/-- A polynomial in rational coordinates with a common denominator again has
a polynomial numerator and a power of that denominator.
Source: Borel, Linear Algebraic Groups, second edition, AG.1, regular functions
on principal affine open subsets. -/
theorem polynomial_eval_div_numerator {K σ : Type*} [Field K]
    (p : σ → Polynomial K) (q : Polynomial K) (f : MvPolynomial σ K) :
    ∃ (N : ℕ) (P : Polynomial K), ∀ t : K, q.eval t ≠ 0 →
      eval (fun i => (p i).eval t / q.eval t) f = P.eval t / (q.eval t) ^ N := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    exact ⟨0, Polynomial.C a, fun t _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨N, P, hP⟩ := hf
    obtain ⟨M, Q, hQ⟩ := hg
    refine ⟨N + M, P * q ^ M + Q * q ^ N, ?_⟩
    intro t ht
    rw [map_add, hP t ht, hQ t ht]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, pow_add]
    field_simp
  | mul_X f i hf =>
    obtain ⟨N, P, hP⟩ := hf
    refine ⟨N + 1, P * p i, ?_⟩
    intro t ht
    rw [map_mul, eval_X, hP t ht]
    simp only [Polynomial.eval_mul, pow_succ]
    exact div_mul_div_comm _ _ _ _

#print axioms polynomial_eval_div_numerator
end HodgeLean.Foundations.Abdulali
