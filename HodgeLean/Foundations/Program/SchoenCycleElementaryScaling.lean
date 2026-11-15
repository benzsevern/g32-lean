import Mathlib.Analysis.Complex.Basic
import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialGenerators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Scalar normalization of every root scales the degree-k elementary coefficient by the exact kth power of the same scalar.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_elementary_evaluation_scale
    {σ : Type*} [Fintype σ] (c : ℂ) (v : σ → ℂ) (k : ℕ) :
    aeval (fun i => c * v i) (esymm σ ℂ k) = c ^ k * aeval v (esymm σ ℂ k) := by
  classical
  simp only [esymm, aeval_sum, aeval_prod, aeval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hs).2]

#print axioms s2e_elementary_evaluation_scale
end HodgeLean.Foundations.Program
