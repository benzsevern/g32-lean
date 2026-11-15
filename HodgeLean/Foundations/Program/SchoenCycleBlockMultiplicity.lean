import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Multiplicities of indexed collision blocks -/
noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A block of repeated points contributes its entire indexed length.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_block_tuple_divisor_multiplicity
    {C : Type*} {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → C) (hp : Function.Injective p)
    (q : Fin n → C) (hq : ∀ a i, q (ι ⟨a, i⟩) = p a)
    (a : Fin b) :
    (∑ i : Fin n, Finsupp.single (q i) (1 : ℤ)) (p a) = m a := by
  classical
  rw [← Equiv.sum_comp ι]
  simp only [Finsupp.finsetSum_apply, Fintype.sum_sigma]
  simp_rw [hq, Finsupp.single_apply, hp.eq_iff]
  simp

/-- Distinct blocks retain a double root and a simple root in the same tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_block_tuple_double_simple_check :
    (Finsupp.single (0 : ℂ) (1 : ℤ) + Finsupp.single 0 1 +
      Finsupp.single 1 1 : ℂ →₀ ℤ) 0 = 2 ∧
    (Finsupp.single (0 : ℂ) (1 : ℤ) + Finsupp.single 0 1 +
      Finsupp.single 1 1 : ℂ →₀ ℤ) 1 = 1 := by
  norm_num [Finsupp.add_apply, Finsupp.single_apply]

#print axioms s2e_block_tuple_divisor_multiplicity
#print axioms s2e_block_tuple_double_simple_check
end HodgeLean.Foundations.Program
