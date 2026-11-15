import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The support of a total-degree-h multidegree on h factors. -/
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A total-degree-h multidegree on h factors is either all degree one or has
a degree-zero factor.
Source: the equality case in the sum of h positive natural numbers. -/
theorem s4_e1_multidegree_one_or_zero (h : ℕ) (d : Fin h → ℕ)
    (hd : ∑ i, d i = h) :
    d = (fun _ => 1) ∨ ∃ i, d i = 0 := by
  classical
  by_cases hz : ∃ i, d i = 0
  · exact Or.inr hz
  left
  have hpos (i : Fin h) : 1 ≤ d i := by
    have hi : d i ≠ 0 := fun hi => hz ⟨i, hi⟩
    omega
  funext i
  by_contra hi
  have hlt : (∑ _ : Fin h, (1 : ℕ)) < ∑ j, d j :=
    Finset.sum_lt_sum (fun j _ => hpos j)
      ⟨i, Finset.mem_univ i, by have := hpos i; omega⟩
  have hs : (∑ _ : Fin h, (1 : ℕ)) = h := by simp
  rw [hs, hd] at hlt
  exact (Nat.lt_irrefl h) hlt

#print axioms s4_e1_multidegree_one_or_zero
end HodgeLean.Foundations.Program
