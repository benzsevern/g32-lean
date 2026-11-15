import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

/-! # Pole bounds for finite differential families
A common lower bound on meromorphic orders persists under finite sums.
-/

open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A finite sum retains any common lower bound on its meromorphic orders. -/
theorem s2e_meromorphic_order_sum_lower_bound
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ) (n : WithTop ℤ)
    (hm : ∀ i ∈ s, MeromorphicAt (f i) z)
    (ho : ∀ i ∈ s, n ≤ meromorphicOrderAt (f i) z) :
    n ≤ meromorphicOrderAt (∑ i ∈ s, f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change n ≤ meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) z
      rw [meromorphicOrderAt_const, ite_eq_left rfl]
      exact le_top
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      have hms : ∀ j ∈ s, MeromorphicAt (f j) z := fun j hj => hm j (Finset.mem_insert_of_mem hj)
      have hos : ∀ j ∈ s, n ≤ meromorphicOrderAt (f j) z :=
        fun j hj => ho j (Finset.mem_insert_of_mem hj)
      exact (le_min (ho i (Finset.mem_insert_self i s)) (ih hms hos)).trans
        (meromorphicOrderAt_add (hm i (Finset.mem_insert_self i s)) (MeromorphicAt.sum hms))

end HodgeLean.Foundations.Program
