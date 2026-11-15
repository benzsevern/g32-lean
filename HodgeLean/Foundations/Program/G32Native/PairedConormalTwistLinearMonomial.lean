import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistPolynomial

/-! # Degree-one homogeneous monomials retain their coordinate indices -/

noncomputable section
set_option maxHeartbeats 400000
open ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native

/-- A degree-one monomial with nonnegative exponents has one specified
coordinate exponent equal to one and every other exponent equal to zero. -/
theorem paired_twist_linear_monomial {n : ℕ} (a : Twist.Mon n 1 ∅) :
    ∃ i : Fin (n + 1), a.val i = 1 ∧ ∀ j, j ≠ i → a.val j = 0 := by
  classical
  have hnonneg : ∀ j, 0 ≤ a.val j := fun j => not_lt.mp fun h =>
    (Finset.notMem_empty j) (a.property.2 ((Twist.mem_negSupp n).mpr h))
  obtain ⟨i, hi⟩ : ∃ i, a.val i ≠ 0 := by
    by_contra h
    have hz : ∀ i, a.val i = 0 := by simpa using h
    have := a.property.1
    simp only [hz, Finset.sum_const_zero] at this
    contradiction
  have hle : a.val i ≤ 1 := by
    calc
      a.val i ≤ ∑ j, a.val j := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ = 1 := a.property.1
  have hone : a.val i = 1 := by have := hnonneg i; omega
  refine ⟨i, hone, ?_⟩
  intro j hji
  have hsum : ∑ j ∈ Finset.univ.erase i, a.val j = 0 := by
    have h := Finset.sum_erase_add Finset.univ a.val (Finset.mem_univ i)
    rw [a.property.1, hone] at h
    omega
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum j
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

end HodgeLean.Foundations.Program.G32Native
