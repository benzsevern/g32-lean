import HodgeLean.Foundations.Program.NumeratorJetFieldRecurrence

/-! # Vanishing of diagonal convolution commutators -/

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

/-- The sum of all coefficient commutators at a single pole vanishes. -/
theorem b65e_diagonalCommutator_sum_zero
    {R : Type*} [CommRing R] (C : ℕ → Matrix (Fin 4) (Fin 4) R)
    (n : ℕ) :
    ∑ b ∈ Finset.range (n + 1), (C b * C (n - b) - C (n - b) * C b) = 0 := by
  rw [Finset.sum_sub_distrib]
  suffices h : (∑ b ∈ Finset.range (n + 1), C (n - b) * C b) =
      ∑ b ∈ Finset.range (n + 1), C b * C (n - b) by rw [h, sub_self]
  rw [← Finset.sum_range_reflect (fun b ↦ C b * C (n - b)) (n + 1)]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self (by omega : b ≤ n)]

end HodgeLean.Foundations.Program
