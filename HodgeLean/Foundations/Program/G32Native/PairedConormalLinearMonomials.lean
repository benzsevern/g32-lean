import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialZeroEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Degree-one homogeneous monomials and their specified coordinate indices -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native

/-- The degree-one monomial of a specified homogeneous coordinate. -/
def conormalLinearMonomial (k : ℕ) (i : Fin (k + 1)) : Twist.Mon k 1 ∅ :=
  ⟨Pi.single i 1, by
    constructor
    · change (∑ j : Fin (k + 1), (Pi.single i 1 : Fin (k + 1) → ℤ) j) = 1
      simp [Pi.single_apply]
    · intro j hj
      have hj' := (Twist.mem_negSupp k).mp hj
      change (Pi.single i 1 : Fin (k + 1) → ℤ) j < 0 at hj'
      by_cases h : j = i
      · subst j; simpa using hj'
      · simp [Pi.single_apply, Ne.symm h] at hj'⟩

/-- Every degree-one monomial with no negative exponents is one specified coordinate. -/
theorem conormalLinearMonomial_surjective (k : ℕ) :
    Function.Surjective (conormalLinearMonomial k) := by
  intro a
  have hn (j : Fin (k + 1)) : 0 ≤ a.val j := by
    by_contra hj
    exact Finset.notMem_empty j (a.property.2 ((Twist.mem_negSupp k).mpr (by omega)))
  obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), a.val i ≠ 0 := by
    by_contra h
    push_neg at h
    have hs := a.property.1
    simp only [h, Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  have hi_le : a.val i ≤ ∑ j, a.val j :=
    Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
  have hi1 : a.val i = 1 := by rw [a.property.1] at hi_le; have := hn i; omega
  have hz : ∑ j ∈ Finset.univ.erase i, a.val j = 0 := by
    have hs := Finset.sum_erase_add (s := Finset.univ) a.val (Finset.mem_univ i)
    rw [a.property.1, hi1] at hs
    omega
  have hother (j : Fin (k + 1)) (hj : j ≠ i) : a.val j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz j (by simp [hj])
  refine ⟨i, Subtype.ext ?_⟩
  funext j
  change (Pi.single i 1 : Fin (k + 1) → ℤ) j = a.val j
  by_cases hj : j = i
  · subst j; simpa using hi1.symm
  · simp [Pi.single_apply, Ne.symm hj, hother j hj]

/-- Distinct homogeneous coordinate indices give distinct degree-one monomials. -/
theorem conormalLinearMonomial_injective (k : ℕ) :
    Function.Injective (conormalLinearMonomial k) := by
  intro i j h
  by_contra hij
  have hv := congrArg (fun a : Twist.Mon k 1 ∅ => a.val i) h
  change (Pi.single i 1 : Fin (k + 1) → ℤ) i =
    (Pi.single j 1 : Fin (k + 1) → ℤ) i at hv
  simpa [Ne.symm hij] using hv

/-- The degree-one monomial set has its original homogeneous coordinate indexing. -/
def conormalLinearMonomialEquiv (k : ℕ) : Fin (k + 1) ≃ Twist.Mon k 1 ∅ :=
  Equiv.ofBijective (conormalLinearMonomial k)
    ⟨conormalLinearMonomial_injective k, conormalLinearMonomial_surjective k⟩

end HodgeLean.Foundations.Program.G32Native
