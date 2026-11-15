import HodgeLean.Foundations.HodgeLieAlgebra
import HodgeLean.Blocks.HodgeStructure.HodgeClass

/-! # Adapter: Blocks' Hodge classes are the invariants of the Hodge Lie algebra

Instantiates Foundations target T6 (`HodgeLean.Foundations.HodgeLieAlgebra`) for Blocks'
`HodgeBlocks.QHodgeStructure`: its pieces `M.H` and `M.isInternal` are the raw data of the
Foundations file, Blocks' conjugation `sigmaQR` is the Foundations `complexConj`, and
`HodgeBlocks.IsHodgeClass M v` holds exactly when `hodgeLieAlgebra M.H M.isInternal` kills `v`.

Relation to the goal: HC no distance; AV milestone no distance; F-1575 step 2 ("the Hodge ring is
the invariant ring of the Hodge group") becomes statable for Blocks' Hodge structures.
-/

open TensorProduct

namespace HodgeLean.Adapters

open HodgeLean.Foundations HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

omit [Module.Finite ℚ V] in
/-- Blocks' rational conjugation `sigmaQR` is the Foundations `complexConj`. -/
theorem sigmaQR_eq_complexConj : sigmaQR V = complexConj V := by
  ext z v
  simp

/-- The pieces of a Blocks Hodge structure are conjugation-symmetric in the Foundations sense. -/
theorem complexConj_mem_H {n : ℤ} (M : QHodgeStructure n V) (p q : ℤ) (x : ℂ ⊗[ℚ] V)
    (hx : x ∈ M.H (p, q)) : complexConj V x ∈ M.H (q, p) := by
  rw [← M.conj_symm p q, ← sigmaQR_eq_complexConj]
  exact ⟨x, hx, rfl⟩

/-- The grading operator of a Blocks Hodge structure commutes with complex conjugation. -/
theorem gradingOperator_complexConj_of_qHodgeStructure {n : ℤ} (M : QHodgeStructure n V)
    (x : ℂ ⊗[ℚ] V) :
    gradingOperator M.H M.isInternal (complexConj V x) =
      complexConj V (gradingOperator M.H M.isInternal x) :=
  gradingOperator_complexConj M.H M.isInternal (complexConj_mem_H M) x

/-- **Blocks' Hodge classes are the invariants of the Hodge Lie algebra.** For a Hodge structure
of weight `2p`, `IsHodgeClass M v` holds if and only if `hodgeLieAlgebra M.H M.isInternal`
kills `v`. -/
theorem isHodgeClass_iff_mem_maxTrivSubmodule {p : ℤ} (M : QHodgeStructure (2 * p) V) (v : V) :
    IsHodgeClass M v ↔
      v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra M.H M.isInternal) V := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff_of_pure M.H M.isInternal
    (fun a b h => M.supported (a, b) h), IsHodgeClass, complexify_apply,
    Int.mul_ediv_cancel_left p two_ne_zero]
  constructor
  · intro h
    exact Or.inr ⟨even_two_mul p, h⟩
  · rintro (rfl | ⟨-, h⟩)
    · rw [TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
    · exact h

/-- In odd weight only `0` is killed by the Hodge Lie algebra. -/
theorem mem_maxTrivSubmodule_iff_eq_zero_of_odd {n : ℤ} (hn : Odd n) (M : QHodgeStructure n V)
    (v : V) : v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra M.H M.isInternal) V ↔ v = 0 := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff_of_pure M.H M.isInternal
    (fun a b h => M.supported (a, b) h)]
  have : ¬ Even n := Int.not_even_iff_odd.mpr hn
  tauto

end HodgeLean.Adapters
