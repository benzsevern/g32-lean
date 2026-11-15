import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Abelian

namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable {k : Type*} [CommRing k]
variable {L L' : Type*} [LieRing L] [LieAlgebra k L] [LieRing L'] [LieAlgebra k L']

/-- Simplicity passes through an equivalence of Lie algebras. -/
theorem pel_simple_lieEquiv (e : L ≃ₗ⁅k⁆ L') [LieAlgebra.IsSimple k L] :
    LieAlgebra.IsSimple k L' := by
  constructor
  · intro I
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (I.comap e.toLieHom) with hI | hI
    · left
      apply le_antisymm _ bot_le
      intro x hx
      have h : e.symm x ∈ I.comap e.toLieHom := by
        change e (e.symm x) ∈ I
        simpa only [e.apply_symm_apply] using hx
      rw [hI, LieSubmodule.mem_bot] at h
      rw [← e.apply_symm_apply x, h, map_zero]
      exact (⊥ : LieIdeal k L').zero_mem
    · right
      rw [eq_top_iff]
      intro x _
      have h : e.symm x ∈ I.comap e.toLieHom := by rw [hI]; trivial
      change e (e.symm x) ∈ I at h
      simpa only [e.apply_symm_apply] using h
  · intro h
    exact LieAlgebra.IsSimple.non_abelian k ((lie_abelian_iff_equiv_lie_abelian e).mpr h)

end HodgeLean.Foundations.Program.GeneralTypeIII
