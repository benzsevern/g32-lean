import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A trivialization of an ideal supplies a principal generator with injective multiplication. -/
theorem s2v_l1b_generator_of_ideal_trivialization
    {R : Type*} [CommRing R] (I : Ideal R) (e : I ≃ₗ[R] R) :
    ∃ a : R, I = Ideal.span {a} ∧ Function.Injective (fun r : R => r * a) := by
  let a : I := e.symm 1
  have hmul : ∀ r : R, r • a = e.symm r := by
    intro r
    dsimp [a]
    rw [← map_smul, smul_eq_mul, mul_one]
  refine ⟨a.val, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      have hx' : x = e ⟨x, hx⟩ * a.val := by
        have he := congrArg Subtype.val (hmul (e ⟨x, hx⟩))
        simpa only [LinearEquiv.symm_apply_apply, Submodule.coe_smul,
          smul_eq_mul] using he.symm
      rw [hx']
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a.property)
  · intro r s hrs
    have hsub : r • a = s • a := Subtype.ext hrs
    rw [hmul, hmul] at hsub
    exact e.symm.injective hsub

/-- Images of the regular generators of finitely many trivialized ideals have nonzero product. -/
theorem s2v_l1b_trivialized_ideal_product_nonzero
    {R K : Type*} [CommRing R] [Nontrivial R] [Field K]
    (ρ : R →+* K) (hρ : Function.Injective ρ)
    {J : Type*} [Fintype J] (I : J → Ideal R)
    (e : ∀ j, I j ≃ₗ[R] R) :
    ∃ a : J → R, (∀ j, I j = Ideal.span {a j}) ∧ ρ (∏ j, a j) ≠ 0 := by
  choose a ha hreg using fun j => s2v_l1b_generator_of_ideal_trivialization (I j) (e j)
  refine ⟨a, ha, ?_⟩
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have hne : a j ≠ 0 := by
    intro hz
    have heq : (0 : R) * a j = 1 * a j := by rw [hz, mul_zero, mul_zero]
    exact zero_ne_one (hreg j heq)
  exact fun hz => hne (hρ (by rw [hz, map_zero]))

end HodgeLean.Foundations.Program
