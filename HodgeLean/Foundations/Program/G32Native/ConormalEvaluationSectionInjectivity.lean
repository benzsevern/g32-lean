import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Injectivity from evaluation on a section of the dual

A covector family is injective if its vectors realize every functional on
the original conormal space.
-/

namespace HodgeLean.Foundations.TubularEuler

theorem conormal_injective_of_dual_evaluation_section
    {K V E : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    (D : V →ₗ[K] Module.Dual K E) (L : Module.Dual K V →ₗ[K] E)
    (hL : ∀ u a, D a (L u) = u a) : Function.Injective D := by
  intro a b hab
  have heq : ∀ u : Module.Dual K V, u a = u b := by
    intro u
    calc
      u a = D a (L u) := (hL u a).symm
      _ = D b (L u) := congrArg (fun f : Module.Dual K E => f (L u)) hab
      _ = u b := hL u b
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff K (a - b)).mp
  intro u
  rw [map_sub, heq u, sub_self]

#print axioms conormal_injective_of_dual_evaluation_section

theorem finrank_range_of_injective_of_dual_equiv
    {K V E : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (D : V →ₗ[K] E) (hi : Function.Injective D)
    (k : ℕ) (e : Module.Dual K V ≃ₗ[K] (Fin k → K)) :
    Module.finrank K D.range = k := by
  letI := FiniteDimensional.of_injective D hi
  calc
    Module.finrank K D.range = Module.finrank K V := LinearMap.finrank_range_of_inj hi
    _ = Module.finrank K (Module.Dual K V) := Subspace.dual_finrank_eq.symm
    _ = Module.finrank K (Fin k → K) := e.finrank_eq
    _ = k := by simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]

#print axioms finrank_range_of_injective_of_dual_equiv

theorem conormal_injective_of_evaluation_family
    {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    (D : V → E → K) (L : Module.Dual K V → E)
    (hL : ∀ u a, D a (L u) = u a) : Function.Injective D := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff K (a - b)).mp
  intro u
  rw [map_sub, ← hL u a, ← hL u b, hab, sub_self]

#print axioms conormal_injective_of_evaluation_family
end HodgeLean.Foundations.TubularEuler
