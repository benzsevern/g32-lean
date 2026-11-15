import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Generic injectivity for finite free component modules -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Scalar extension along an injective scalar map detects elements of a flat module. -/
theorem union_flat_scalar_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (fun x : M => (1 : S) ⊗ₜ[R] x) := by
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (Algebra.linearMap R S) hRS
  intro x y hxy
  apply (TensorProduct.lid R M).symm.injective
  apply hi
  simpa only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
    Algebra.linearMap_apply, map_one] using hxy

/-- A map between finite free modules of equal rank is injective if it is
surjective after extension to a field containing the original ring. -/
theorem union_free_injective_of_generic_surjective
    {R K M N : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (hRK : Function.Injective (algebraMap R K))
    (hrank : Module.finrank R M = Module.finrank R N)
    (f : M →ₗ[R] N) (hf : Function.Surjective (f.baseChange K)) :
    Function.Injective f := by
  letI : Nontrivial R := ⟨⟨0, 1, fun h => zero_ne_one (by
    simpa only [map_zero, map_one] using congrArg (algebraMap R K) h)⟩⟩
  have hr : Module.finrank K (K ⊗[R] M) = Module.finrank K (K ⊗[R] N) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hrank]
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mpr hf
  intro x y hxy
  apply union_flat_scalar_injective hRK
  apply hi
  simpa only [LinearMap.baseChange_tmul] using
    congrArg (fun z : N => (1 : K) ⊗ₜ[R] z) hxy

#print axioms union_flat_scalar_injective
#print axioms union_free_injective_of_generic_surjective

end HodgeLean.Foundations.Program.G32Native
