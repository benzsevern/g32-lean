import HodgeLean.Adapters.NormalConeB4aGysinEvaluationKernel
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

noncomputable section
set_option maxHeartbeats 400000
open Set HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A nonzero regular function on a Noetherian curve has finitely many scalar-valued zeros.
Source: finiteness of minimal primes over a nonzero ideal in dimension at most one. -/
theorem s0_finite_zero_evaluations
    {k T : Type*} [Field k] [CommRing T] [Algebra k T]
    [IsNoetherianRing T] [Ring.DimensionLEOne T] (f : T) (hf : f ≠ 0) :
    Set.Finite {w : T →ₐ[k] k | w f = 0} := by
  let I : Ideal T := Ideal.span {f}
  have hI : I ≠ ⊥ := by
    simpa [I, Ideal.span_singleton_eq_bot] using hf
  have hi : Function.Injective (fun w : T →ₐ[k] k ↦ RingHom.ker w) :=
    fun w w' h ↦ a3b4a_gysin_evaluation_eq_of_ker_eq w w' h
  apply ((Ideal.finite_minimalPrimes_of_isNoetherianRing T I).preimage hi.injOn).subset
  intro w hw
  letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  apply Ideal.mem_minimalPrimes_of_ne_bot hI
  rw [Ideal.span_le]
  intro t ht
  rcases Set.mem_singleton_iff.mp ht with rfl
  exact hw

#print axioms s0_finite_zero_evaluations
end HodgeLean.Foundations.Program
