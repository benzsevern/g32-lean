import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A regular parameter remains regular in a Noetherian adic ring. -/
theorem s2v_l1b_adic_parameter_regular
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (p : R) (hp : Function.Injective (fun x : R => p * x)) :
    Function.Injective (fun x : AdicCompletion I R =>
      algebraMap R (AdicCompletion I R) p * x) := by
  let f : R →ₗ[R] R := p • LinearMap.id
  have hf : Function.Injective f := hp
  have hh := AdicCompletion.map_injective (I := I) hf
  have heq (x : AdicCompletion I R) :
      AdicCompletion.map I f x = algebraMap R (AdicCompletion I R) p * x := by
    have h1 : AdicCompletion.map I f 1 = algebraMap R (AdicCompletion I R) p := by
      change AdicCompletion.map I f (AdicCompletion.of I R 1) = _
      rw [AdicCompletion.map_of]
      change AdicCompletion.of I R (p * 1) = _
      rw [mul_one]
      rfl
    calc
      AdicCompletion.map I f x = AdicCompletion.map I f (x • (1 : AdicCompletion I R)) := by
        rw [smul_eq_mul, mul_one]
      _ = x • AdicCompletion.map I f 1 := (AdicCompletion.map I f).map_smul x 1
      _ = _ := by rw [h1, smul_eq_mul, mul_comm]
  intro x y h
  apply hh
  rw [heq, heq]
  exact h

end HodgeLean.Foundations.Program
