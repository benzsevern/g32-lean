import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-! # Primitive classes and shorter periods

HC no distance; AV milestone no distance.
-/
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A primitive class cannot be fixed by a power whose exponent is not a multiple
of its cyclotomic order.
Source: Schoen (1988), Lemma 1.1, p. 5; rational cyclotomic coprimality.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_primitive_period_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (m d : ℕ) (hd : 0 < d) (hmd : ¬ m ∣ d)
    (v : V) (hprimitive : Polynomial.aeval T (Polynomial.cyclotomic m ℚ) v = 0)
    (hperiod : (T ^ d) v = v) : v = 0 := by
  have hcop : IsCoprime (Polynomial.cyclotomic m ℚ)
      (Polynomial.X ^ d - 1 : Polynomial ℚ) := by
    rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℚ]
    apply IsCoprime.prod_right
    intro j hj
    apply Polynomial.cyclotomic.isCoprime_rat
    intro hmj
    subst j
    exact hmd (Nat.mem_divisors.mp hj).1
  have hdis := Polynomial.disjoint_ker_aeval_of_isCoprime T hcop
  apply Submodule.disjoint_def.mp hdis v hprimitive
  simp only [LinearMap.mem_ker, map_sub, map_pow, Polynomial.aeval_X,
    map_one, LinearMap.sub_apply, Module.End.one_apply, hperiod, sub_self]

#print axioms s4_assembly_primitive_period_eq_zero
end HodgeLean.Foundations.Program
