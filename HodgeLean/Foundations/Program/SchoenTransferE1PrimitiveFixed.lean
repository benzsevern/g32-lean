import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-! Rational elimination of a fixed vector in a primitive cyclotomic kernel. -/
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A fixed vector in a primitive cyclotomic kernel vanishes for order at least three.
Source: Schoen (1988), Lemma 1.1, p. 5; coprimality of distinct rational cyclotomic polynomials. -/
theorem s4_e1_primitive_fixed_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : Module.End ℚ V) (m : ℕ) (hm : 3 ≤ m) (x : V)
    (hx : f x = x)
    (hp : Polynomial.aeval f (Polynomial.cyclotomic m ℚ) x = 0) : x = 0 := by
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime f
    (Polynomial.cyclotomic.isCoprime_rat (show m ≠ 1 by omega))
  apply Submodule.disjoint_def.mp hd x hp
  simp only [LinearMap.mem_ker, Polynomial.cyclotomic_one, map_sub,
    Polynomial.aeval_X, Polynomial.aeval_one, Module.End.one_eq_id,
    LinearMap.sub_apply, LinearMap.id_apply, hx, sub_self]

#print axioms s4_e1_primitive_fixed_eq_zero
end HodgeLean.Foundations.Program
