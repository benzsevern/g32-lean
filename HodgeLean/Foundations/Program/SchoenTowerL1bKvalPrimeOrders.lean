import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Prime orders of nonzero products add as integers. -/
theorem s2v_l1b_kval_prime_order_mul
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {p a b : R} (hp : Prime p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((emultiplicity p (a * b)).toNat : ℤ) =
      ((emultiplicity p a).toNat : ℤ) + ((emultiplicity p b).toNat : ℤ) := by
  rw [emultiplicity_mul hp, ENat.toNat_add
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp (FiniteMultiplicity.of_prime_left hp ha))
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp (FiniteMultiplicity.of_prime_left hp hb)), Nat.cast_add]

/-- The integer order of a rational function does not depend on its numerator presentation. -/
theorem s2v_l1b_kval_fraction_order_eq
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field K]
    (ρ : R →+* K) (hρ : Function.Injective ρ)
    {a b c d p : R} (hp : Prime p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (heq : ρ a / ρ b = ρ c / ρ d) :
    ((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ) =
      ((emultiplicity p c).toNat : ℤ) - ((emultiplicity p d).toNat : ℤ) := by
  have hb' : ρ b ≠ 0 := fun h => hb (hρ (h.trans ρ.map_zero.symm))
  have hd' : ρ d ≠ 0 := fun h => hd (hρ (h.trans ρ.map_zero.symm))
  have hcross : a * d = c * b := by
    apply hρ
    simpa only [map_mul] using (div_eq_div_iff hb' hd').mp heq
  have ho := congrArg (fun z : R => ((emultiplicity p z).toNat : ℤ)) hcross
  rw [s2v_l1b_kval_prime_order_mul hp ha hd,
    s2v_l1b_kval_prime_order_mul hp hc hb] at ho
  omega

end HodgeLean.Foundations.Program
