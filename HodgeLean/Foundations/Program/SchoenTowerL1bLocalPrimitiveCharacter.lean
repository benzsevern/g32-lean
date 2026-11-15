import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A coprime signed local exponent permits choosing the primitive rescaling
root whose character is a prescribed primitive root. -/
theorem s2v_l1b_primitive_character_inverse
    {G : Type*} [CommGroup G] (ξ : G) (e : ℕ)
    (hξ : IsPrimitiveRoot ξ e) (n : ℤ) (hcop : Int.gcd n (e : ℤ) = 1) :
    ∃ ζ : G, IsPrimitiveRoot ζ e ∧ ζ ^ n = ξ := by
  let a := Int.gcdA n (e : ℤ)
  let b := Int.gcdB n (e : ℤ)
  have hbez : n * a + (e : ℤ) * b = 1 := by
    simpa only [hcop, Nat.cast_one] using (Int.gcd_eq_gcd_ab n (e : ℤ)).symm
  have hze : (ξ ^ a) ^ e = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hξ.zpow_eq_one, one_zpow]
  have hzn : (ξ ^ a) ^ n = ξ := by
    calc
      _ = ξ ^ (n * a) := by rw [← zpow_mul, mul_comm]
      _ = ξ ^ (n * a + (e : ℤ) * b) := by
        rw [zpow_add, zpow_mul ξ (e : ℤ) b, hξ.zpow_eq_one, one_zpow, mul_one]
      _ = ξ := by rw [hbez, zpow_one]
  refine ⟨ξ ^ a, ⟨hze, ?_⟩, hzn⟩
  intro l hl
  apply hξ.dvd_of_pow_eq_one l
  rw [← hzn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl, one_zpow]

/-- The coprime signed character construction applies to nonzero primitive
scalars in a field through their associated units. -/
theorem s2v_l1b_primitive_scalar_inverse
    {K : Type*} [Field K] (ξ : K) (e : ℕ) (he : e ≠ 0)
    (hξ : IsPrimitiveRoot ξ e) (n : ℤ) (hcop : Int.gcd n (e : ℤ) = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ e ∧ ζ ^ n = ξ := by
  obtain ⟨ζ, hζ, hzn⟩ := s2v_l1b_primitive_character_inverse
    (hξ.isUnit he).unit e (hξ.isUnit_unit he) n hcop
  refine ⟨ζ, IsPrimitiveRoot.coe_units_iff.mpr hζ, ?_⟩
  have hh : (ζ : K) ^ n = ((hξ.isUnit he).unit : K) := by exact_mod_cast hzn
  simpa only [IsUnit.unit_spec] using hh

end HodgeLean.Foundations.Program
