import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.ZMod.Basic

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- One integer exponent describes every value of the original cyclic
complex character in the fixed standard rotation coordinates. -/
theorem s2e_c1_cyclic_character_phase
    (m : ℕ) (hm : 0 < m) (χ : Multiplicative (ZMod m) →* ℂˣ) :
    ∃ a : ℕ, a < m ∧ ∀ k : ℕ,
      (χ (Multiplicative.ofAdd (k : ZMod m)) : ℂ) =
        Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ (a * k) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have htag (k : ℕ) : Multiplicative.ofAdd (k : ZMod m) =
      (Multiplicative.ofAdd (1 : ZMod m)) ^ k := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  have hp (k : ℕ) : (χ (Multiplicative.ofAdd (k : ZMod m)) : ℂ) =
      (χ (Multiplicative.ofAdd (1 : ZMod m)) : ℂ) ^ k := by
    rw [htag, map_pow, Units.val_pow_eq_pow_val]
  have hroot : (χ (Multiplicative.ofAdd (1 : ZMod m)) : ℂ) ^ m = 1 := by
    rw [← hp m, ZMod.natCast_self]
    change (χ (1 : Multiplicative (ZMod m)) : ℂ) = 1
    rw [map_one, Units.val_one]
  obtain ⟨a, ha, he⟩ := (Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hm)).eq_pow_of_pow_eq_one hroot
  refine ⟨a, ha, fun k => ?_⟩
  rw [hp, ← he, pow_mul]

end HodgeLean.Foundations.Program
