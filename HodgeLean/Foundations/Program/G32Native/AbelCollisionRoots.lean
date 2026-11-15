import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact root paths for monic collision coefficients -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Powers of a specified primitive root retain unit top moments. -/
theorem collision_root_top_moment {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (i : Fin n) : (ζ ^ i.val) ^ n = 1 := by
  calc
    (ζ ^ i.val) ^ n = (ζ ^ n) ^ i.val := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = 1 := by rw [hζ.pow_eq_one, one_pow]

/-- The lower moments of the exact root path vanish. -/
theorem collision_root_lower_moment {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (∑ i : Fin n, (ζ ^ i.val) ^ k) = 0 := by
  have he : (∑ i : Fin n, (ζ ^ i.val) ^ k) = ∑ i ∈ Finset.range n, (ζ ^ k) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he]
  have htop : (ζ ^ k) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm k n, pow_mul, hζ.pow_eq_one, one_pow]
  have hne : ζ ^ k - 1 ≠ 0 := sub_ne_zero.mpr
    (hζ.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hk) hkn)
  apply (mul_eq_zero.mp ?_).resolve_right hne
  rw [geom_sum_mul, htop, sub_self]

/-- A primitive complex root exists in every positive degree. -/
theorem collision_primitive_root_exists {n : ℕ} (hn : 0 < n) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ n :=
  ⟨Complex.exp (2 * Real.pi * Complex.I / n), Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)⟩

#print axioms collision_root_top_moment
#print axioms collision_root_lower_moment
#print axioms collision_primitive_root_exists
end HodgeLean.Foundations.Program.G32Native
