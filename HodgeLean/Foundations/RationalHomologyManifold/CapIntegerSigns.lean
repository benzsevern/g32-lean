import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Field.Rat

/-! Actual Alexander–Whitney signs under additive coefficient-forgetting maps.
HC no distance; AV milestone no distance.
-/
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Additive maps preserve the rational cap sign as its actual integral action in the target.
Source: Hatcher, Algebraic Topology, section 3.3; the cap differential sign is an integral unit.
HC no distance; AV milestone no distance.
-/
theorem map_cap_sign {A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B]
    (f : A →+ B) (p : ℕ) (a : A) :
    f ((-1 : ℚ) ^ p • a) = (-1 : ℤ) ^ p • f a := by
  have hs : (-1 : ℚ) ^ p = (((-1 : ℤ) ^ p : ℤ) : ℚ) := by simp
  rw [hs, Int.cast_smul_eq_zsmul, map_zsmul]

#print axioms map_cap_sign
end HodgeLean.Foundations.RationalHomologyManifold
