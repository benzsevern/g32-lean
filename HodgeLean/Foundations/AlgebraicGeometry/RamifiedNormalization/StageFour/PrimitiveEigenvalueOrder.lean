import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SlicePowers
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A nonzero evaluation transforming by a primitive scalar detects the exact order of the actual scheme endomorphism. -/
theorem endomorphism_order_of_primitive_evaluation
    {F : Over (Spec ↧ℂ)} (D : F ⟶ F) (m : ℕ) (hm : 0 < m)
    (hperiod : (End.of D) ^ m = 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (v : ComplexPoint F → ℂ) (hv : ∀ z, v (Point.map D z) = ζ * v z)
    (z : ComplexPoint F) (hz : v z ≠ 0) : orderOf (End.of D) = m := by
  have hiter (n : ℕ) : v ((Point.map D)^[n] z) = ζ ^ n * v z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hv, ih, pow_succ]
      ring
  apply (orderOf_eq_iff hm).mpr
  refine ⟨hperiod, ?_⟩
  intro n hnm hn hpow
  have he : (Point.map D)^[n] z = z := by
    rw [← point_map_end_pow, hpow]
    rfl
  have hroot : ζ ^ n = 1 := mul_right_cancel₀ hz
    ((hiter n).symm.trans (by rw [he, one_mul]))
  exact (Nat.not_dvd_of_pos_of_lt hn hnm) ((hζ.pow_eq_one_iff_dvd n).mp hroot)

end AlgebraicGeometry.RamifiedNormalization.StageFour
