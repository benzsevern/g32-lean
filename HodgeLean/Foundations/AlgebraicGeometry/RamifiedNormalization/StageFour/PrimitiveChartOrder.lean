import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PrimitiveEigenvalueOrder

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A primitive integral evaluation on one injectively parametrized invariant chart detects the exact actual scheme order. -/
theorem endomorphism_order_of_primitive_chart_evaluation
    {F : Over (Spec ↧ℂ)} (D : F ⟶ F) (m : ℕ) (hm : 0 < m)
    (hperiod : (End.of D) ^ m = 1)
    {C : Type} (f : C → C) (H : C → ComplexPoint F) (hH : Function.Injective H)
    (hD : ∀ z, H (f z) = Point.map D (H z))
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (v : C → ℂ) (hv : ∀ z, v (f z) = ζ * v z) (z : C) (hz : v z ≠ 0) :
    orderOf (End.of D) = m := by
  have hiter (n : ℕ) : H (f^[n] z) = (Point.map D)^[n] (H z) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hD, ih, Function.iterate_succ_apply']
  have heval (n : ℕ) : v (f^[n] z) = ζ ^ n * v z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', hv, ih, pow_succ]
      ring
  apply (orderOf_eq_iff hm).mpr
  refine ⟨hperiod, ?_⟩
  intro n hnm hn hpow
  have hpoint : (Point.map D)^[n] (H z) = H z := by
    rw [← point_map_end_pow, hpow]
    rfl
  have hreturn : f^[n] z = z := hH ((hiter n).trans hpoint)
  have hroot : ζ ^ n = 1 := mul_right_cancel₀ hz
    ((heval n).symm.trans (by rw [hreturn, one_mul]))
  exact (Nat.not_dvd_of_pos_of_lt hn hnm) ((hζ.pow_eq_one_iff_dvd n).mp hroot)

end AlgebraicGeometry.RamifiedNormalization.StageFour
