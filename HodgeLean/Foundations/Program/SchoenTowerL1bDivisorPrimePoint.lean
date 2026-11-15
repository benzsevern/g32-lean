import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkSpectrum
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A prime element in the specified stalk determines an actual codimension-one scheme point. -/
theorem s2v_l1b_divisor_prime_stalk_point_coheight
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (p : X.presheaf.stalk x) (hp : Prime p) :
    let P := Ideal.span ({p} : Set (X.presheaf.stalk x))
    letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    Order.coheight ((X.fromSpecStalk x) (⟨P, inferInstance⟩ : Spec (X.presheaf.stalk x))) = 1 := by
  let P := Ideal.span ({p} : Set (X.presheaf.stalk x))
  letI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  change Order.coheight ((X.fromSpecStalk x)
    (⟨P, inferInstance⟩ : Spec (X.presheaf.stalk x))) = 1
  rw [s2v_l1b_divisor_stalk_spectrum_coheight, ← idealHeight_eq_coheight]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero) hp.not_isUnit

end HodgeLean.Foundations.Program
