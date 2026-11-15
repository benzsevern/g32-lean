import HodgeLean.Ported.Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-! Linearity of fractions with a fixed exceptional denominator. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Division by a chart denominator is linear on the centre ideal. -/
def g32l4_blowUp_ratioLinearMap {R : Type} [CommRing R] (I : Ideal R) (a : I) :
    I →ₗ[R] affineBlowUpAlgebra I a where
  toFun b := affineBlowUpAlgebra.ratio I a b
  map_add' b c := by
    apply (mul_cancel_left_mem_nonZeroDivisors
      (affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors (I := I) (a := a))).mp
    rw [mul_add, ← algebraMap_eq_mul_ratio, ← algebraMap_eq_mul_ratio,
      ← algebraMap_eq_mul_ratio]
    exact map_add _ _ _
  map_smul' r b := by
    apply (mul_cancel_left_mem_nonZeroDivisors
      (affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors (I := I) (a := a))).mp
    rw [← algebraMap_eq_mul_ratio]
    simp only [RingHom.id_apply, Submodule.coe_smul, smul_eq_mul, Algebra.smul_def]
    change algebraMap R (affineBlowUpAlgebra I a) (r * (b : R)) =
      algebraMap R (affineBlowUpAlgebra I a) a *
        (algebraMap R (affineBlowUpAlgebra I a) r * affineBlowUpAlgebra.ratio I a b)
    rw [map_mul, algebraMap_eq_mul_ratio I a b]
    ring

end HodgeLean.Foundations.Program
