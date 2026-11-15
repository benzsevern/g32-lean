import HodgeLean.Foundations.Program.MilneTensorDefs
import HodgeLean.Foundations.Program.G32WeilLineAssemblyCupSpan

/-! # Independent boundary checks for Milne M3

These examples use existing constructions and verified library results.
They import none of the M1 tensor or M3 auxiliary statements.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

-- The normalized alternating lift is a section, even in degree zero.
example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    InvariantsExterior.wedgeQuotient n (m0_tensorLift J r n v) = v := by
  simp only [m0_tensorLift, LinearMap.smul_apply, map_smul,
    InvariantsExterior.wedgeQuotient_toTensorPower, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]

-- Scalar multiplication survives the empty tensor and exterior constructions.
example : InvariantsExterior.wedgeQuotient (K := ℂ) (M := Fin 0 → ℂ) 0
    (PiTensorProduct.tprod ℂ Fin.elim0) =
      exteriorPower.ιMulti ℂ 0 Fin.elim0 :=
  InvariantsExterior.wedgeQuotient_tprod 0 Fin.elim0

-- Multiplication of algebraic spans uses the existing theorem, in arbitrary degrees.
example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (p q : ℕ)
    (a : ℂ ⊗[ℚ] HQ J (2 * p)) (b : ℂ ⊗[ℚ] HQ J (2 * q))
    (ha : a ∈ (algebraicCycleClassSpan J p).baseChange ℂ)
    (hb : b ∈ (algebraicCycleClassSpan J q).baseChange ℂ) :
    (cupProductOf J).cupC (by omega : 2 * p + 2 * q = 2 * (p + q)) a b ∈
      (algebraicCycleClassSpan J (p + q)).baseChange ℂ :=
  g32c_cupC_span J p q (p + q) (by omega) a b ha hb

end HodgeLean.Foundations.Program
