import HodgeLean.Foundations.Program.SchoenTransferComplexOneCup
import HodgeLean.Foundations.Program.SchoenTransferAlternatingCoordinates

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The actual complex tensor cup followed by alternation has the specified factorial normalization. -/
theorem s4_complexOneCup_tensorAlternation
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    (s4_complexOneCup Y h).comp (exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) h) =
      (Nat.factorial h : ℂ) • s4_e2_alternatingCup Y h := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, exteriorPower.toTensorPower_apply_ιMulti, map_sum,
    Units.smul_def, map_zsmul, s4_complexOneCup, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply]
  exact (s4_alternatingCup_coordinates Y h v).symm

/-- The normalized alternating map is the factorial inverse times the actual tensor cup image. -/
theorem s4_alternatingCup_eq_complex_tensor
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    s4_e2_alternatingCup Y h = (Nat.factorial h : ℂ)⁻¹ •
      (s4_complexOneCup Y h).comp (exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) h) := by
  rw [s4_complexOneCup_tensorAlternation, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)), one_smul]

end HodgeLean.Foundations.Program
