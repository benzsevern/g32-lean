import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerExtraction
import HodgeLean.Foundations.Program.SchoenTransferAlternatingNormalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped DirectSum TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Apply a degree-one retraction in every extracted curve factor, then take the normalized cup. -/
def s4_selected_curve_power_linear_retraction
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (R : HQ Y 1 →ₗ[ℚ] HQ A 1) : HQ (g3_power Y n) n →ₗ[ℚ] HQ A n :=
  (Nat.factorial n : ℚ)⁻¹ •
    (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
      ((PiTensorProduct.map (fun _ : Fin n => R)).comp
        (s4_selected_curve_power_extract Y hdim n))

/-- The normalized tensor retraction recovers the exterior cup map on alternating degree-one inputs. -/
theorem s4_selected_curve_power_retraction_alternating
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (L : HQ A 1 →ₗ[ℚ] HQ Y 1) (R : HQ Y 1 →ₗ[ℚ] HQ A 1)
    (hRL : R.comp L = LinearMap.id) :
    (s4_selected_curve_power_linear_retraction A Y hdim n R).comp
      ((s4_e1_oneCup Y n).comp ((PiTensorProduct.map (fun _ : Fin n => L)).comp
        (exteriorPower.toTensorPower ℚ (HQ A 1) n))) = (cupProductOf A).cupWedgeMap n := by
  have hmaps : (PiTensorProduct.map (fun _ : Fin n => R)).comp
      (PiTensorProduct.map (fun _ : Fin n => L)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hRL, PiTensorProduct.map_id]
  apply LinearMap.ext
  intro x
  change (Nat.factorial n : ℚ)⁻¹ •
    (PiTensorProduct.lift ((cupProductOf A).cupMulti n))
      ((PiTensorProduct.map (fun _ : Fin n => R))
        (s4_selected_curve_power_extract Y hdim n
          (s4_e1_oneCup Y n ((PiTensorProduct.map (fun _ : Fin n => L))
            (exteriorPower.toTensorPower ℚ (HQ A 1) n x))))) = _
  have he := LinearMap.congr_fun (s4_selected_curve_power_extract_oneCup Y hdim n)
    ((PiTensorProduct.map (fun _ : Fin n => L))
      (exteriorPower.toTensorPower ℚ (HQ A 1) n x))
  change s4_selected_curve_power_extract Y hdim n (s4_e1_oneCup Y n _) = _ at he
  simp only [LinearMap.id_apply] at he
  have hmapped := LinearMap.congr_fun hmaps
    (exteriorPower.toTensorPower ℚ (HQ A 1) n x)
  change (PiTensorProduct.map (fun _ : Fin n => R))
    ((PiTensorProduct.map (fun _ : Fin n => L))
      (exteriorPower.toTensorPower ℚ (HQ A 1) n x)) = _ at hmapped
  simp only [LinearMap.id_apply] at hmapped
  rw [he, hmapped]
  have ha := LinearMap.congr_fun (tensor_alternation_factorial n ((cupProductOf A).cupAlternating n)) x
  change (PiTensorProduct.lift ((cupProductOf A).cupMulti n))
      (exteriorPower.toTensorPower ℚ (HQ A 1) n x) =
    (Nat.factorial n) • ((cupProductOf A).cupWedgeMap n x) at ha
  rw [ha, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

#print axioms s4_selected_curve_power_retraction_alternating
end HodgeLean.Foundations.Program
