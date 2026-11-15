import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerLinearRetraction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- Scaling a degree-one tensor action scales its actual ordered cup by the corresponding power.
Source: multilinearity of the actual degree-one cup map. -/
theorem s4_selected_tensor_cup_scalar
    (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (n : ℕ) (c : ℚ) (R : V →ₗ[ℚ] HQ A 1) :
    (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
      (PiTensorProduct.map (fun _ : Fin n => c • R)) =
    c ^ n • (PiTensorProduct.lift ((cupProductOf A).cupMulti n)).comp
      (PiTensorProduct.map (fun _ : Fin n => R)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
  change (cupProductOf A).cupMulti n (fun i => c • R (v i)) =
    c ^ n • (cupProductOf A).cupMulti n (fun i => R (v i))
  rw [MultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

#print axioms s4_selected_tensor_cup_scalar
end HodgeLean.Foundations.Program
