import HodgeLean.Foundations.Program.G32Native.PairedConormalKernelMatrixTransport
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Dual coordinates of the prescribed homogeneous evaluation pairing -/
noncomputable section
set_option maxHeartbeats 200000
open Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The ordered homogeneous coordinates identify the actual algebraic dual
with the vector space used in the prescribed kernel model. -/
def conormalModelDualCoordinates (k : ℕ) :
    (ℂ × (Fin k → ℂ)) ≃ₗ[ℂ] Dual ℂ (ℂ × (Fin k → ℂ)) :=
  (EulerModel.normalHomogeneousCoordinates k).trans
    ((Pi.basisFun ℂ (Fin (k + 1))).toDualEquiv.trans
      (EulerModel.normalHomogeneousCoordinates k).dualMap)

/-- Each literal coordinate vector evaluates to its specified dual coordinate. -/
theorem conormal_model_dual_coordinate (k : ℕ) (w : ℂ × (Fin k → ℂ))
    (i : Fin (k + 1)) :
    conormalModelDualCoordinates k w
      ((EulerModel.normalHomogeneousCoordinates k).symm (Pi.single i 1)) =
      EulerModel.normalHomogeneousCoordinates k w i := by
  change (Pi.basisFun ℂ (Fin (k + 1))).toDual
    (EulerModel.normalHomogeneousCoordinates k w)
    (EulerModel.normalHomogeneousCoordinates k
      ((EulerModel.normalHomogeneousCoordinates k).symm (Pi.single i 1))) = _
  rw [LinearEquiv.apply_symm_apply]
  simpa using (Pi.basisFun ℂ (Fin (k + 1))).toDual_apply_left
    (EulerModel.normalHomogeneousCoordinates k w) i

/-- The ordered dual coordinate equivalence is exactly the prescribed bilinear pairing. -/
theorem conormal_model_dual_evaluation (k : ℕ) (w v : ℂ × (Fin k → ℂ)) :
    conormalModelDualCoordinates k w v = EulerModel.homogeneousNormalEvaluation k w v := by
  let e := EulerModel.normalHomogeneousCoordinates k
  have h : (conormalModelDualCoordinates k w).comp e.symm.toLinearMap =
      (EulerModel.homogeneousNormalEvaluation k w).comp e.symm.toLinearMap := by
    apply (Pi.basisFun ℂ (Fin (k + 1))).ext
    intro i
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    change conormalModelDualCoordinates k w (e.symm (Pi.single i 1)) =
      EulerModel.homogeneousNormalEvaluation k w (e.symm (Pi.single i 1))
    rw [conormal_model_dual_coordinate, conormal_model_evaluation_dotProduct]
    simp only [e, LinearEquiv.apply_symm_apply, dotProduct_single_one]
  have hv := LinearMap.congr_fun h (e v)
  change conormalModelDualCoordinates k w (e.symm (e v)) =
    EulerModel.homogeneousNormalEvaluation k w (e.symm (e v)) at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

end HodgeLean.Foundations.Program.G32Native
