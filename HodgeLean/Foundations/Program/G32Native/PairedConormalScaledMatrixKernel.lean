import HodgeLean.Foundations.Program.G32Native.PairedConormalKernelMatrixTransport

/-! # Scalar-compatible correction to the original projective kernel -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- The transposed actual coefficient matrix corrects a scaled relation
kernel over the same original projective point. -/
def conormalScaledMatrixKernelEquiv (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0)
    (r : ℂ × (Fin k → ℂ)) (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v) :
    LinearMap.ker (EulerModel.homogeneousNormalEvaluation k r) ≃ₗ[ℂ]
      EulerModel.projectiveNormalKernel k
        (Projectivization.mk ℂ ((EulerModel.normalHomogeneousCoordinates k).symm v)
          ((EulerModel.normalHomogeneousCoordinates k).symm.map_ne_zero_iff.mpr hv)) := by
  let e := EulerModel.normalHomogeneousCoordinates k
  have hr : r = c • e.symm (A.mulVec v) := by
    apply e.injective
    rw [hcoords, map_smul, LinearEquiv.apply_symm_apply]
  have hK : LinearMap.ker (EulerModel.homogeneousNormalEvaluation k r) =
      LinearMap.ker (EulerModel.homogeneousNormalEvaluation k (e.symm (A.mulVec v))) := by
    rw [hr, EulerModel.homogeneousNormalKernel_smul k _ c hc]
  exact (LinearEquiv.ofEq _ _ hK).trans
    ((conormalModelMatrixKernelEquiv k A hA v).trans
      (LinearEquiv.ofEq _ _ (EulerModel.projectiveNormalKernel_mk k (e.symm v)
        (e.symm.map_ne_zero_iff.mpr hv)).symm))

/-- Scalar normalization changes only kernel membership; the actual fibre
vector is corrected by the original transposed matrix. -/
theorem conormalScaledMatrixKernelEquiv_val (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (hv : v ≠ 0)
    (r : ℂ × (Fin k → ℂ)) (c : ℂ) (hc : c ≠ 0)
    (hcoords : EulerModel.normalHomogeneousCoordinates k r = c • A.mulVec v)
    (z : LinearMap.ker (EulerModel.homogeneousNormalEvaluation k r)) :
    (conormalScaledMatrixKernelEquiv k A hA v hv r c hc hcoords z).val =
      conormalModelMatrixDualEquiv k A hA z.val := by
  simp only [conormalScaledMatrixKernelEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]
  rfl

#print axioms conormalScaledMatrixKernelEquiv
#print axioms conormalScaledMatrixKernelEquiv_val
end HodgeLean.Foundations.Program.G32Native
