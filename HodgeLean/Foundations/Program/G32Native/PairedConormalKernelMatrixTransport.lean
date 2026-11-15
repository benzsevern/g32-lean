import HodgeLean.Foundations.Program.G32Native.PairedConormalActualRelationMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme
import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalKernel

/-! # Literal coefficient matrices and the prescribed homogeneous evaluation kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open Matrix
namespace HodgeLean.Foundations.Program.G32Native

/-- The prescribed model pairing is the actual ordered homogeneous coordinate dot product. -/
theorem conormal_model_evaluation_dotProduct (k : ℕ) (v w : ℂ × (Fin k → ℂ)) :
    EulerModel.homogeneousNormalEvaluation k v w =
      EulerModel.normalHomogeneousCoordinates k v ⬝ᵥ EulerModel.normalHomogeneousCoordinates k w := by
  rw [EulerModel.homogeneousNormalEvaluation_apply, dotProduct, Fin.sum_univ_succ]
  rfl

/-- The actual complex-linear dual action of an invertible coordinate matrix
in the prescribed model's leading-coordinate and tail coordinates. -/
def conormalModelMatrixDualEquiv (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A) :
    (ℂ × (Fin k → ℂ)) ≃ₗ[ℂ] (ℂ × (Fin k → ℂ)) :=
  ((EulerModel.normalHomogeneousCoordinates k).trans
    (LinearEquiv.ofBijective A.transpose.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_transpose A).mpr hA),
        Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_transpose A).mpr hA)⟩)).trans
      (EulerModel.normalHomogeneousCoordinates k).symm

/-- The specified dual action is the literal transposed matrix on the actual ordered coordinates. -/
theorem conormal_model_matrix_dual_coordinates (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (w : ℂ × (Fin k → ℂ)) :
    EulerModel.normalHomogeneousCoordinates k (conormalModelMatrixDualEquiv k A hA w) =
      A.transpose.mulVec (EulerModel.normalHomogeneousCoordinates k w) := by
  change EulerModel.normalHomogeneousCoordinates k
    ((EulerModel.normalHomogeneousCoordinates k).symm
      (A.transpose.mulVec (EulerModel.normalHomogeneousCoordinates k w))) = _
  exact (EulerModel.normalHomogeneousCoordinates k).apply_symm_apply _

/-- The actual transposed dual action preserves precisely the prescribed homogeneous evaluation pairing. -/
theorem conormal_model_matrix_dual_evaluation (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) (w : ℂ × (Fin k → ℂ)) :
    EulerModel.homogeneousNormalEvaluation k ((EulerModel.normalHomogeneousCoordinates k).symm v)
      (conormalModelMatrixDualEquiv k A hA w) =
    EulerModel.homogeneousNormalEvaluation k
      ((EulerModel.normalHomogeneousCoordinates k).symm (A.mulVec v)) w := by
  rw [conormal_model_evaluation_dotProduct, conormal_model_evaluation_dotProduct]
  simp only [LinearEquiv.apply_symm_apply, conormal_model_matrix_dual_coordinates]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- The actual dual matrix action restricts to the prescribed evaluation kernels. -/
def conormalModelMatrixKernelEquiv (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : IsUnit A)
    (v : Fin (k + 1) → ℂ) :
    LinearMap.ker (EulerModel.homogeneousNormalEvaluation k
      ((EulerModel.normalHomogeneousCoordinates k).symm (A.mulVec v))) ≃ₗ[ℂ]
    LinearMap.ker (EulerModel.homogeneousNormalEvaluation k
      ((EulerModel.normalHomogeneousCoordinates k).symm v)) :=
  (conormalModelMatrixDualEquiv k A hA).ofSubmodules _ _ (by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      change EulerModel.homogeneousNormalEvaluation k
        ((EulerModel.normalHomogeneousCoordinates k).symm v)
        (conormalModelMatrixDualEquiv k A hA z) = 0
      rw [conormal_model_matrix_dual_evaluation]
      exact hz
    · intro hw
      refine ⟨(conormalModelMatrixDualEquiv k A hA).symm w, ?_,
        (conormalModelMatrixDualEquiv k A hA).apply_symm_apply w⟩
      change EulerModel.homogeneousNormalEvaluation k
        ((EulerModel.normalHomogeneousCoordinates k).symm (A.mulVec v))
        ((conormalModelMatrixDualEquiv k A hA).symm w) = 0
      rw [← conormal_model_matrix_dual_evaluation k A hA v,
        LinearEquiv.apply_symm_apply]
      exact hw)

end HodgeLean.Foundations.Program.G32Native
