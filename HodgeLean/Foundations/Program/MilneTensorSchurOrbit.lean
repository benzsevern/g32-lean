import HodgeLean.Foundations.Program.MilneTensorSchur

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι m n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def m1b_matrixUnitEquiv (P : (Matrix ι ι ℂ)ˣ) : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin'OfInv P.inv_val P.val_inv

theorem m1b_matrixUnit_formTransport (M : Matrix ι ι ℂ) (P : (Matrix ι ι ℂ)ˣ) :
    m1b_formTransport M.toBilin' (m1b_matrixUnitEquiv P).symm =
      (P.val.transpose * M * P.val).toBilin' := by
  change M.toBilin'.comp P.val.toLin' P.val.toLin' = _
  rw [Matrix.toBilin'_comp]

theorem m1b_symmetric_schur_transport (A : (Matrix m m ℂ)ˣ)
    (hA : A.val.transpose = A.val) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    m1b_formTransport (Matrix.fromBlocks A.val B B.transpose D).toBilin'
      (m1b_matrixUnitEquiv (m1b_upperBlockUnit (-(A.inv * B)))).symm =
        (Matrix.fromBlocks A.val 0 0 (D - B.transpose * A.inv * B)).toBilin' := by
  rw [m1b_matrixUnit_formTransport, m1b_symmetric_schur_congruence A hA B D]

theorem m1b_alternating_schur_transport (A : (Matrix m m ℂ)ˣ)
    (hA : A.val.transpose = -A.val) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    m1b_formTransport (Matrix.fromBlocks A.val B (-B.transpose) D).toBilin'
      (m1b_matrixUnitEquiv (m1b_upperBlockUnit (-(A.inv * B)))).symm =
        (Matrix.fromBlocks A.val 0 0 (D + B.transpose * A.inv * B)).toBilin' := by
  rw [m1b_matrixUnit_formTransport, m1b_alternating_schur_congruence A hA B D]

theorem m1b_schur_nondegenerate (A : (Matrix m m ℂ)ˣ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (h : IsUnit (Matrix.fromBlocks A.val B C D)) :
    (D - C * A.inv * B).toBilin'.Nondegenerate := by
  apply (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero).mpr
  exact ((Matrix.isUnit_iff_isUnit_det _).mp ((m1b_schur_unit_iff A B C D).mp h)).ne_zero

end HodgeLean.Foundations.Program
