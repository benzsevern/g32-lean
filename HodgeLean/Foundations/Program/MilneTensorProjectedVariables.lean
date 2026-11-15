import HodgeLean.Foundations.Program.MilneTensorFormProjection
import HodgeLean.Foundations.Program.MilneTensorDescent

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*}

def m1b_projectedMatrixVariables (ε : ℂ) :
    Matrix ι ι (MvPolynomial ((ι × ι) ⊕ ζ) ℂ) :=
  fun i j => MvPolynomial.C ((2 : ℂ)⁻¹) *
    (MvPolynomial.X (Sum.inl (i, j)) + MvPolynomial.C ε * MvPolynomial.X (Sum.inl (j, i)))

theorem m1b_projectedMatrixVariables_eval [Fintype ι] [DecidableEq ι] (ε : ℂ) (Q : Matrix ι ι ℂ) (v : ζ → ℂ) :
    (MvPolynomial.eval (Sum.elim (fun ij : ι × ι => Q ij.1 ij.2) v)).mapMatrix
      (m1b_projectedMatrixVariables ε) = m1b_matrixFormProjection ε Q := by
  ext i j
  simp [m1b_projectedMatrixVariables, m1b_matrixFormProjection,
    RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, mul_add]

theorem m1b_projectedMatrixVariables_det_ne_zero [Fintype ι] [DecidableEq ι]
    (ε : ℂ) (B : Matrix ι ι ℂ) (hB : (m1b_matrixFormProjection ε B).det ≠ 0) :
    (m1b_projectedMatrixVariables (ι := ι) (ζ := ζ) ε).det ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval
    (Sum.elim (fun ij : ι × ι => B ij.1 ij.2) (0 : ζ → ℂ))) h
  rw [map_zero, RingHom.map_det, m1b_projectedMatrixVariables_eval] at he
  exact hB he

end HodgeLean.Foundations.Program
