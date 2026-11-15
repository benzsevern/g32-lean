import HodgeLean.Foundations.Program.MilneTensorPairingEquiv

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_coordinateDual (d : ℕ) : (Fin d → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin d → ℂ) :=
  m1b_formDualEquiv (1 : Matrix (Fin d) (Fin d) ℂ).toBilin'
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp))

theorem m1b_coordinateDual_apply (d : ℕ) (x y : Fin d → ℂ) :
    m1b_coordinateDual d x y = dotProduct x y := by
  change (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' x y = _
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]

theorem m1b_coordinateDual_transpose (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin d → ℂ) :
    m1b_coordinateDual d (X.transpose.mulVec x) = X.toLin'.dualMap (m1b_coordinateDual d x) := by
  apply LinearMap.ext
  intro y
  change m1b_coordinateDual d (X.transpose.mulVec x) y =
    m1b_coordinateDual d x (X.mulVec y)
  rw [m1b_coordinateDual_apply, m1b_coordinateDual_apply, dotProduct_comm]
  exact Matrix.dotProduct_transpose_mulVec X y x

end HodgeLean.Foundations.Program
