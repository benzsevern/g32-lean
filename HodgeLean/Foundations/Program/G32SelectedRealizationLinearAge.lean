import HodgeLean.Foundations.Program.G32SelectedRealizationLinearMultiplicity
import HodgeLean.Foundations.Program.G32SelectedRealizationLinearInvariants

noncomputable section
open HodgeLean.Papers HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_scalar_age (c : ℂ) : b4_age (Algebra.lmul ℂ ℂ c) = g32h_angle c := by
  classical
  let b := Module.Basis.singleton Unit ℂ
  have hm : LinearMap.toMatrix b b (Algebra.lmul ℂ ℂ c) =
      Matrix.diagonal (fun _ : Unit ↦ c) := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [LinearMap.toMatrix_apply, b]
  unfold b4_age
  rw [← LinearMap.charpoly_toMatrix (f := Algebra.lmul ℂ ℂ c) b, hm, Matrix.charpoly_diagonal]
  simp

end HodgeLean.Foundations.Program
