import HodgeLean.Foundations.Program.MilneTensorEquivMatrix

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem m1b_coordinateReindex_standard (e : ι ≃ κ) :
    (1 : Matrix κ κ ℂ).toBilin'.compl₁₂
      (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap
      (LinearEquiv.funCongrLeft ℂ ℂ e).symm.toLinearMap =
        (1 : Matrix ι ι ℂ).toBilin' := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (1 : Matrix κ κ ℂ).toBilin' (fun i => x (e.symm i)) (fun i => y (e.symm i)) =
    (1 : Matrix ι ι ℂ).toBilin' x y
  simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct]
  exact e.symm.sum_comp (fun i => x i * y i)

theorem m1b_coordinateReindex_basis (e : ι ≃ κ) (i : κ) :
    LinearEquiv.funCongrLeft ℂ ℂ e (Pi.single i 1) = Pi.single (e.symm i) (1 : ℂ) := by
  funext j
  change (Pi.single i (1 : ℂ) : κ → ℂ) (e j) =
    (Pi.single (e.symm i) (1 : ℂ) : ι → ℂ) j
  simp only [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

end HodgeLean.Foundations.Program
