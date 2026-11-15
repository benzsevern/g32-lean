import HodgeLean.Foundations.Program.MilneTensorPolarizedCommutation

noncomputable section
open Matrix
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_polarizedTensorMap_unit_commutes
    (hC : (1 : Matrix ι ι ℂ).toBilin'.Nondegenerate) (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (hJ : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v q,
      J v (fun a => m1b_congruenceCoordinates M (q a)) =
        J (fun s => M *ᵥ v s) q)
    (g : LinearMap.GeneralLinearGroup ℂ (ι → ℂ)) :
    SchurWeyl.tensorPow (Fin (k * 2)) (g : Module.End ℂ (ι → ℂ)) *
        m1b_polarizedTensorMap (1 : Matrix ι ι ℂ).toBilin' hC k J =
      m1b_polarizedTensorMap (1 : Matrix ι ι ℂ).toBilin' hC k J *
        SchurWeyl.tensorPow (Fin (k * 2)) (g : Module.End ℂ (ι → ℂ)) := by
  let u : Module.End ℂ (ι → ℂ) := g
  have hM : u.toMatrix'.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (LinearMap.isUnit_toMatrix'_iff.mpr g.isUnit)).ne_zero
  have h := m1b_polarizedTensorMap_commutes hC k J hJ u.toMatrix' hM
  rw [Matrix.toLin'_toMatrix'] at h
  exact h.symm

end HodgeLean.Foundations.Program
