import HodgeLean.Foundations.Program.MilneTensorPolarizedTensorMap
import HodgeLean.Foundations.Program.MilneTensorRankOneCongruence
import HodgeLean.Foundations.Program.MilneTensorPairingAdjoint

noncomputable section
open Matrix
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_polarizedTensorMap_commutes
    (hC : (1 : Matrix ι ι ℂ).toBilin'.Nondegenerate) (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (hJ : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v q,
      J v (fun a => m1b_congruenceCoordinates M (q a)) =
        J (fun s => M *ᵥ v s) q)
    (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    (m1b_polarizedTensorMap (1 : Matrix ι ι ℂ).toBilin' hC k J).comp
      (SchurWeyl.tensorPow (Fin (k * 2)) M.toLin') =
    (SchurWeyl.tensorPow (Fin (k * 2)) M.toLin').comp
      (m1b_polarizedTensorMap (1 : Matrix ι ι ℂ).toBilin' hC k J) := by
  have hadj : ∀ x y, (1 : Matrix ι ι ℂ).toBilin' (M.toLin' x) y =
      (1 : Matrix ι ι ℂ).toBilin' x (M.transpose.toLin' y) := by
    intro x y
    simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, Matrix.toLin'_apply]
    exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec M x y).symm
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change m1b_polarizedTensorMap _ hC k J
    (SchurWeyl.tensorPow (Fin (k * 2)) M.toLin' (⨂ₜ[ℂ] s, x s)) =
    SchurWeyl.tensorPow (Fin (k * 2)) M.toLin'
      (m1b_polarizedTensorMap _ hC k J (⨂ₜ[ℂ] s, x s))
  apply m1b_tensorFunction_injective _ hC (k * 2)
  apply MultilinearMap.ext
  intro v
  rw [m1b_tensorFunction_adjoint _ _ _ _ hadj, SchurWeyl.tensorPow_tprod,
    m1b_polarizedTensorMap_tprod, m1b_polarizedTensorMap_tprod]
  have h := hJ M.transpose (by simpa using hM) v
    (fun a => m1b_rankOneForm (fun s => x (finProdFinEquiv (a, s))))
  simp only [m1b_rankOneForm_congruence, Matrix.transpose_transpose] at h
  exact h

end HodgeLean.Foundations.Program
