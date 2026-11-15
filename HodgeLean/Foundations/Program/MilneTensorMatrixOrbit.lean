import HodgeLean.Foundations.Program.MilneTensorTotalOrbit
import HodgeLean.Foundations.Program.MilneTensorSchurOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_totalOrbitExtension_matrix_eval (B : Matrix ι ι ℂ) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B.toBilin', ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v)
    (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) (v : Fin n → Fin r → ι → ℂ) :
    m1b_totalOrbitExtension B.toBilin' f (M⁻¹.transpose * B * M⁻¹).toBilin' v =
      f (fun j c => M⁻¹ *ᵥ v j c) := by
  let e := Matrix.toLin'OfInv (M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hM))
    (M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hM))
  have he : m1b_formTransport B.toBilin' e = (M⁻¹.transpose * B * M⁻¹).toBilin' := by
    change B.toBilin'.comp M⁻¹.toLin' M⁻¹.toLin' = _
    rw [Matrix.toBilin'_comp]
  rw [← he, m1b_totalOrbitExtension_eval B.toBilin' f hf e]
  rfl

theorem m1b_formTransport_reindex (Q : Matrix ι ι ℂ) (e : ι ≃ ι) :
    m1b_formTransport Q.toBilin' (LinearEquiv.funCongrLeft ℂ ℂ e) =
      Matrix.toBilin' (fun i j => Q (e i) (e j)) := by
  let d := LinearEquiv.funCongrLeft ℂ ℂ e
  have hd (i : ι) : d.symm (Pi.single i 1) = Pi.single (e i) (1 : ℂ) := by
    funext j
    change (Pi.single i (1 : ℂ) : ι → ℂ) (e.symm j) =
      (Pi.single (e i) (1 : ℂ) : ι → ℂ) j
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  apply (Pi.basisFun ℂ ι).ext
  intro i
  apply (Pi.basisFun ℂ ι).ext
  intro j
  simp only [Pi.basisFun_apply]
  change Q.toBilin' (d.symm (Pi.single i 1)) (d.symm (Pi.single j 1)) =
    Matrix.toBilin' (fun s t => Q (e s) (e t)) (Pi.single i 1) (Pi.single j 1)
  rw [hd, hd, Matrix.toBilin'_single Q (e i) (e j)]
  exact (Matrix.toBilin'_single (fun s t => Q (e s) (e t)) i j).symm

theorem m1b_totalOrbitExtension_reindex (B Q : Matrix ι ι ℂ) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B.toBilin', ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v)
    (e : ι ≃ ι) (v : Fin n → Fin r → ι → ℂ) :
    m1b_totalOrbitExtension B.toBilin' f (Matrix.toBilin' (fun i j => Q (e i) (e j)))
      (fun j c i => v j c (e i)) = m1b_totalOrbitExtension B.toBilin' f Q.toBilin' v := by
  rw [← m1b_formTransport_reindex Q e]
  exact m1b_totalOrbitExtension_equivariant B.toBilin' f hf Q.toBilin'
    (LinearEquiv.funCongrLeft ℂ ℂ e) v

end HodgeLean.Foundations.Program
