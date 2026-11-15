import HodgeLean.Foundations.Program.MilneTensorMatrixOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r n : ℕ}

theorem m1b_totalOrbitExtension_congruence (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (M Q : Matrix ι ι ℂ) (hM : M.det ≠ 0) (v : Fin n → Fin r → ι → ℂ) :
    m1b_totalOrbitExtension B f (M.transpose * Q * M).toBilin' v =
      m1b_totalOrbitExtension B f Q.toBilin' (fun t c => M *ᵥ v t c) := by
  let e := Matrix.toLin'OfInv (M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hM))
    (M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hM))
  have he : m1b_formTransport Q.toBilin' e.symm = (M.transpose * Q * M).toBilin' := by
    change Q.toBilin'.comp M.toLin' M.toLin' = _
    rw [Matrix.toBilin'_comp]
  have h := m1b_totalOrbitExtension_equivariant B f hf Q.toBilin' e.symm
    (fun t c => e (v t c))
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [he] at h
  exact h

theorem m1b_congruence_mem_orbit (B : LinearMap.BilinForm ℂ (ι → ℂ))
    (M Q : Matrix ι ι ℂ) (hM : M.det ≠ 0)
    (hQ : Q.toBilin' ∈ Set.range (m1b_formTransport B)) :
    (M.transpose * Q * M).toBilin' ∈ Set.range (m1b_formTransport B) := by
  let e := Matrix.toLin'OfInv (M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hM))
    (M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hM))
  have he : m1b_formTransport Q.toBilin' e.symm = (M.transpose * Q * M).toBilin' := by
    change Q.toBilin'.comp M.toLin' M.toLin' = _
    rw [Matrix.toBilin'_comp]
  rw [← he]
  exact (m1b_formTransport_mem_orbit_iff B Q.toBilin' e.symm).mpr hQ

end HodgeLean.Foundations.Program
