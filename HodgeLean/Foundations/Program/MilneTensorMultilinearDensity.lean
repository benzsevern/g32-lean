import HodgeLean.Foundations.Program.MilneTensorGLDensity
import HodgeLean.Foundations.Program.MilneTensorDiagonal

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_multilinear_orbit_extension_of_local {r n : ℕ}
    (B : Matrix ι ι ℂ)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ)
    (i₀ j₀ : ι) (hB : B i₀ j₀ ≠ 0)
    (hlocal : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → (M⁻¹.transpose * B * M⁻¹) i₀ j₀ ≠ 0 →
      ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
          (fun jc => v jc.1 jc.2.1 jc.2.2)) p = f (fun j c => M⁻¹ *ᵥ v j c)) :
    ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
      MvPolynomial.eval (Sum.elim (fun ij => (M⁻¹.transpose * B * M⁻¹) ij.1 ij.2)
        (fun jc => v jc.1 jc.2.1 jc.2.2)) p = f (fun j c => M⁻¹ *ᵥ v j c) := by
  let g := f.compLinearMap (fun _ => m1b_copyCoordinates (ι := ι) r)
  let q := m1b_multilinearPolynomial g
  have hq (w : Fin n → Fin r → ι → ℂ) :
      MvPolynomial.eval (fun jc : Fin n × (Fin r × ι) => w jc.1 jc.2.1 jc.2.2) q = f w :=
    m1b_multilinearPolynomial_eval g (fun j ci => w j ci.1 ci.2)
  have h := m1b_polynomial_orbit_extension_of_local B p q i₀ j₀ hB (by
    intro M hM hp v
    exact (hlocal M hM hp v).trans (hq (fun j c => M⁻¹ *ᵥ v j c)).symm)
  intro M hM v
  have he := h M hM v
  exact he.trans (hq (fun j c => M⁻¹ *ᵥ v j c))

end HodgeLean.Foundations.Program
