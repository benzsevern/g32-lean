import HodgeLean.Foundations.Program.MilneTensorSymmetricAssembly
import HodgeLean.Foundations.Program.MilneTensorMatrixOrbit

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem m1b_symmetric_orbit_polynomial_from_numerator {r n : ℕ}
    (B : Matrix ι ι ℂ) (hsB : ∀ s t, B s t = B t s) (hdB : B.det ≠ 0)
    (i j : ι) (hij : i ≠ j) (hiB : B i i ≠ 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries B.toBilin', ∀ v,
      f (fun t => m1b_copies r u (v t)) = f v)
    (a : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ) (k : ℕ)
    (ha : ∀ (Q : Matrix ι ι ℂ), (∀ s t, Q s t = Q t s) → Q.det ≠ 0 → Q i i ≠ 0 →
      ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun st => Q st.1 st.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) a =
            Q i i ^ k * m1b_totalOrbitExtension B.toBilin' f Q.toBilin' v) :
    ∃ p : MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ M : Matrix ι ι ℂ, M.det ≠ 0 → ∀ v : Fin n → Fin r → ι → ℂ,
        MvPolynomial.eval (Sum.elim (fun st => (M⁻¹.transpose * B * M⁻¹) st.1 st.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) p = f (fun t c => M⁻¹ *ᵥ v t c) := by
  apply m1b_symmetric_polynomial_from_numerator B hsB hdB i j hij hiB f
    (fun Q v => m1b_totalOrbitExtension B.toBilin' f Q.toBilin' v)
    (fun e Q _ _ v => m1b_totalOrbitExtension_reindex B Q f hf e v)
    (fun M hM v => m1b_totalOrbitExtension_matrix_eval B f hf M hM v) a k ha

end HodgeLean.Foundations.Program
