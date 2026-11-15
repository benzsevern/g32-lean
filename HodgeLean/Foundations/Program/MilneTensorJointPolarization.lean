import HodgeLean.Foundations.Program.MilneTensorPolynomialCoefficients
import HodgeLean.Foundations.Program.MilneTensorPolarizationLinear

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def m1b_jointPolarization (k : ℕ) (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => σ → ℂ) ℂ) :=
  (m1b_polarizationLinear k).compMultilinearMap (m1b_polynomialCoefficientMultilinear P)

theorem m1b_jointPolarization_apply (k : ℕ) (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (v : Fin n → ι → ℂ) (q : Fin k → σ → ℂ) :
    m1b_jointPolarization k P v q =
      m1b_polarization k (m1b_formPolynomialAt (m1b_multilinearProjectionPolynomial P)
        (fun ti => v ti.1 ti.2)) q := by
  change m1b_polarization k (m1b_polynomialCoefficientMultilinear P v) q = _
  rw [m1b_polynomialCoefficientMultilinear_partial]

end HodgeLean.Foundations.Program
