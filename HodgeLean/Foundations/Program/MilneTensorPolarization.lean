import HodgeLean.Foundations.Program.MilneTensorIteratedDirectional
import HodgeLean.Foundations.Program.MilneTensorLineDerivative

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_polarization (n : ℕ) (P : MvPolynomial σ ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => σ → ℂ) ℂ :=
  ((n.factorial : ℂ)⁻¹) •
    (MvPolynomial.aeval (0 : σ → ℂ)).toLinearMap.compMultilinearMap
      (m1b_iteratedDirectional n P)

theorem m1b_polarization_diagonal (n : ℕ) (P : MvPolynomial σ ℂ) (x : σ → ℂ) :
    m1b_polarization n P (fun _ => x) = (m1b_linePolynomial x P).coeff n := by
  change (n.factorial : ℂ)⁻¹ * MvPolynomial.eval (0 : σ → ℂ)
    (m1b_iteratedDirectional n P (fun _ => x)) = _
  rw [m1b_iteratedDirectional_diagonal, ← m1b_linePolynomial_zero x,
    ← m1b_linePolynomial_iterate, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul]

end HodgeLean.Foundations.Program
