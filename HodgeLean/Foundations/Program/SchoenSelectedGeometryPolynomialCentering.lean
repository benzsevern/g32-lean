import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Complex.Basic

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Translation of polynomial coordinates centers a prescribed complex parameter vector at the origin.
Source: inverse translations of affine space. -/
def s0_polynomial_centering_equiv {n : ℕ} (a : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (fun j ↦ MvPolynomial.X j - MvPolynomial.C (a j)))
    (MvPolynomial.aeval (fun j ↦ MvPolynomial.X j + MvPolynomial.C (a j)))
    (by apply MvPolynomial.algHom_ext; intro j; simp)
    (by apply MvPolynomial.algHom_ext; intro j; simp)

#print axioms s0_polynomial_centering_equiv
end HodgeLean.Foundations.Program
