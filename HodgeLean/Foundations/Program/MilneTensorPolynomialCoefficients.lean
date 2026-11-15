import Mathlib.Algebra.MvPolynomial.Funext
import HodgeLean.Foundations.Program.MilneTensorPartialPolynomial
import HodgeLean.Foundations.Program.MilneTensorPolynomialMultilinear

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def m1b_polynomialCoefficientMultilinear (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) (MvPolynomial σ ℂ) :=
  ∑ a : Fin n → ι,
    (MultilinearMap.mkPiRing ℂ (Fin n)
      (m1b_formPolynomialAt P (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2))).compLinearMap (fun t => LinearMap.proj (a t))

theorem m1b_polynomialCoefficientMultilinear_eval
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) (v : Fin n → ι → ℂ) (x : σ → ℂ) :
    MvPolynomial.eval x (m1b_polynomialCoefficientMultilinear P v) =
      MvPolynomial.eval (Sum.elim x (fun ti => v ti.1 ti.2))
        (m1b_multilinearProjectionPolynomial P) := by
  rw [m1b_polynomialMultilinear_eval]
  change MvPolynomial.aeval x (m1b_polynomialCoefficientMultilinear P v) = _
  simp only [m1b_polynomialCoefficientMultilinear, m1b_polynomialMultilinear,
    sum_apply, smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, MultilinearMap.mkPiAlgebra_apply,
    LinearMap.proj_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul]
  change (∏ t, v t (a t)) * MvPolynomial.eval x
      (m1b_formPolynomialAt P (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2)) = _
  rw [m1b_formPolynomialAt_eval]
  exact mul_comm _ _

theorem m1b_polynomialCoefficientMultilinear_partial
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) (v : Fin n → ι → ℂ) :
    m1b_polynomialCoefficientMultilinear P v =
      m1b_formPolynomialAt (m1b_multilinearProjectionPolynomial P) (fun ti => v ti.1 ti.2) := by
  apply MvPolynomial.funext
  intro x
  rw [m1b_polynomialCoefficientMultilinear_eval, m1b_formPolynomialAt_eval]

end HodgeLean.Foundations.Program
