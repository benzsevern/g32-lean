import HodgeLean.Foundations.Program.MilneTensorMultilinearProjection

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def m1b_polynomialMultilinear (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (x : σ → ℂ) : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ :=
  ∑ a : Fin n → ι,
    (MvPolynomial.eval (Sum.elim x
      (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2)) P) •
        (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
          (fun t => LinearMap.proj (a t))

theorem m1b_polynomialMultilinear_basis (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (x : σ → ℂ) (a : Fin n → ι) :
    m1b_polynomialMultilinear P x (fun t => Pi.single (a t) 1) =
      MvPolynomial.eval (Sum.elim x
        (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2)) P := by
  classical
  simp only [m1b_polynomialMultilinear, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hba
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [Pi.single_apply, ht]), mul_zero]
  · simp

theorem m1b_polynomialMultilinear_eval (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (x : σ → ℂ) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (Sum.elim x (fun ti => v ti.1 ti.2))
      (m1b_multilinearProjectionPolynomial P) = m1b_polynomialMultilinear P x v := by
  apply m1b_multilinearProjectionPolynomial_eval
  intro a
  exact (m1b_polynomialMultilinear_basis P x a).symm

end HodgeLean.Foundations.Program
