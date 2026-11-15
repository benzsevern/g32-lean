import HodgeLean.Foundations.Program.MilneTensorPolynomialMultilinear
import HodgeLean.Foundations.Program.MilneTensorPartialCovariance

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem m1b_multilinearProjection_of_eval
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ)
    (F : (σ → ℂ) → MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (hP : ∀ x v, MvPolynomial.eval (Sum.elim x (fun ti => v ti.1 ti.2)) P = F x v) :
    m1b_multilinearProjectionPolynomial P = P := by
  apply MvPolynomial.funext
  intro z
  let x : σ → ℂ := fun s => z (Sum.inl s)
  let v : Fin n → ι → ℂ := fun t i => z (Sum.inr (t, i))
  have he : Sum.elim x (fun ti : Fin n × ι => v ti.1 ti.2) = z := by
    funext s
    cases s <;> rfl
  rw [← he]
  exact (m1b_multilinearProjectionPolynomial_eval P x (F x)
    (fun a => hP x (fun t => Pi.single (a t) 1)) v).trans (hP x v).symm

theorem m1b_reconstruction_linearSubstitution_form [Fintype σ] [DecidableEq σ]
    (L : (σ → ℂ) →ₗ[ℂ] (σ → ℂ)) (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) :
    m1b_multilinearProjectionPolynomial
      (m1b_linearSubstitution (m1b_sumCoordinateMap L LinearMap.id)
        (m1b_multilinearProjectionPolynomial P)) =
      m1b_linearSubstitution (m1b_sumCoordinateMap L LinearMap.id)
        (m1b_multilinearProjectionPolynomial P) := by
  apply m1b_multilinearProjection_of_eval _ (fun x => m1b_polynomialMultilinear P (L x))
  intro x v
  rw [m1b_linearSubstitution_eval]
  exact m1b_polynomialMultilinear_eval P (L x) v

end HodgeLean.Foundations.Program
