import HodgeLean.Foundations.Program.MilneTensorPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def m1b_multilinearProjectionPolynomial
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) :
    MvPolynomial (σ ⊕ (Fin n × ι)) ℂ :=
  ∑ a : Fin n → ι,
    MvPolynomial.eval₂Hom MvPolynomial.C
      (Sum.elim (fun s => MvPolynomial.X (Sum.inl s))
        (fun ti : Fin n × ι => MvPolynomial.C ((Pi.single (a ti.1) 1 : ι → ℂ) ti.2))) P *
      ∏ t, MvPolynomial.X (Sum.inr (t, a t))

theorem m1b_multilinearProjectionPolynomial_eval
    (P : MvPolynomial (σ ⊕ (Fin n × ι)) ℂ) (x : σ → ℂ)
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ)
    (hf : ∀ a : Fin n → ι,
      MvPolynomial.eval (Sum.elim x (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2)) P =
        f (fun t => Pi.single (a t) 1)) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (Sum.elim x (fun ti : Fin n × ι => v ti.1 ti.2))
      (m1b_multilinearProjectionPolynomial P) = f v := by
  rw [m1b_multilinearProjectionPolynomial, map_sum,
    m1b_multilinear_coordinate_expansion f v]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, map_prod]
  simp only [MvPolynomial.eval_X, Sum.elim_inr]
  have he : MvPolynomial.eval (Sum.elim x (fun ti : Fin n × ι => v ti.1 ti.2))
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (Sum.elim (fun s => MvPolynomial.X (Sum.inl s))
          (fun ti : Fin n × ι => MvPolynomial.C ((Pi.single (a ti.1) 1 : ι → ℂ) ti.2))) P) =
        MvPolynomial.eval (Sum.elim x (fun ti : Fin n × ι => (Pi.single (a ti.1) 1 : ι → ℂ) ti.2)) P := by
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    · ext c
      simp
    · funext z
      cases z <;> simp
  rw [he, hf]
  exact mul_comm _ _

end HodgeLean.Foundations.Program
