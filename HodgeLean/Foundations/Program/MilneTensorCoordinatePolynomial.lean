import HodgeLean.Foundations.Program.MilneTensorSchurPolynomial

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι]

def m1b_formVectorSubstitution (A : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) (r n : ℕ) :
    ((κ × κ) ⊕ (Fin n × (Fin r × κ))) →
      MvPolynomial ((ι × ι) ⊕ (Fin n × (Fin r × ι))) ℂ :=
  Sum.elim
    (fun ab => ∑ i, ∑ j, MvPolynomial.C (A i ab.1) *
      MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.C (A j ab.2))
    (fun jc => ∑ i, MvPolynomial.C (C jc.2.2 i) *
      MvPolynomial.X (Sum.inr (jc.1, jc.2.1, i)))

theorem m1b_formVectorSubstitution_variable_eval
    (A : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) {r n : ℕ}
    (M : Matrix ι ι ℂ) (v : Fin n → Fin r → ι → ℂ)
    (q : (κ × κ) ⊕ (Fin n × (Fin r × κ))) :
    MvPolynomial.eval (Sum.elim (fun ij => M ij.1 ij.2)
      (fun jc => v jc.1 jc.2.1 jc.2.2)) (m1b_formVectorSubstitution A C r n q) =
      Sum.elim (fun ab => (A.transpose * M * A) ab.1 ab.2)
        (fun jc => (C *ᵥ v jc.1 jc.2.1) jc.2.2) q := by
  cases q with
  | inl ab =>
    simp only [m1b_formVectorSubstitution, Sum.elim_inl, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.mul_apply,
      Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  | inr jc =>
    simp only [m1b_formVectorSubstitution, Sum.elim_inr, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rfl

theorem m1b_formVectorSubstitution_eval
    (A : Matrix ι κ ℂ) (C : Matrix κ ι ℂ) {r n : ℕ}
    (M : Matrix ι ι ℂ) (v : Fin n → Fin r → ι → ℂ)
    (p : MvPolynomial ((κ × κ) ⊕ (Fin n × (Fin r × κ))) ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => M ij.1 ij.2)
      (fun jc => v jc.1 jc.2.1 jc.2.2))
      (MvPolynomial.eval₂Hom MvPolynomial.C (m1b_formVectorSubstitution A C r n) p) =
        MvPolynomial.eval (Sum.elim (fun ab => (A.transpose * M * A) ab.1 ab.2)
          (fun jc => (C *ᵥ v jc.1 jc.2.1) jc.2.2)) p := by
  let ev := MvPolynomial.eval (Sum.elim (fun ij : ι × ι => M ij.1 ij.2)
    (fun jc : Fin n × (Fin r × ι) => v jc.1 jc.2.1 jc.2.2))
  have hc : ev.comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    exact MvPolynomial.eval_C c
  change ev (MvPolynomial.eval₂Hom MvPolynomial.C (m1b_formVectorSubstitution A C r n) p) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  change MvPolynomial.eval (fun q => ev (m1b_formVectorSubstitution A C r n q)) p = _
  congr 1
  congr 1
  funext q
  exact m1b_formVectorSubstitution_variable_eval A C M v q

end HodgeLean.Foundations.Program
