import HodgeLean.Foundations.Program.MilneTensorFormPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*}

def m1b_symmetricRawPolynomial (p : MvPolynomial (Sym2 ι ⊕ ζ) ℂ) :
    MvPolynomial ((ι × ι) ⊕ ζ) ℂ :=
  MvPolynomial.rename (Sum.map (fun s => s.out) id) p

theorem m1b_symmetricRawPolynomial_eval
    (p : MvPolynomial (Sym2 ι ⊕ ζ) ℂ) (B : ι → ι → ℂ)
    (hs : ∀ i j, B i j = B j i) (v : ζ → ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => B ij.1 ij.2) v)
      (m1b_symmetricRawPolynomial p) =
        MvPolynomial.eval (Sum.elim (Sym2.lift ⟨B, hs⟩) v) p := by
  rw [m1b_symmetricRawPolynomial, MvPolynomial.eval_rename]
  congr 2
  funext s
  cases s with
  | inl s =>
    change B s.out.1 s.out.2 = Sym2.lift ⟨B, hs⟩ s
    exact congrArg (Sym2.lift ⟨B, hs⟩) (Sym2.mk_fst_out_snd_out s)
  | inr s => rfl

theorem m1b_rawSymmetricPolynomial_eval
    (p : MvPolynomial ((ι × ι) ⊕ ζ) ℂ) (x : Sym2 ι ⊕ ζ → ℂ) :
    MvPolynomial.eval x
      (MvPolynomial.rename (Sum.map (fun ij => Sym2.mk ij.1 ij.2) id) p) =
        MvPolynomial.eval (Sum.elim (fun ij => x (Sum.inl (Sym2.mk ij.1 ij.2)))
          (fun z => x (Sum.inr z))) p := by
  rw [MvPolynomial.eval_rename]
  congr 2
  funext s
  cases s <;> rfl

end HodgeLean.Foundations.Program
