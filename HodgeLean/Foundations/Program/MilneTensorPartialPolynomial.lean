import HodgeLean.Foundations.Program.MilneTensorLinearSubstitution

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ ζ : Type*}

def m1b_formPolynomialAt (P : MvPolynomial (σ ⊕ ζ) ℂ) (v : ζ → ℂ) :
    MvPolynomial σ ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun z => MvPolynomial.C (v z))) P

theorem m1b_formPolynomialAt_eval (P : MvPolynomial (σ ⊕ ζ) ℂ)
    (v : ζ → ℂ) (x : σ → ℂ) :
    MvPolynomial.eval x (m1b_formPolynomialAt P v) =
      MvPolynomial.eval (Sum.elim x v) P := by
  rw [m1b_formPolynomialAt, MvPolynomial.map_eval₂Hom]
  congr 2
  · ext c
    simp
  · funext z
    cases z <;> simp

end HodgeLean.Foundations.Program
