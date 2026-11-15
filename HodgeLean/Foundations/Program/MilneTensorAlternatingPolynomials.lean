import HodgeLean.Foundations.Program.MilneTensorAlternatingCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*} [LinearOrder ι]

def m1b_rawAlternatingPolynomial (p : MvPolynomial ((ι × ι) ⊕ ζ) ℂ) :
    MvPolynomial ({q : ι × ι // q.1 < q.2} ⊕ ζ) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun ij => m1b_alternatingCoordinateMatrix ζ ij.1 ij.2)
      (fun z => MvPolynomial.X (Sum.inr z))) p

def m1b_alternatingRawPolynomial
    (p : MvPolynomial ({q : ι × ι // q.1 < q.2} ⊕ ζ) ℂ) :
    MvPolynomial ((ι × ι) ⊕ ζ) ℂ :=
  MvPolynomial.rename (Sum.map Subtype.val id) p

theorem m1b_rawAlternatingPolynomial_eval
    (p : MvPolynomial ((ι × ι) ⊕ ζ) ℂ)
    (x : {q : ι × ι // q.1 < q.2} ⊕ ζ → ℂ) :
    MvPolynomial.eval x (m1b_rawAlternatingPolynomial p) =
      MvPolynomial.eval (Sum.elim
        (fun ij => MvPolynomial.eval x (m1b_alternatingCoordinateMatrix ζ ij.1 ij.2))
        (fun z => x (Sum.inr z))) p := by
  let ev := MvPolynomial.eval x
  have hc : ev.comp MvPolynomial.C = RingHom.id ℂ := by
    ext a
    exact MvPolynomial.eval_C a
  change ev (MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun ij => m1b_alternatingCoordinateMatrix ζ ij.1 ij.2)
      (fun z => MvPolynomial.X (Sum.inr z))) p) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  congr 2
  funext z
  cases z with
  | inl ij => rfl
  | inr z => exact MvPolynomial.eval_X _

theorem m1b_alternatingRawPolynomial_eval
    (p : MvPolynomial ({q : ι × ι // q.1 < q.2} ⊕ ζ) ℂ)
    (Q : Matrix ι ι ℂ) (v : ζ → ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v)
      (m1b_alternatingRawPolynomial p) =
        MvPolynomial.eval (Sum.elim
          (fun q : {q : ι × ι // q.1 < q.2} => Q q.val.1 q.val.2) v) p := by
  rw [m1b_alternatingRawPolynomial, MvPolynomial.eval_rename]
  congr 2
  funext z
  cases z <;> rfl

end HodgeLean.Foundations.Program
