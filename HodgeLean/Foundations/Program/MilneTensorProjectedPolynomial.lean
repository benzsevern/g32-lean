import HodgeLean.Foundations.Program.MilneTensorCovarianceCoordinates
import HodgeLean.Foundations.Program.MilneTensorLinearSubstitution

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ζ] [DecidableEq ζ]

def m1b_formProjectedPolynomial (ε : ℂ) (P : MvPolynomial ((ι × ι) ⊕ ζ) ℂ) :
    MvPolynomial ((ι × ι) ⊕ ζ) ℂ :=
  m1b_linearSubstitution
    (m1b_sumCoordinateMap (m1b_formProjectionCoordinates ε) LinearMap.id) P

theorem m1b_formProjectedPolynomial_eval (ε : ℂ) (P : MvPolynomial ((ι × ι) ⊕ ζ) ℂ)
    (Q : Matrix ι ι ℂ) (v : ζ → ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) (m1b_formProjectedPolynomial ε P) =
      MvPolynomial.eval (Sum.elim (fun ij => m1b_matrixFormProjection ε Q ij.1 ij.2) v) P := by
  rw [m1b_formProjectedPolynomial, m1b_linearSubstitution_eval]
  rfl

end HodgeLean.Foundations.Program
