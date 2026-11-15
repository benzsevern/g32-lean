import HodgeLean.Foundations.Program.MilneTensorDescent
import Mathlib.Algebra.MvPolynomial.Polynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_weightedCoefficient (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ :=
  ((MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)) P).coeff n

theorem m1b_weightedCoefficient_eval (w : σ → ℕ) (n : ℕ)
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) :
    MvPolynomial.eval x (m1b_weightedCoefficient w n P) =
      ((MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) * Polynomial.X ^ w i)) P).coeff n := by
  rw [m1b_weightedCoefficient, ← Polynomial.coeff_map]
  apply congrArg (fun q : Polynomial ℂ => q.coeff n)
  rw [show Polynomial.map (MvPolynomial.eval x) =
    Polynomial.mapRingHom (MvPolynomial.eval x) from rfl, MvPolynomial.map_eval₂Hom]
  congr 2
  · ext c
    simp
  · funext i
    simp

end HodgeLean.Foundations.Program
