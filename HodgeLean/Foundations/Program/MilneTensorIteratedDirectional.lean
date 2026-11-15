import HodgeLean.Foundations.Program.MilneTensorDirectional
import Mathlib.LinearAlgebra.BilinearMap

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_iteratedDirectional : (n : ℕ) → MvPolynomial σ ℂ →ₗ[ℂ]
    MultilinearMap ℂ (fun _ : Fin n => σ → ℂ) (MvPolynomial σ ℂ)
  | 0 => (MultilinearMap.constLinearEquivOfIsEmpty ℂ ℂ _ _).toLinearMap
  | n + 1 => (multilinearCurryLeftEquiv ℂ (fun _ : Fin (n + 1) => σ → ℂ)
      (MvPolynomial σ ℂ)).symm.toLinearMap.comp
        (m1b_directionalDerivativeLinear.flip.compr₂ (m1b_iteratedDirectional n))

theorem m1b_iteratedDirectional_succ (n : ℕ) (P : MvPolynomial σ ℂ)
    (v : Fin (n + 1) → σ → ℂ) :
    m1b_iteratedDirectional (n + 1) P v =
      m1b_iteratedDirectional n (m1b_directionalDerivative (v 0) P) (fun i => v i.succ) := rfl

theorem m1b_iteratedDirectional_diagonal (n : ℕ) (P : MvPolynomial σ ℂ) (x : σ → ℂ) :
    m1b_iteratedDirectional n P (fun _ => x) = (m1b_directionalDerivative x)^[n] P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [m1b_iteratedDirectional_succ, ih, Function.iterate_succ_apply]

end HodgeLean.Foundations.Program
