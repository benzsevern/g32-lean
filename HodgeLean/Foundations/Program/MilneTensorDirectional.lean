import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
namespace HodgeLean.Foundations.Program
variable {σ : Type*}

def m1b_directionalDerivative (x : σ → ℂ) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  MvPolynomial.mkDerivation ℂ (fun i => MvPolynomial.C (x i))

theorem m1b_directionalDerivative_X (x : σ → ℂ) (i : σ) :
    m1b_directionalDerivative x (MvPolynomial.X i) = MvPolynomial.C (x i) :=
  MvPolynomial.mkDerivation_X ℂ _ _

theorem m1b_directionalDerivative_add (x y : σ → ℂ) :
    m1b_directionalDerivative (x + y) =
      m1b_directionalDerivative x + m1b_directionalDerivative y := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [m1b_directionalDerivative, MvPolynomial.mkDerivation_X]

theorem m1b_directionalDerivative_smul (c : ℂ) (x : σ → ℂ) :
    m1b_directionalDerivative (c • x) = c • m1b_directionalDerivative x := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [m1b_directionalDerivative, MvPolynomial.mkDerivation_X,
    MvPolynomial.smul_eq_C_mul, smul_eq_mul]

def m1b_directionalDerivativeLinear :
    (σ → ℂ) →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ) where
  toFun x := (m1b_directionalDerivative x).toLinearMap
  map_add' x y := congrArg Derivation.toLinearMap (m1b_directionalDerivative_add x y)
  map_smul' c x := congrArg Derivation.toLinearMap (m1b_directionalDerivative_smul c x)

end HodgeLean.Foundations.Program
