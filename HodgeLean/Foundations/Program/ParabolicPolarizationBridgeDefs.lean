import HodgeLean.Foundations.Program.UniversalFamilyCover
import HodgeLean.Foundations.HermitianClassC8
import HodgeLean.Papers.G32Disc
import HodgeLean.Papers.G32Family

/-! # H1: the printed parabolic form as a Hermitian form, definitions

The printed matrix `g32H0` of G32 Proposition 6.3, read as the Gram matrix of a Hermitian form
on `K⁶` for `K = ℚ(√-3)`, and the complex embedding of `K` used to compare `hermSignature` with
an eigenvalue count. No geometric comparison is defined here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Matrix
open HodgeLean.Papers HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The primitive cube root of unity `ζ = (-1 + √-3) / 2` of `K = ℚ(√-3)`, the element at which
`g32d_ParabolicPolarization` evaluates the printed matrix.
Source: G32 v0.16, Section 2 and Proposition 6.3; `g32d_ParabolicPolarization`. -/
def hp_zeta : QuadraticAlgebra ℚ (-3) 0 := (-1 + QuadraticAlgebra.omega) / 2

example : hp_zeta = (-1 + QuadraticAlgebra.omega) / 2 := rfl

/-- The sesquilinear form on `Kⁿ` with Gram matrix `M` in the standard basis,
`(x, y) ↦ ∑ i j, star (x i) * M i j * y j`, conjugate-linear in the first variable as
`diagForm` and `weilHermitian` are.
Source: Mathlib `Matrix.toLinearMapₛₗ₂`; the convention of `HermitianForm.diagForm`. -/
def hp_matrixForm {n : ℕ} (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0)) :
    (Fin n → QuadraticAlgebra ℚ (-3) 0) →ₗ⋆[QuadraticAlgebra ℚ (-3) 0]
      (Fin n → QuadraticAlgebra ℚ (-3) 0) →ₗ[QuadraticAlgebra ℚ (-3) 0]
        QuadraticAlgebra ℚ (-3) 0 :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd _) (Pi.basisFun _ (Fin n)) (Pi.basisFun _ (Fin n)) M

/-- The Gram matrix of `hp_matrixForm M` in the standard basis is `M`. -/
example {n : ℕ} (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0)) :
    LinearMap.toMatrix₂ (Pi.basisFun _ (Fin n)) (Pi.basisFun _ (Fin n)) (hp_matrixForm M) = M :=
  LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _

/-- The diagonal model `b60_H` is the matrix form of its diagonal. -/
example : hp_matrixForm (diagonal fun i ↦
    algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0) (![1, 1, 1, -1, -1, -2] i)) = b60_H := rfl

/-- The printed parabolic form on `K⁶`: Gram matrix `g32H0 ζ` in the standard basis.
Source: G32 v0.16, proof of Proposition 6.3 (the matrix `h_0`); `g32H0`. -/
def hp_h0Form :
    (Fin 6 → QuadraticAlgebra ℚ (-3) 0) →ₗ⋆[QuadraticAlgebra ℚ (-3) 0]
      (Fin 6 → QuadraticAlgebra ℚ (-3) 0) →ₗ[QuadraticAlgebra ℚ (-3) 0]
        QuadraticAlgebra ℚ (-3) 0 :=
  hp_matrixForm (g32H0 hp_zeta)

/-- Convention check: `hp_h0Form (eᵢ, eⱼ)` is the `(i, j)` entry of `g32H0 ζ`, not of its
transpose. -/
example :
    LinearMap.toMatrix₂ (Pi.basisFun _ (Fin 6)) (Pi.basisFun _ (Fin 6)) hp_h0Form =
      g32H0 hp_zeta :=
  LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _

/-- The form is not zero: its value at `(e₀, e₀)` is the printed entry `2/3`. -/
example : hp_h0Form (Pi.single 0 1) (Pi.single 0 1) = 2 / 3 := by
  have h := congrFun (congrFun (show LinearMap.toMatrix₂ (Pi.basisFun _ (Fin 6))
    (Pi.basisFun _ (Fin 6)) hp_h0Form = g32H0 hp_zeta from
      LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _) 0) 0
  rw [LinearMap.toMatrix₂_apply, Pi.basisFun_apply] at h
  rw [h]
  simp [g32H0]

/-- The complex embedding of `K = ℚ(√-3)` sending `√-3` to `i√3`.
Source: the standard embedding of an imaginary quadratic field; Mathlib
`QuadraticAlgebra.lift`. -/
def hp_toComplex : QuadraticAlgebra ℚ (-3) 0 →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨(Real.sqrt 3 : ℂ) * Complex.I, by
    have h3 : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    simp only [zero_smul, add_zero, Rat.smul_one_eq_cast]
    push_cast
    linear_combination (Complex.I ^ 2) * h3 + 3 * Complex.I_sq⟩

example : hp_toComplex QuadraticAlgebra.omega = (Real.sqrt 3 : ℂ) * Complex.I := by
  simp [hp_toComplex]

end HodgeLean.Foundations.Program
