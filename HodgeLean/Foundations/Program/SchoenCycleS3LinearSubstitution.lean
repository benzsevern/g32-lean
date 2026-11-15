import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Pi
import Mathlib.Basic.Complex.Basic

/-! # Homogeneous polynomial substitution for a change of coefficient basis -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The linear homogeneous coordinate polynomial of a linear coordinate transformation. -/
def s2e_linearCoordinatePolynomial {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (i : Fin n) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (f (Pi.single j 1) i) * X j

/-- Evaluation of the coordinate polynomial is the corresponding transformed coordinate. -/
theorem s2e_linearCoordinatePolynomial_eval {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (i : Fin n) (v : Fin n → ℂ) :
    eval v (s2e_linearCoordinatePolynomial f i) = f v i := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [s2e_linearCoordinatePolynomial, map_sum]
  simp only [map_mul, eval_C, eval_X]
  conv_rhs => rw [hv, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Linear coordinate polynomials are homogeneous of degree one. -/
theorem s2e_linearCoordinatePolynomial_homogeneous {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (i : Fin n) :
    (s2e_linearCoordinatePolynomial f i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Substitution by the actual linear coordinate polynomials. -/
def s2e_linearSubstitution {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (s2e_linearCoordinatePolynomial f)

/-- Evaluation commutes with linear coordinate substitution. -/
theorem s2e_linearSubstitution_eval {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (v : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ) :
    eval v (s2e_linearSubstitution f p) = eval (f v) p := by
  have h : (eval v).comp (s2e_linearSubstitution f).toRingHom = eval (f v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [s2e_linearSubstitution]
    · intro i
      change eval v (s2e_linearSubstitution f (X i)) = eval (f v) (X i)
      rw [s2e_linearSubstitution, aeval_X, eval_X]
      exact s2e_linearCoordinatePolynomial_eval f i v
  exact congrArg (fun h : MvPolynomial (Fin n) ℂ →+* ℂ => h p) h

/-- Invertible linear coordinate changes induce polynomial algebra automorphisms. -/
def s2e_linearSubstitutionEquiv {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ where
  __ := s2e_linearSubstitution e.toLinearMap
  invFun := s2e_linearSubstitution e.symm.toLinearMap
  left_inv p := by
    apply MvPolynomial.funext
    intro v
    change eval v (s2e_linearSubstitution e.symm.toLinearMap
      (s2e_linearSubstitution e.toLinearMap p)) = eval v p
    rw [s2e_linearSubstitution_eval, s2e_linearSubstitution_eval]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  right_inv p := by
    apply MvPolynomial.funext
    intro v
    change eval v (s2e_linearSubstitution e.toLinearMap
      (s2e_linearSubstitution e.symm.toLinearMap p)) = eval v p
    rw [s2e_linearSubstitution_eval, s2e_linearSubstitution_eval]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Linear coordinate substitution preserves each homogeneous component. -/
theorem s2e_linearSubstitution_homogeneous {n d : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (p : MvPolynomial (Fin n) ℂ) (hp : p.IsHomogeneous d) :
    (s2e_linearSubstitution f p).IsHomogeneous d := by
  simpa only [one_mul, s2e_linearSubstitution] using hp.aeval _ (s2e_linearCoordinatePolynomial_homogeneous f)

end HodgeLean.Foundations.Program
