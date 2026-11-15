import HodgeLean.Foundations.Program.SchoenCycleStep1
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Descent of polynomial coefficients on quotient affine opens -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Coefficientwise invariant polynomial equations descend on an affine quotient open.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_invariant_polynomial_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (F : Polynomial Γ(X.left, q.left ⁻¹ᵁ U))
    (hF : ∀ n u, ((a u).left.appLE (q.left ⁻¹ᵁ U) (q.left ⁻¹ᵁ U)
      (by change q.left ⁻¹ᵁ U ≤ ((a u).left ≫ q.left) ⁻¹ᵁ U
          have he : (a u).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv u)
          rw [he])).hom (F.coeff n) = F.coeff n) :
    ∃! P : Polynomial Γ(Y.left, U), P.map (q.left.app U).hom = F := by
  classical
  have hc (n : ℕ) := s2e_step1_invariant_affine_descent
    X Y G a ha1 hamul q hinv hquot U hU (F.coeff n) (hF n)
  choose c he hu using hc
  let P : Polynomial Γ(Y.left, U) := ∑ n ∈ F.support, Polynomial.monomial n (c n)
  have hP : P.map (q.left.app U).hom = F := by
    simp only [P, Polynomial.map_sum, Polynomial.map_monomial, he]
    exact Polynomial.sum_monomial_eq F
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  apply Polynomial.ext
  intro n
  have hQn := congrArg (fun R => Polynomial.coeff R n) hQ
  have hPn := congrArg (fun R => Polynomial.coeff R n) hP
  rw [Polynomial.coeff_map] at hQn hPn
  exact (hu n _ hQn).trans (hu n _ hPn).symm

end HodgeLean.Foundations.Program
