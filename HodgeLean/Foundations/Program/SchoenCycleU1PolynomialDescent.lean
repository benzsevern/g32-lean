import HodgeLean.Foundations.Program.SchoenCycleU1Local
import Mathlib.Algebra.Polynomial.Degree.Support

/-! # Polynomial descent along retained quotient charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Polynomials whose coefficients are invariant descend uniquely to the actual affine
chart of the retained quotient, without a reduced-point restriction.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1. -/
theorem s2e_u1_invariant_polynomial_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (V : B.left.Opens) (hV : IsAffineOpen V)
    (P : Polynomial Γ((g3_power Z N).left, γ.left ⁻¹ᵁ V))
    (hP : ∀ σ, P.map ((s2_permute Z N σ).left.appLE _ _
      (s2e_step1_action_preimage _ _ γ _ (hγ σ) V)).hom = P) :
    ∃! Q : Polynomial Γ(B.left, V), Q.map (γ.left.app V).hom = P := by
  classical
  obtain ⟨e, he, _⟩ := s2e_u1_retained_quotient_invariant_chart Z B N γ hsurj hγ hquot V hV
  have hc (j : ℕ) : P.coeff j ∈ s2e_u1_invariantChartRing Z B N γ hγ V := by
    intro σ
    simpa only [Polynomial.coeff_map] using congrArg (fun Q => Q.coeff j) (hP σ)
  let Q : Polynomial Γ(B.left, V) := ∑ j ∈ P.support,
    Polynomial.C (e.symm ⟨P.coeff j, hc j⟩) * Polynomial.X ^ j
  have hf (j : ℕ) : (γ.left.app V).hom (e.symm ⟨P.coeff j, hc j⟩) = P.coeff j := by
    rw [← he]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hQ : Q.map (γ.left.app V).hom = P := by
    simp only [Q, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, hf]
    exact P.as_sum_support_C_mul_X_pow.symm
  refine ⟨Q, hQ, ?_⟩
  intro R hR
  apply Polynomial.map_injective _ ?_ (hR.trans hQ.symm)
  intro a b hab
  apply e.injective
  apply Subtype.ext
  simpa only [he] using hab

end HodgeLean.Foundations.Program
