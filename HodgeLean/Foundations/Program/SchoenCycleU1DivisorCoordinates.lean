import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialDescent
import HodgeLean.Foundations.Program.SchoenCycleU1PowerOpen
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Regular divisor coordinates on retained quotient charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Pull back a curve function to each coordinate on an actual quotient preimage chart.
Source: Hartshorne, Algebraic Geometry, II.2, pullback of regular functions. -/
def s2e_u1_coordinateSection (Z B : Over (Spec ↧ℂ)) (N : ℕ)
    (γ : g3_power Z N ⟶ B) (U : Z.left.Opens) (V : B.left.Opens)
    (hV : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (t : Γ(Z.left, U)) (i : Fin N) :
    Γ((g3_power Z N).left, γ.left ⁻¹ᵁ V) :=
  ((g3_proj Z N i).left.appLE U (γ.left ⁻¹ᵁ V) (by
    intro x hx
    exact (s2e_u1_mem_powerOpen Z N U x).mp (hV hx) i)).hom t

/-- The section of a coordinate transforms by the inverse permutation of its index.
Source: Hartshorne, Algebraic Geometry, II.2, functoriality of regular functions. -/
theorem s2e_u1_coordinateSection_permute (Z B : Over (Spec ↧ℂ)) (N : ℕ)
    (γ : g3_power Z N ⟶ B) (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (U : Z.left.Opens) (V : B.left.Opens)
    (hV : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (t : Γ(Z.left, U))
    (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    ((s2_permute Z N σ).left.appLE _ _
      (s2e_step1_action_preimage _ _ γ _ (hγ σ) V)).hom
        (s2e_u1_coordinateSection Z B N γ U V hV t i) =
      s2e_u1_coordinateSection Z B N γ U V hV t (σ.symm i) := by
  unfold s2e_u1_coordinateSection
  have he := Scheme.Hom.appLE_comp_appLE (s2_permute Z N σ).left
    (g3_proj Z N i).left U (γ.left ⁻¹ᵁ V) (γ.left ⁻¹ᵁ V)
    (by intro x hx; exact (s2e_u1_mem_powerOpen Z N U x).mp (hV hx) i)
    (s2e_step1_action_preimage _ _ γ _ (hγ σ) V)
  have hp : (s2_permute Z N σ).left ≫ (g3_proj Z N i).left =
      (g3_proj Z N (σ.symm i)).left := by
    change (s2_permute Z N σ ≫ g3_proj Z N i).left = _
    simp only [s2_permute, s2_check_lift_proj]
  simp only [hp] at he
  exact congrArg (fun f => f.hom t) he

/-- The monic root polynomial of a curve function is invariant on the actual
preimage chart, with repeated coordinates retained.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1. -/
theorem s2e_u1_coordinatePolynomial_invariant (Z B : Over (Spec ↧ℂ)) (N : ℕ)
    (γ : g3_power Z N ⟶ B) (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (U : Z.left.Opens) (V : B.left.Opens)
    (hV : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (t : Γ(Z.left, U))
    (σ : Equiv.Perm (Fin N)) :
    (∏ i : Fin N, (Polynomial.X - Polynomial.C
      (s2e_u1_coordinateSection Z B N γ U V hV t i))).map
      ((s2_permute Z N σ).left.appLE _ _
        (s2e_step1_action_preimage _ _ γ _ (hγ σ) V)).hom =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C
        (s2e_u1_coordinateSection Z B N γ U V hV t i)) := by
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C,
    s2e_u1_coordinateSection_permute Z B N γ hγ U V hV t σ]
  exact σ.symm.prod_comp (fun i => Polynomial.X - Polynomial.C
    (s2e_u1_coordinateSection Z B N γ U V hV t i))

/-- A regular curve coordinate determines a unique polynomial on the retained affine
quotient chart whose pullback is the ordered root polynomial, also at collisions.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1. -/
theorem s2e_u1_retained_divisor_coordinate_polynomial
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : Z.left.Opens) (V : B.left.Opens) (hV : IsAffineOpen V)
    (hVU : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (t : Γ(Z.left, U)) :
    ∃! Q : Polynomial Γ(B.left, V), Q.map (γ.left.app V).hom =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C
        (s2e_u1_coordinateSection Z B N γ U V hVU t i)) := by
  exact s2e_u1_invariant_polynomial_descent Z B N γ hsurj hγ hquot V hV _
    (s2e_u1_coordinatePolynomial_invariant Z B N γ hγ U V hVU t)

end HodgeLean.Foundations.Program
