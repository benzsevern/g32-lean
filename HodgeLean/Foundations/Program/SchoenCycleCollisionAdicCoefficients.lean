import HodgeLean.Foundations.Program.SchoenCycleCollisionAdicInvariants
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # Exact elementary coefficient lifts in actual adic stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A symmetric polynomial in actual curve-power parameters has a unique exact
lift to the actual downstairs adic stalk at a total collision.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_total_collision_symmetric_polynomial_adic_lift
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) 
    (p : MvPolynomial (Fin n) ℂ) (hp : IsSymmetric p) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃! y : AdicCompletion (IsLocalRing.maximalIdeal S) S,
      s2e_adic_stalkMap γ.left x.underlying y =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (aeval (s2e_curvePowerParameter Z n x) p) := by
  intro R S
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  apply (s2e_total_collision_adic_stalkMap_invariants Z B n γ hγ hquot x a hx _).mp
  intro σ
  rw [s2e_fixed_permutation_adic_parameter_polynomial Z n σ x
    (s2e_total_collision_permutation_fixed Z n x a hx σ) p, hp σ.symm]

#print axioms s2e_total_collision_symmetric_polynomial_adic_lift
/-- The elementary polynomials in actual curve-power parameters have a unique
family of exact lifts to the downstairs adic stalk.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_total_collision_adic_elementary_coefficients
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) 
    : let R := (g3_power Z n).left.presheaf.stalk x.underlying
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃! c : Fin n → AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ j, s2e_adic_stalkMap γ.left x.underlying (c j) =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (aeval (s2e_curvePowerParameter Z n x) (esymm (Fin n) ℂ (j.val + 1))) := by
  intro R S
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  have H (j : Fin n) := s2e_total_collision_symmetric_polynomial_adic_lift
    Z B n γ hγ hquot x a hx (esymm (Fin n) ℂ (j.val + 1))
      (esymm_isSymmetric (Fin n) ℂ (j.val + 1))
  choose c hc hu using H
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact funext (fun j => hu j (d j) (hd j))

#print axioms s2e_total_collision_adic_elementary_coefficients
end HodgeLean.Foundations.Program
