import HodgeLean.Foundations.Program.SchoenCycleS1i1Proofs

/-! # Coefficient parameters at a total collision
Implication from the explicit inputs to the first infrastructure part.
Further comparison steps are listed in docs/specs/s2e-s1bci.md.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical BigOperators
namespace HodgeLean.Foundations.Program

/-- Coefficient parameters at a total collision.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, §3, symmetric products;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_collision_coefficient_parameters
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (N : ℕ) (hN : n < N) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : Fin n → S,
      IsLocalRing.maximalIdeal S = Ideal.span (Set.range c) ∧
      (∀ j, γ.left.stalkMap x.underlying (c j) -
        aeval (s2e_curvePowerParameter Z n x) (esymm (Fin n) ℂ (j.val + 1)) ∈
        IsLocalRing.maximalIdeal R ^ N) :=
  s2e_collision_coefficient_parameters_aux Z B n γ hγ hquot x a hx N hN

example := @s2e_collision_coefficient_parameters

end HodgeLean.Foundations.Program
