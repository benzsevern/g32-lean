import HodgeLean.Foundations.Program.SchoenCycleS1i3Proofs

/-! # Actual branch equation at a total collision
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

/-- Actual branch equation at a total collision.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_collision_branch_local_equation
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (q : ℕ) (hq : n = q + 1) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    ∃ (U : B.left.affineOpens) (hu : γ.left x.underlying ∈ U.1)
      (c : Γ(B.left, U.1)),
      (s2c_branchIdeal Z B q γq a).ideal U = Ideal.span {c} ∧
      γ.left.stalkMap x.underlying
        (B.left.presheaf.germ U.1 (γ.left x.underlying) hu c) -
          (∏ i : Fin n, s2e_curvePowerParameter Z n x i) ∈
        IsLocalRing.maximalIdeal R ^ (n + 1) :=
  s2e_collision_branch_local_equation_aux Z B n γ hγ hquot x a hx q hq

example := @s2e_collision_branch_local_equation

end HodgeLean.Foundations.Program
