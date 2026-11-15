import HodgeLean.Foundations.Program.SchoenCycleCollisionBlocks

/-! # Actual quotient sections realizing collision coefficient jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Every elementary coefficient on a collision block is represented to any
finite order by an actual section of the retained quotient.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1;
Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12. -/
theorem s2e_retained_collision_coefficient_jet_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U) (H : Subgroup (Equiv.Perm (Fin n)))
    (x : ComplexPoint (g3_power Z n)) (hx : ⊤ ≤ x.left ⁻¹ᵁ (γ.left ⁻¹ᵁ U))
    (hH : ∀ σ, Point.map (s2_permute Z n σ) x = x ↔ σ ∈ H)
    (a : ComplexPoint Z) (N j : ℕ) :
    let S := Finset.univ.filter (fun i : Fin n => Point.map (g3_proj Z n i) x = a)
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : Γ(B.left, U),
      ((g3_power Z n).left.presheaf.germ (γ.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom
        ((γ.left.app U).hom c) - aeval (s2e_curvePowerParameter Z n x)
          (rename (fun i : S => (i : Fin n)) (esymm S ℂ j)) ∈
        IsLocalRing.maximalIdeal R ^ N := by
  let S := Finset.univ.filter (fun i : Fin n => Point.map (g3_proj Z n i) x = a)
  have hinv : ∀ σ ∈ H, rename σ
      (rename (fun i : S => (i : Fin n)) (esymm S ℂ j)) =
      rename (fun i : S => (i : Fin n)) (esymm S ℂ j) := by
    intro σ hσ
    apply s2e_block_elementary_rename
    intro i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact s2e_fixed_tuple_collision_block Z n x a σ ((hH σ).mpr hσ) i
  exact s2e_retained_invariant_parameter_jet_descent Z B n γ hγ hquot U hU H x hx hH
    N (rename (fun i : S => (i : Fin n)) (esymm S ℂ j)) hinv

end HodgeLean.Foundations.Program
