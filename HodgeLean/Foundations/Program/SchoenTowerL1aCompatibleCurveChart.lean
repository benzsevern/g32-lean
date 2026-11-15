import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedRefinement
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedOrbit

/-! # Compatible curve charts for the retained quotient

Implication from an actual ordered curve neighborhood containing the specified
point to a retained affine quotient restriction factoring through that neighborhood.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual saturated affine source of the retained quotient can be
chosen to factor openly through the prescribed ordered curve neighborhood.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Stacks Project, tag 04A9. -/
theorem s2v_l1a_compatible_curve_chart
    (A Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (a : A ⟶ Z) [IsOpenImmersion a.left]
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (x : ComplexPoint (g3_power Z (h + 1))) (y : ComplexPoint (g3_power A (h + 1)))
    (hy : Point.map (s2_powerMap a (h + 1)) y = x) :
    ∃ U : B.left.affineOpens, x.underlying ∈ γ.left ⁻¹ᵁ U.1 ∧
      ∃ j : ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ U.1) ⟶
          g3_power A (h + 1),
        IsOpenImmersion j.left ∧
        j ≫ s2_powerMap a (h + 1) =
          ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ U.1) := by
  let X := g3_power Z (h + 1)
  let f := s2_powerMap a (h + 1)
  letI : IsOpenImmersion f.left := s2v_l1a_ordered_power_open a (h + 1)
  let W := f.left.opensRange
  have hW (τ : Equiv.Perm (Fin (h + 1))) :
      (Point.map (s2_permute Z (h + 1) τ) x).underlying ∈ W :=
    s2v_l1a_ordered_orbit_in_range a (h + 1) x y hy τ
  obtain ⟨U, hx, hsub⟩ := s2v_l1a_retained_affine_refinement Z B h γ hγinv hγ x W hW
  let V := γ.left ⁻¹ᵁ U.1
  let Vo := ComplexPoint.openScheme X V
  let v : Vo ⟶ X := ComplexPoint.openInclusion X V
  have hrange : Set.range v.left ⊆ Set.range f.left := by
    rintro _ ⟨z, rfl⟩
    exact hsub z.2
  let j' := IsOpenImmersion.lift f.left v.left hrange
  have hj : j' ≫ f.left = v.left := IsOpenImmersion.lift_fac f.left v.left hrange
  let j : Vo ⟶ g3_power A (h + 1) := Over.homMk j' (by
    rw [← Over.w f, ← Category.assoc, hj]
    rfl)
  have hjover : j ≫ f = v := by
    apply Over.OverMorphism.ext
    exact hj
  letI : IsOpenImmersion (j' ≫ f.left) := by
    rw [hj]
    exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨U, hx, j, ?_, hjover⟩
  exact IsOpenImmersion.of_comp j' f.left

end HodgeLean.Foundations.Program
