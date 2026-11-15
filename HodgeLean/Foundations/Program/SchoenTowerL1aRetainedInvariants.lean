import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantComparison

/-! # Actual invariant rings for the retained symmetric quotient

The affine section pullback for the given quotient is injective, with image
exactly the sections fixed by the retained permutations.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The specified finite symmetric categorical quotient has the actual invariant section rings on every affine target open.
Source: Stacks Project, tags 04A9 and 01LH, invariant rings and relative affine gluing. -/
theorem s2v_l1a_retained_affine_invariants
    (Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (W : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ W),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B ⟶ W, γ ≫ u = f)
    (U : B.left.affineOpens) :
    Function.Injective (γ.left.app U.1).hom ∧
      ∀ s : Γ((g3_power Z (h + 1)).left, γ.left ⁻¹ᵁ U.1),
        s ∈ Set.range (γ.left.app U.1).hom ↔
          ∀ τ, (s2v_l1a_saturatedSectionEnd γ.left
            (fun τ => (s2_permute Z (h + 1) τ).left)
            (fun τ => congrArg (fun f : g3_power Z (h + 1) ⟶ B => f.left) (hγinv τ))
            U.1 τ).hom s = s := by
  exact s2v_l1a_affine_sections_range_of_categorical_quotient
    (g3_power Z (h + 1)) B γ (s2_permute Z (h + 1)) hγinv hγ U

end HodgeLean.Foundations.Program
