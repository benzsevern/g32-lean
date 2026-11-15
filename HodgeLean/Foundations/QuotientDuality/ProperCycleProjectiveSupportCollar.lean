import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenCollarSubspace
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMaps

/-! # Retained actual collars of original projective algebraic supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original algebraic closed support in a projective complex scheme has actual retained neighborhood maps and a deformation.
Source: properCycle_projective_closed_neighborhood_deformation; properCycle_open_collar_as_subspace.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_support_collar_nonempty
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left) :
    Nonempty (ProperCycleSupportCollar (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left))) := by
  let Z : Over (Spec ↧ℂ) := Over.mk (reducedClosedStructureMap X.hom S)
  let i : Z ⟶ X := properCycle_reduced_closed_map X S
  have hrange : Set.range (Point.map i) = Point.underlying ⁻¹' (S : Set X.left) := by
    rw [range_map_of_closedImmersion]
    change {z : ComplexPoint X | z.underlying ∈ Set.range (reducedClosedSubschemeι _)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  have hc := properCycle_projective_closed_neighborhood_deformation X Z i
  dsimp only at hc
  rw [hrange] at hc
  obtain ⟨U, j, k, hj, hk, r, hjr, H, _⟩ := hc
  obtain ⟨V, hV, hSV, jV, rV, hfactor, hfix, ⟨HV⟩⟩ :=
    properCycle_open_collar_as_subspace (TopCat.of (ComplexPoint X)) _ U j k hj hk r hjr H
  exact ⟨⟨V, hV, hSV, jV, rV, hfactor, hfix, HV⟩⟩

/-- Choose actual collar data, retaining every original topological map used by supported cap.
Source: properCycle_projective_support_collar_nonempty.
HC no distance; AV milestone no distance. -/
def properCycle_projective_support_collar
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left) :
    ProperCycleSupportCollar (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) :=
  Classical.choice (properCycle_projective_support_collar_nonempty X S)

end HodgeLean.Foundations.QuotientDuality
