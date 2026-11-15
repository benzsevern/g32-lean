import HodgeLean.Foundations.QuotientDuality.ProperCycleStrongSupportCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCollar

/-! # Actual support-fixing collar data on original projective supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original projective algebraic support has actual collar maps whose retained deformation fixes every original support point.
Source: properCycle_projective_closed_neighborhood_deformation; properCycle_strong_open_collar_data.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_strong_support_collar_nonempty
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left) :
    Nonempty (ProperCycleStrongSupportCollar (TopCat.of (ComplexPoint X))
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
  obtain ⟨U, j, k, hj, hk, r, hjr, H, hfixed⟩ := hc
  exact properCycle_strong_open_collar_data (TopCat.of (ComplexPoint X)) _ U
    j k hj hk r hjr H hfixed

/-- The selected data retain an actual support-fixing deformation on a literal original neighborhood.
Source: properCycle_projective_strong_support_collar_nonempty.
HC no distance; AV milestone no distance. -/
def properCycle_projective_strong_support_collar
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left) :
    ProperCycleStrongSupportCollar (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) :=
  Classical.choice (properCycle_projective_strong_support_collar_nonempty X S)

end HodgeLean.Foundations.QuotientDuality
