import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveClosedNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapOpenCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMaps

/-! # Actual cap lifts on original projective algebraic supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Capping a class supported on an original algebraic closed subset lifts to the homology of that same subset.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; properCycle_projective_closed_neighborhood_deformation.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_algebraic_cap_support
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left)
    (p q : ℕ)
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) p)
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p + q)) :
    ∃ b : Homology ℚ (TopCat.of (Point.underlying ⁻¹' (S : Set X.left))) q,
      homologyMap ℚ q (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
        (Point.underlying ⁻¹' (S : Set X.left))).map b =
      capCohomologyLinear ℚ (TopCat.of (ComplexPoint X)) p q
        ((cochainCohomologyEquiv ℚ (TopCat.of (ComplexPoint X)) p).symm
          (forgetSupport ℚ (TopCat.of (ComplexPoint X))
            (Point.underlying ⁻¹' (S : Set X.left)) p a)) c := by
  let Z : Over (Spec ↧ℂ) := Over.mk (reducedClosedStructureMap X.hom S)
  let i : Z ⟶ X := properCycle_reduced_closed_map X S
  have hrange : Set.range (Point.map i) = Point.underlying ⁻¹' (S : Set X.left) := by
    rw [range_map_of_closedImmersion]
    change {z : ComplexPoint X | z.underlying ∈ Set.range (reducedClosedSubschemeι _)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  have hcollar := properCycle_projective_closed_neighborhood_deformation X Z i
  dsimp only at hcollar
  rw [hrange] at hcollar
  obtain ⟨U, j, k, hj, hk, r, _, H, _⟩ := hcollar
  have hcS := isClosed_range_map_of_closedImmersion i
  rw [hrange] at hcS
  exact properCycle_cap_factor_through_open_collar (TopCat.of (ComplexPoint X))
    _ hcS U j k hj hk r H p q a c

end HodgeLean.Foundations.QuotientDuality
