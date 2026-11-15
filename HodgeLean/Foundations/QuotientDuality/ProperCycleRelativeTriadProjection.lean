import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriad
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadInclusion

/-! # Original relative chains projected into the actual two-subspace quotient
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal quotient from original relative chains to the actual triad quotient is the empty-triad inverse followed by enlargement of its second subspace.
Source: properCycle_empty_triad_relative_iso; properCycle_triad_inclusion_chain_map.
HC no distance; AV milestone no distance. -/
def properCycle_relative_to_triad_chain_map (X : TopCat.{0}) (A B : Set X) :
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A) ⟶
      triadRelativeChainComplex ℚ X A B :=
  (properCycle_empty_triad_relative_iso X A).inv ≫
    properCycle_triad_inclusion_chain_map X A ∅ B (Set.empty_subset B)

/-- Projection of original ordinary chains through the relative quotient is exactly the original triad projection.
Source: properCycle_empty_triad_relative_projection; properCycle_triad_projection_inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_to_triad_projection
    (X : TopCat.{0}) (A B : Set X) :
    relativeChainProjection ℚ (TopPair.ofSubset (X := X) A) ≫
      properCycle_relative_to_triad_chain_map X A B = triadRelativeChainProjection ℚ X A B := by
  unfold properCycle_relative_to_triad_chain_map
  rw [← properCycle_empty_triad_relative_projection X A,
    Category.assoc, Iso.hom_inv_id_assoc,
    properCycle_triad_projection_inclusion]

end HodgeLean.Foundations.QuotientDuality
