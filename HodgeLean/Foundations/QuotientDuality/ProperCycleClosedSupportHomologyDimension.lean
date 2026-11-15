import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedProjectiveStructure
import HodgeLean.Adapters.NormalConeB4aGysinReducedClosedDimension

/-! # Ordinary homology of original projective algebraic closed supports -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- An original algebraic closed support in a projective scheme has zero ordinary rational homology above twice its own algebraic dimension.
Source: properCycle_closed_projective_structure; properCycle_projective_homology_dimension_vanishes; range_map_of_closedImmersion.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_closed_support_homology_vanishes
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left)
    (d : ℕ) (hdim : topologicalKrullDim S ≤ d) (n : ℕ) (hn : 2*d < n) :
    Subsingleton (Homology ℚ
      (TopCat.of {x : ComplexPoint X | x.underlying ∈ S}) n) := by
  let Y := Over.mk (reducedClosedStructureMap X.hom S)
  let j := properCycle_reduced_closed_map X S
  letI : IsProjective Y.hom := properCycle_closed_projective_structure X Y j
  have hr : Set.range (Point.map j) = {x : ComplexPoint X | x.underlying ∈ S} := by
    rw [range_map_of_closedImmersion]
    change {x : ComplexPoint X | x.underlying ∈ Set.range (reducedClosedSubschemeι S)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  let h : ComplexPoint Y ≃ₜ {x : ComplexPoint X | x.underlying ∈ S} :=
    (isEmbedding_map_of_closedImmersion j).toHomeomorph.trans (Homeomorph.setCongr hr)
  have hdY : topologicalKrullDim Y.left ≤ d := by
    change topologicalKrullDim (reducedClosedSubscheme S) ≤ d
    rw [HodgeLean.Adapters.a3b4a_gysin_reduced_closed_dimension_eq]
    exact hdim
  exact properCycle_homeomorph_homology_subsingleton
    (X := TopCat.of {x : ComplexPoint X | x.underlying ∈ S})
    (Y := TopCat.of (ComplexPoint Y)) h.symm n
      (properCycle_projective_homology_dimension_vanishes Y d hdY n hn)

end HodgeLean.Foundations.QuotientDuality
