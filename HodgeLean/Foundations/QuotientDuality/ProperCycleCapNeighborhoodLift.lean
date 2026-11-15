import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapVanishing
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomologySupportLift

/-! # Actual cap classes lift to every open support neighborhood -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Capping any originally supported cohomology class yields an actual homology class of every open neighborhood of its support, with the original inclusion equation.
Source: Hatcher, Algebraic Topology, sections 2.1, 2.2 and 3.3, exactness and relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_lift_to_open_neighborhood
    (X : TopCat.{0}) (S : Set X) (hS : IsClosed S)
    (U : Set X) (hU : IsOpen U) (hSU : S ⊆ U) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    ∃ b : Homology ℚ (TopCat.of U) q,
      homologyMap ℚ q (TopPair.ofSubset (X := X) U).map b =
        capCohomologyLinear ℚ X p q
          ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  apply properCycle_homology_lift_of_relative_projection_zero X U q
  apply properCycle_cap_projection_zero_relative_cohomology X Sᶜ U hS.isOpen_compl hU
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x ∈ S
    · exact Or.inr (hSU hx)
    · exact Or.inl hx

end HodgeLean.Foundations.QuotientDuality
