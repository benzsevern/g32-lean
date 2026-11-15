import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCap
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Actual relative fundamental classes under neighborhood excision -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual relative fundamental class in a support neighborhood, obtained by inverting the checked canonical excision map on the original projected class.
Source: Hatcher, Algebraic Topology, section 2.2, excision and local fundamental classes.
HC no distance; AV milestone no distance. -/
noncomputable def properCycle_neighborhood_relative_fundamental
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (n : ℕ) (c : Homology ℚ X n) :
    RelativeHomology ℚ (neighborhoodSupportComplementPair U S) n :=
  (LinearEquiv.ofBijective (relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ))
    (b6m_closed_support_excision_bijective ℚ hU hS hSU n)).symm
    ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) n).hom c)

/-- The actual excised relative fundamental class maps to the original projected fundamental class.
Source: Hatcher, Algebraic Topology, section 2.2, canonical excision isomorphism.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_relative_fundamental_pushforward
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ)
      (properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c) =
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) n).hom c :=
  (LinearEquiv.ofBijective (relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ))
    (b6m_closed_support_excision_bijective ℚ hU hS hSU n)).apply_symm_apply _

end HodgeLean.Foundations.QuotientDuality
