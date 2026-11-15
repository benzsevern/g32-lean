import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamental

/-! # Restriction of actual excised relative fundamental classes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Shrinking an actual support neighborhood preserves the excised original relative fundamental class under the literal inclusion of neighborhood pairs.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_relative_fundamental_restriction
    (X : TopCat.{0}) (S U V : Set X) (hS : IsClosed S) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hSV : S ⊆ V) (hVU : V ⊆ U) (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (neighborhoodSupportInclusionPairMap hVU S)
      (properCycle_neighborhood_relative_fundamental X S V hS hV hSV n c) =
      properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c := by
  apply (b6m_closed_support_excision_bijective ℚ hU hS hSU n).injective
  have hf : neighborhoodSupportInclusionPairMap hVU S ≫ b6m_subspacePairMap X U Sᶜ =
      b6m_subspacePairMap X V Sᶜ := by
    ext x : 2 <;> rfl
  have hm : (relativeHomologyMap ℚ n (b6m_subspacePairMap X U Sᶜ)).comp
      (relativeHomologyMap ℚ n (neighborhoodSupportInclusionPairMap hVU S)) =
      relativeHomologyMap ℚ n (b6m_subspacePairMap X V Sᶜ) := by
    rw [← relativeHomologyMap_comp, hf]
  calc
    _ = relativeHomologyMap ℚ n (b6m_subspacePairMap X V Sᶜ)
        (properCycle_neighborhood_relative_fundamental X S V hS hV hSV n c) :=
      LinearMap.congr_fun hm _
    _ = _ := (properCycle_neighborhood_relative_fundamental_pushforward X S V hS hV hSV n c).trans
      (properCycle_neighborhood_relative_fundamental_pushforward X S U hS hU hSU n c).symm

end HodgeLean.Foundations.QuotientDuality
