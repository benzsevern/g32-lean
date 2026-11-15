import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamentalRestriction

/-! # Actual neighborhood cap compatibility under shrinking -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Shrinking an actual open support neighborhood preserves the constructed neighborhood cap class under its literal inclusion map.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and relative cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_cap_restriction
    (X : TopCat.{0}) (S U V : Set X) (hS : IsClosed S) (hU : IsOpen U) (hV : IsOpen V)
    (hSU : S ⊆ U) (hSV : S ⊆ V) (hVU : V ⊆ U) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    homologyMap ℚ q (TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVU S))
      (properCycle_neighborhood_cap X S V hS hV hSV p q a c) =
      properCycle_neighborhood_cap X S U hS hU hSU p q a c := by
  let f := neighborhoodSupportInclusionPairMap hVU S
  let fU := b6m_subspacePairMap X U Sᶜ
  let fV := b6m_subspacePairMap X V Sᶜ
  let dU := properCycle_neighborhood_relative_fundamental X S U hS hU hSU (p + q) c
  let dV := properCycle_neighborhood_relative_fundamental X S V hS hV hSV (p + q) c
  have hf : f ≫ fU = fV := by ext x : 2 <;> rfl
  have ha : relativeCohomologyMap ℚ p f (relativeCohomologyMap ℚ p fU a) =
      relativeCohomologyMap ℚ p fV a := by
    have hm := relativeCohomologyMap_comp ℚ p f fU
    rw [hf] at hm
    exact (LinearMap.congr_fun hm a).symm
  have hd : relativeHomologyMap ℚ (p + q) f dV = dU :=
    properCycle_neighborhood_relative_fundamental_restriction X S U V hS hU hV hSU hSV hVU (p + q) c
  change homologyMap ℚ q (TopPair.Hom.fst f)
    (relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair V S) p q
      (relativeCohomologyMap ℚ p fV a) dV) =
    relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair U S) p q
      (relativeCohomologyMap ℚ p fU a) dU
  refine (congrArg (fun z => homologyMap ℚ q (TopPair.Hom.fst f)
    (relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair V S) p q z dV)) ha.symm).trans ?_
  exact (properCycle_relative_cap_naturality f p q (relativeCohomologyMap ℚ p fU a) dV).trans
    (congrArg (relativeCapCohomologyLinear ℚ (neighborhoodSupportComplementPair U S) p q
      (relativeCohomologyMap ℚ p fU a)) hd)

end HodgeLean.Foundations.QuotientDuality
