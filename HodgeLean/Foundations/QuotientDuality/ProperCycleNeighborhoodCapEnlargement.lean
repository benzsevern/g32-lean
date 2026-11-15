import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Actual neighborhood cap under enlargement of original supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Enlarging the original cohomological support leaves its actual cap class unchanged in a common open neighborhood.
Source: Hatcher, Algebraic Topology, section 3.3, cap naturality for inclusions of support pairs.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_cap_enlarge_support
    (X : TopCat.{0}) (S T U : Set X) (hS : IsClosed S) (hT : IsClosed T)
    (hU : IsOpen U) (hST : S ⊆ T) (hTU : T ⊆ U) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    properCycle_neighborhood_cap X S U hS hU (hST.trans hTU) p q a c =
      properCycle_neighborhood_cap X T U hT hU hTU p q
        (enlargeSupport ℚ X hST p a) c := by
  let f := supportInclusionPairMap X hST
  let g : neighborhoodSupportComplementPair U T ⟶ neighborhoodSupportComplementPair U S :=
    TopPair.ofSubsetHom (𝟙 (TopCat.of U)) (fun z hz hs => hz (hST hs))
  have hsquare : g ≫ HodgeLean.Foundations.Program.b6m_subspacePairMap X U Sᶜ =
      HodgeLean.Foundations.Program.b6m_subspacePairMap X U Tᶜ ≫ f := by
    ext z : 2 <;> rfl
  have hn := properCycle_neighborhood_cap_naturality X X T S U U hT hS hU hU
    hTU (hST.trans hTU) f g hsquare p q a c
  change homologyMap ℚ q (𝟙 (TopCat.of U))
    (properCycle_neighborhood_cap X T U hT hU hTU p q (enlargeSupport ℚ X hST p a) c) =
    properCycle_neighborhood_cap X S U hS hU (hST.trans hTU) p q a
      (homologyMap ℚ (p+q) (𝟙 X) c) at hn
  simpa only [homologyMap_id, LinearMap.id_apply] using hn.symm

end HodgeLean.Foundations.QuotientDuality
