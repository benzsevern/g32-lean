import HodgeLean.Foundations.QuotientDuality.ProperCycleChainSheafSections

/-! # Literal components of the original finite-chain section comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Opposite
namespace HodgeLean.Foundations.QuotientDuality

/-- Each component of the actual chain-section comparison is precisely the original relative projection followed by the original sheafification unit on that open.
Source: properCycle_chain_sheaf_section_map; singularChainPresheafComplexEvaluationIso.
HC no distance; AV milestone no distance. -/
lemma properCycle_chain_sheaf_section_map_component (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (properCycle_chain_sheaf_section_map X U).f n =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) ≫
        (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X n)).app (op U) := by
  ext c
  rfl

end HodgeLean.Foundations.QuotientDuality
