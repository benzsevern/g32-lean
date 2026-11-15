import HodgeLean.Foundations.QuotientDuality.ProperCycleChainSheafSectionComponents
import HodgeLean.Foundations.QuotientDuality.ProperCycleChainStalk

/-! # Actual open restriction of original finite-chain sheaf sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Opposite
namespace HodgeLean.Foundations.QuotientDuality

/-- The original finite-chain section map commutes with the actual restriction map of the chain sheaf section complexes on nested opens.
Source: properCycle_relative_projection_restrict; properCycle_chain_sheaf_section_map_component; toSheafify naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_chain_sheaf_section_map_restrict
    (X : TopCat.{0}) {U V : Opens X} (h : V ≤ U) :
    properCycle_chain_sheaf_section_map X U ≫
      TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) (singularChainSheafComplex ℚ X)
        (homOfLE h) = properCycle_chain_sheaf_section_map X V := by
  ext n c
  let P := singularChainPresheaf ℚ X n
  let unit := toSheafify (Opens.grothendieckTopology X) P
  change ((sheafify (Opens.grothendieckTopology X) P).map (homOfLE h).op)
      (unit.app (op U) ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n c)) =
    unit.app (op V) ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n c)
  have hn := ConcreteCategory.congr_hom (unit.naturality (homOfLE h).op)
    ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n c)
  have hpmap := congrArg (fun f => (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (f.f n))
    (properCycle_relative_projection_restrict X (show (V : Set X) ⊆ U from h))
  have hp := ConcreteCategory.congr_hom hpmap c
  change P.map (homOfLE h).op
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n c) =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n c at hp
  exact hn.symm.trans (congrArg (fun d => unit.app (op V) d) hp)

end HodgeLean.Foundations.QuotientDuality
