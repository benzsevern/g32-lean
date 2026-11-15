import HodgeLean.Foundations.QuotientDuality.ProperCycleChainSheafSectionRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedChainSectionVanishing

/-! # Actual supported finite-chain comparison to the original chain sheaf section kernel
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual kernel complex of chain sheaf section restriction to the complement of the original support.
Source: TopCat.Sheaf.sectionComplexRestriction; kernel in the category of chain complexes; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
def properCycle_supported_chain_section_complex (X : TopCat.{0}) (S : Closeds X) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  kernel (TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) (singularChainSheafComplex ℚ X)
    (homOfLE (show S.compl ≤ ⊤ from le_top)))

/-- Include original finite singular chains on the literal closed support into the actual kernel of the ambient chain sheaf section restriction map.
Source: properCycle_chain_sheaf_section_map_restrict; properCycle_supported_chain_sheaf_section_zero; kernel.lift.
HC no distance; AV milestone no distance. -/
def properCycle_supported_chain_section_map (X : TopCat.{0}) (S : Closeds X) :
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).obj
        (SingularChainComplex ℚ (TopCat.of (S : Set X))) ⟶
      properCycle_supported_chain_section_complex X S := by
  let F := (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)
  let r := TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) (singularChainSheafComplex ℚ X)
    (homOfLE (show S.compl ≤ ⊤ from le_top))
  refine kernel.lift r
    (F.map (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom) ≫
      properCycle_chain_sheaf_section_map X ⊤) ?_
  rw [Category.assoc, properCycle_chain_sheaf_section_map_restrict]
  exact properCycle_supported_chain_sheaf_section_zero X (S : Set X) S.compl
    (fun x hx h => h hx)

example (X : TopCat.{0}) (S : Closeds X) :
    properCycle_supported_chain_section_map X S ≫
      kernel.ι (TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) (singularChainSheafComplex ℚ X)
        (homOfLE (show S.compl ≤ ⊤ from le_top))) =
      ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).map
          (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom) ≫
        properCycle_chain_sheaf_section_map X ⊤ := by
  exact kernel.lift_ι _ _ _

end HodgeLean.Foundations.QuotientDuality
