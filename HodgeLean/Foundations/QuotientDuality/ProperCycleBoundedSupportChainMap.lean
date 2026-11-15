import HodgeLean.Foundations.QuotientDuality.ProperCycleChainExtensionSections
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedChainSheaf

/-! # Original finite support chains in actual bounded supported sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual original finite support chain map, extended with the literal negative grading and followed by the original bounded truncation projection under supported sections.
Source: properCycle_closed_support_chain_section_map; properCycle_section_functor_extend_iso; CochainComplex.πTruncGE.
HC no distance; AV milestone no distance. -/
def properCycle_bounded_support_chain_map (X : TopCat.{0}) (S : Closeds X) (N : ℕ) :
    ((((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).obj
        (SingularChainComplex ℚ (TopCat.of (S : Set X)))).extend ComplexShape.embeddingDownNat) ⟶
      ((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.up ℤ)).obj
        (properCycle_bounded_chain_sheaf X N).obj :=
  HomologicalComplex.extendMap (properCycle_closed_support_chain_section_map X S)
      ComplexShape.embeddingDownNat ≫
    (properCycle_section_functor_extend_iso (TopCat.Sheaf.closedSupportSections X S)
      (singularChainSheafComplex ℚ X)).hom ≫
    ((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.up ℤ)).map
      ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ)))

end HodgeLean.Foundations.QuotientDuality
