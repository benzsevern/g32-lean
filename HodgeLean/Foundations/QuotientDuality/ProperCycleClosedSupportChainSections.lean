import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedChainSectionKernelIso

/-! # Finite support chains in the original closed support section complex
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual finite singular chains on the specified support map to the original functor of closed support sections applied to the original chain sheaf complex.
Source: properCycle_supported_chain_section_map; properCycle_closed_support_chain_section_iso.
HC no distance; AV milestone no distance. -/
def properCycle_closed_support_chain_section_map (X : TopCat.{0}) (S : Closeds X) :
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).obj
        (SingularChainComplex ℚ (TopCat.of (S : Set X))) ⟶
      ((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.down ℕ)).obj
        (singularChainSheafComplex ℚ X) :=
  properCycle_supported_chain_section_map X S ≫
    (properCycle_closed_support_chain_section_iso X S).inv

example (X : TopCat.{0}) (S : Closeds X) :
    properCycle_closed_support_chain_section_map X S ≫
      (properCycle_closed_support_chain_section_iso X S).hom =
      properCycle_supported_chain_section_map X S := by
  unfold properCycle_closed_support_chain_section_map
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HodgeLean.Foundations.QuotientDuality
