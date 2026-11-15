import HodgeLean.Foundations.QuotientDuality.RetainedCycleSectionExtensionCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportForgetting
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedSupportChainMap

/-! # Forgetting support in the original bounded chain construction -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace HodgeLean.Foundations.QuotientDuality

/-- Forgetting support commutes with the literal bounded finite-chain map. -/
lemma retained_bounded_support_forgetting (X : TopCat.{0}) (S : Closeds X) (N : ℕ) :
    properCycle_bounded_support_chain_map X S N ≫
      ((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (properCycle_bounded_chain_sheaf X N).obj =
    extendMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
        (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom) ≫
          properCycle_chain_sheaf_section_map X ⊤) ComplexShape.embeddingDownNat ≫
      (properCycle_section_functor_extend_iso (subdivisionGlobalSectionsFunctor X)
        (singularChainSheafComplex ℚ X)).hom ≫
      ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
        ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ))) := by
  let τ := retainedSupportForgetting X S
  have h := (τ.mapHomologicalComplex (.up ℤ)).naturality
    ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ)))
  unfold properCycle_bounded_support_chain_map
  dsimp only [properCycle_bounded_chain_sheaf]
  dsimp only [τ] at h
  simp only [Category.assoc]
  rw [h]
  have he := retained_section_extension_naturality
    (TopCat.Sheaf.closedSupportSections X S) (subdivisionGlobalSectionsFunctor X)
    (retainedSupportForgetting X S) (singularChainSheafComplex ℚ X)
  change (properCycle_section_functor_extend_iso (TopCat.Sheaf.closedSupportSections X S)
    (singularChainSheafComplex ℚ X)).hom ≫
      ((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (singularChainSheafCochainComplex ℚ X) = _ at he
  rw [← Category.assoc
    (properCycle_section_functor_extend_iso (TopCat.Sheaf.closedSupportSections X S)
      (singularChainSheafComplex ℚ X)).hom, he]
  simp only [Category.assoc]
  rw [← Category.assoc (extendMap (properCycle_closed_support_chain_section_map X S)
    ComplexShape.embeddingDownNat)
      (extendMap (((retainedSupportForgetting X S).mapHomologicalComplex (.down ℕ)).app
        (singularChainSheafComplex ℚ X)) ComplexShape.embeddingDownNat),
    ← extendMap_comp, retained_supported_chain_forgetting]

end HodgeLean.Foundations.QuotientDuality
