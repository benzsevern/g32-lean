import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedSupportChainSections
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionGlobalSections

/-! # Forgetting support in the original chain section kernel -/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original kernel inclusion, evaluated on the whole space.
Source: TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion.
-/
def retainedSupportForgetting (X : TopCat.{0}) (S : Closeds X) :
    TopCat.Sheaf.closedSupportSections X S ⟶ subdivisionGlobalSectionsFunctor X :=
  Functor.whiskerRight (TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl)
    (subdivisionGlobalSectionsFunctor X)

/-- The specified chain-kernel coordinates retain their literal inclusion into global sections. -/
lemma retained_support_kernel_iso_inclusion (X : TopCat.{0}) (S : Closeds X) :
    (properCycle_closed_support_chain_section_iso X S).hom ≫
      kernel.ι (TopCat.Sheaf.sectionComplexRestriction X (.down ℕ)
        (singularChainSheafComplex ℚ X) (homOfLE (show S.compl ≤ ⊤ from le_top))) =
    ((retainedSupportForgetting X S).mapHomologicalComplex (.down ℕ)).app
      (singularChainSheafComplex ℚ X) := by
  ext n : 1
  let K := singularChainSheafComplex ℚ X
  let r := TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) K
    (homOfLE (show S.compl ≤ ⊤ from le_top))
  change (TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n)).hom ≫
    (AddCommGrpCat.kernelIsoKer (r.f n)).inv ≫
      (PreservesKernel.iso (HomologicalComplex.eval AddCommGrpCat (.down ℕ) n) r).inv ≫
        (HomologicalComplex.eval AddCommGrpCat (.down ℕ) n).map (kernel.ι r) = _
  have h₁ := PreservesKernel.iso_inv_ι
    (HomologicalComplex.eval AddCommGrpCat (.down ℕ) n) r
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (r.f n)
  have h₃ := TopCat.Sheaf.supportedSectionsIsoKer_hom_subtype X S.compl ⊤ S.compl
    (by simp) (K.X n)
  exact (congrArg (fun q =>
    (TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n)).hom ≫
      (AddCommGrpCat.kernelIsoKer (r.f n)).inv ≫ q) h₁).trans
    ((congrArg (fun q =>
      (TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n)).hom ≫ q)
      h₂).trans h₃)

/-- Forgetting support in the actual finite-chain construction is the original ambient chain inclusion. -/
lemma retained_supported_chain_forgetting (X : TopCat.{0}) (S : Closeds X) :
    properCycle_closed_support_chain_section_map X S ≫
      ((retainedSupportForgetting X S).mapHomologicalComplex (.down ℕ)).app
        (singularChainSheafComplex ℚ X) =
    ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
      (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom) ≫
        properCycle_chain_sheaf_section_map X ⊤ := by
  rw [← retained_support_kernel_iso_inclusion]
  unfold properCycle_closed_support_chain_section_map
  rw [← Category.assoc, Category.assoc (properCycle_supported_chain_section_map X S),
    Iso.inv_hom_id, Category.comp_id]
  exact kernel.lift_ι _ _ _

end HodgeLean.Foundations.QuotientDuality
