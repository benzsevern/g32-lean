import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedChainSections
import HodgeConjecture.Definitions.AlgebraicTopology.Support.CohomologyInjectiveModel

/-! # Actual closed support sections of the original chain sheaf complex
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace Opposite
namespace HodgeLean.Foundations.QuotientDuality

/-- The original functor of sections with closed support on the chain sheaf complex is canonically the actual kernel complex of restriction to the support complement.
Source: TopCat.Sheaf.supportedSectionsIsoKer; PreservesKernel.iso; HomologicalComplex.Hom.isoOfComponents.
HC no distance; AV milestone no distance. -/
def properCycle_closed_support_chain_section_iso (X : TopCat.{0}) (S : Closeds X) :
    ((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.down ℕ)).obj
        (singularChainSheafComplex ℚ X) ≅
      properCycle_supported_chain_section_complex X S := by
  let K := singularChainSheafComplex ℚ X
  let A := ((TopCat.Sheaf.closedSupportSections X S).mapHomologicalComplex (.down ℕ)).obj K
  let r := TopCat.Sheaf.sectionComplexRestriction X (.down ℕ) K
    (homOfLE (show S.compl ≤ ⊤ from le_top))
  let I : A ⟶ ((TopCat.Sheaf.supportEvaluation X ⊤).mapHomologicalComplex (.down ℕ)).obj K :=
    ((TopCat.Sheaf.supportEvaluation X ⊤).mapHomologicalComplex (.down ℕ)).map
      (((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl).mapHomologicalComplex
        (.down ℕ)).app K)
  let e (n : ℕ) : A.X n ≅ (properCycle_supported_chain_section_complex X S).X n :=
    TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n) ≪≫
      (AddCommGrpCat.kernelIsoKer (r.f n)).symm ≪≫
        (PreservesKernel.iso (HomologicalComplex.eval AddCommGrpCat.{0} (.down ℕ) n) r).symm
  have he (n : ℕ) : (e n).hom ≫ (kernel.ι r).f n = I.f n := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    change _ ≫ _ ≫ (PreservesKernel.iso (HomologicalComplex.eval AddCommGrpCat.{0} (.down ℕ) n) r).inv ≫
      (HomologicalComplex.eval AddCommGrpCat.{0} (.down ℕ) n).map (kernel.ι r) = _
    have h₁ := PreservesKernel.iso_inv_ι
      (HomologicalComplex.eval AddCommGrpCat.{0} (.down ℕ) n) r
    have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (r.f n)
    have h₃ := TopCat.Sheaf.supportedSectionsIsoKer_hom_subtype X S.compl ⊤ S.compl
      (by simp) (K.X n)
    exact (congrArg (fun t =>
      (TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n)).hom ≫
        (AddCommGrpCat.kernelIsoKer (r.f n)).inv ≫ t) h₁).trans
      ((congrArg (fun t =>
        (TopCat.Sheaf.supportedSectionsIsoKer X S.compl ⊤ S.compl (by simp) (K.X n)).hom ≫ t)
        h₂).trans h₃)
  exact HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    apply (cancel_mono ((kernel.ι r).f j)).1
    change ((e i).hom ≫ (kernel r).d i j) ≫ (kernel.ι r).f j =
      (A.d i j ≫ (e j).hom) ≫ (kernel.ι r).f j
    rw [Category.assoc, ← (kernel.ι r).comm i j, ← Category.assoc, he,
      Category.assoc, he]
    exact I.comm i j)

example (X : TopCat.{0}) (S : Closeds X) :
    (properCycle_closed_support_chain_section_iso X S).inv ≫
      (properCycle_closed_support_chain_section_iso X S).hom = 𝟙 _ :=
  Iso.inv_hom_id _

end HodgeLean.Foundations.QuotientDuality
