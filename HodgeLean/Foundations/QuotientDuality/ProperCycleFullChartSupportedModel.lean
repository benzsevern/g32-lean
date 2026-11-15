import HodgeLean.Foundations.QuotientDuality.ProperCycleProductChartCohomology
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExcision
import HodgeConjecture.Definitions.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Actual supported models in full-target product charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual supported class has an original full-target chart model whose literal coordinate pullbacks retain all smaller neighborhood restrictions.
Source: TopPair.isoOfSubset; relativeCohomologyMap_comp; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_full_chart_supported_model
    (X : TopCat.{0}) (S : Set X) (E Y : Type) [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (htarget : e.target = Set.univ) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (n : ℕ) (a : CohomologyWithSupport ℚ X S n) :
    ∃ b : RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ)) n,
      ∀ (W : Set X) (hW : W ⊆ e.source),
        relativeCohomologyMap ℚ n (b6m_subspacePairMap X W Sᶜ) a =
          relativeCohomologyMap ℚ n
            (TopPair.ofSubsetHom (X := TopCat.of W) (Y := TopCat.of (E × Y))
              (TopCat.ofHom ⟨fun w => e w.val, (e.continuousOn.mono hW).domRestrict⟩)
              (show Set.MapsTo (fun w : W => e w.val) (Subtype.val ⁻¹' Sᶜ)
                (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) from
                fun w hw hz => hw ((hflat w.val (hW w.property)).mpr hz))) b := by
  let H : e.source ≃ₜ (E × Y) := e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _))
  let p : neighborhoodSupportComplementPair e.source S ≅
      TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) :=
    TopPair.isoOfSubset H (fun w => not_congr (hflat w.val w.property).symm)
  let C : RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ)) n ≅
      RelativeCohomology ℚ (neighborhoodSupportComplementPair e.source S) n :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso p))
  let b := C.toLinearEquiv.symm
    (relativeCohomologyMap ℚ n (b6m_subspacePairMap X e.source Sᶜ) a)
  have hb : relativeCohomologyMap ℚ n p.hom b =
      relativeCohomologyMap ℚ n (b6m_subspacePairMap X e.source Sᶜ) a := by
    change C.toLinearEquiv (C.toLinearEquiv.symm _) = _
    exact C.toLinearEquiv.apply_symm_apply _
  refine ⟨b, ?_⟩
  intro W hW
  let g := neighborhoodSupportInclusionPairMap hW S
  calc
    _ = relativeCohomologyMap ℚ n g
        (relativeCohomologyMap ℚ n (b6m_subspacePairMap X e.source Sᶜ) a) := by
      exact LinearMap.congr_fun
        (relativeCohomologyMap_comp ℚ n g (b6m_subspacePairMap X e.source Sᶜ)) a
    _ = relativeCohomologyMap ℚ n g (relativeCohomologyMap ℚ n p.hom b) :=
      congrArg (relativeCohomologyMap ℚ n g) hb.symm
    _ = _ := by
      exact (LinearMap.congr_fun (relativeCohomologyMap_comp ℚ n g p.hom) b).symm

end HodgeLean.Foundations.QuotientDuality
