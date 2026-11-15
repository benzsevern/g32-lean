import HodgeLean.Adapters.NormalConeB4aClassExtension

/-! # Actual supported restriction detection across a vanishing boundary degree
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing in the single boundary support degree makes the original supported restriction to its complement injective.
Source: TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque; supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality; Bredon, Sheaf Theory, second edition, II.10 and V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_boundary_restriction_injective
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S B : Closeds X) (hBS : B ≤ S) (n : ℕ)
    (hzero : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) B) n)) :
    Function.Injective (relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap
        (show (B.compl : Set X) ⊆ Set.univ from Set.subset_univ _) (S : Set X))) := by
  let U := B.compl
  let V := S.compl
  have hVU : V ≤ U := fun x hx hxB => hx (hBS hxB)
  let K := rationalSingularCochainComplex X
  let L := supportedRationalSingularCochainComplex X V
  let E := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex X hVU ⊤ K
  have hE := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
    X hVU ⊤ K (fun _ => inferInstance)
  have hsmall : IsZero (E.X₁.homology (n : ℤ)) := by
    letI := ModuleCat.subsingleton_of_isZero hzero
    exact @AddCommGrpCat.isZero_of_subsingleton _
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X B B.isClosed ⊤ n).injective.subsingleton
  letI : Mono (HomologicalComplex.homologyMap E.g (n : ℤ)) :=
    (hE.homology_exact₂ (n : ℤ)).mono_g (hsmall.eq_zero_of_src _)
  let t := TopCat.Sheaf.sectionComplexRestriction X (ComplexShape.up ℤ) L
    (homOfLE (show U ≤ ⊤ from le_top))
  have ht : E.g ≫ (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso X hVU K).hom = t :=
    TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g X hVU K
  have htH : HomologicalComplex.homologyMap E.g (n : ℤ) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso X hVU K).hom (n : ℤ) =
      HomologicalComplex.homologyMap t (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ht]
  letI : Mono (HomologicalComplex.homologyMap t (n : ℤ)) := by
    rw [← htH]
    infer_instance
  have hbij := AddCommGrpCat.injective_of_mono (HomologicalComplex.homologyMap t (n : ℤ))
  let eTop := supportedRationalSingularSectionCohomologyEquivSupportComplement X S S.isClosed ⊤ n
  let eU := supportedRationalSingularSectionCohomologyEquivSupportComplement X S S.isClosed U n
  have hnat : (fun z => eU (HomologicalComplex.homologyMap t (n : ℤ) (eTop.symm z))) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap
          (show (B.compl : Set X) ⊆ Set.univ from Set.subset_univ _) (S : Set X)) := by
    funext z
    exact (supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
      X S S.isClosed (homOfLE (show U ≤ ⊤ from le_top)) n (eTop.symm z)).trans
        (congrArg _ (eTop.apply_symm_apply z))
  rw [← hnat]
  exact eU.injective.comp (hbij.comp eTop.symm.injective)


end HodgeLean.Foundations.QuotientDuality
