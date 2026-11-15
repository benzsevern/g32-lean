import HodgeLean.Adapters.NormalConeB4aClassPurityGlobal
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularSectionNaturality

/-! # Extension across a boundary with lower supported vanishing

Route: use the exact sequence of flasque singular cochains for nested
supports. Vanishing in two consecutive boundary degrees makes restriction
an isomorphism on section cohomology. Its natural comparison with relative
singular cohomology retains the actual neighborhood restriction map.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Vanishing on a smaller boundary support in degrees `n` and `n+1` gives
unique extension from its complement for classes on the larger support. -/
theorem a3b4a_classRelative_restriction_bijective_of_boundary_vanishing
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S B : Closeds X) (hBS : B ≤ S) (n : ℕ)
    (hzero : ∀ j ∈ ({n, n + 1} : Finset ℕ), IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) B) j)) :
    Function.Bijective (relativeCohomologyMap ℚ n
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
  have hsmall (j : ℕ) (hj : j ∈ ({n, n + 1} : Finset ℕ)) :
      IsZero (E.X₁.homology (j : ℤ)) := by
    letI := ModuleCat.subsingleton_of_isZero (hzero j hj)
    exact @AddCommGrpCat.isZero_of_subsingleton _
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X B B.isClosed ⊤ j).injective.subsingleton
  letI : Mono (HomologicalComplex.homologyMap E.g (n : ℤ)) :=
    (hE.homology_exact₂ (n : ℤ)).mono_g ((hsmall n (by simp)).eq_zero_of_src _)
  letI : Epi (HomologicalComplex.homologyMap E.g (n : ℤ)) :=
    (hE.homology_exact₃ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by simp)).epi_f
      ((hsmall (n + 1) (by simp)).eq_zero_of_tgt _)
  letI : IsIso (HomologicalComplex.homologyMap E.g (n : ℤ)) :=
    isIso_of_mono_of_epi _
  let t := TopCat.Sheaf.sectionComplexRestriction X (ComplexShape.up ℤ) L
    (homOfLE (show U ≤ ⊤ from le_top))
  have ht : E.g ≫ (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso X hVU K).hom = t :=
    TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g X hVU K
  have htH : HomologicalComplex.homologyMap E.g (n : ℤ) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso X hVU K).hom (n : ℤ) =
      HomologicalComplex.homologyMap t (n : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ht]
  letI : IsIso (HomologicalComplex.homologyMap t (n : ℤ)) := by
    rw [← htH]
    infer_instance
  have hbij := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap t (n : ℤ))
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
  exact eU.bijective.comp (hbij.comp eTop.symm.bijective)

end HodgeLean.Adapters
