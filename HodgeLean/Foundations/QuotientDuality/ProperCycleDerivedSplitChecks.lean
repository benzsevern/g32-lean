import HodgeLean.Foundations.QuotientDuality.ProperCycleShiftedDerivedSupport
import HodgeLean.Foundations.QuotientDuality.ProperCyclePositiveSupportChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonOrientation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

/-! # Independent shifted supported-section and original cap normalization checks
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSplitChecks

private abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private instance derivedSplitPointUnique : Unique (ComplexPoint point) where
  default := 𝟙 point
  uniq f := by
    apply Over.OverMorphism.ext
    simpa using f.w
private instance derivedSplitPointIntegral : IsIntegral point.left :=
  inferInstanceAs (IsIntegral (Spec ↧ℂ))
private instance derivedSplitCoordinatesUnique : Unique (Fin 0 → ℂ) :=
  { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
private abbrev T := TopCat.of (ComplexPoint point)
private def S : Closeds T := ⊤
private abbrev P := neighborhoodSupportComplementPair (Set.univ : Set T) (S : Set T)
private instance derivedSplitNeighborhoodUnique : Unique P.fst where
  default := ⟨𝟙 point, Set.mem_univ _⟩
  uniq v := Subtype.ext (Subsingleton.elim _ _)
private def x : P.fst := default
private def chart : OpenPartialHomeomorph P.fst (Fin 0 → ℂ) :=
  (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
private lemma pair_eq : P = pointComplementPair x := by
  change TopPair.ofSubset (X := TopCat.of (Set.univ : Set T))
    {z | z.val ∉ (S : Set T)} =
    TopPair.ofSubset ({x} : Set P.fst)ᶜ
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact iff_of_false (fun hz => hz (Set.mem_univ _))
    (fun hz => hz (Subsingleton.elim _ _))
private def pointPairEquiv :=
  ((relativeHomologyFunctor ℚ 0).mapIso (eqToIso pair_eq)).toLinearEquiv
private def z : RelativeHomology ℚ P 0 :=
  pointPairEquiv.symm (localClassOfChart 0 chart x (by trivial))
private lemma z_ne : z ≠ 0 := by
  intro hz
  have h := congrArg pointPairEquiv hz
  change pointPairEquiv (pointPairEquiv.symm _) = pointPairEquiv 0 at h
  rw [pointPairEquiv.apply_symm_apply, map_zero] at h
  exact localClassOfChart_ne_zero 0 chart x (by trivial) h
private def a : RelativeCohomology ℚ P 0 := normalizedRelativeCoclass z z_ne
private lemma a_eval : relativeCohomologyEquivDualHomology ℚ P 0 a z = 1 :=
  normalizedRelativeCoclass_pairing_self z z_ne

private def relativeComparison :
    TopCat.Sheaf.supportH T S (TopCat.Sheaf.const T (AddCommGrpCat.of ℚ)) 0 ≃+
      RelativeCohomology ℚ P 0 :=
  (ComplexPoint.rationalSupportAddEquivSupportedInjectiveHomology point S 0).trans
    (ComplexPoint.complexSupportInjectiveSectionCohomologyEquiv point S ⊤ 0)
private instance derivedSplitSheafDerived : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{0} T) :=
  HasDerivedCategory.standard _
private instance derivedSplitGroupDerived : HasDerivedCategory AddCommGrpCat.{0} :=
  HasDerivedCategory.standard _
private def relativeIso :
    AddCommGrpCat.of (TopCat.Sheaf.supportH T S
      (TopCat.Sheaf.const T (AddCommGrpCat.of ℚ)) 0) ≅
    AddCommGrpCat.of (RelativeCohomology ℚ P 0) := relativeComparison.toAddCommGrpIso
private def shiftedSource : AddCommGrpCat.{0} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (-4)).obj
    ((TopCat.Sheaf.derivedClosedSupportSections T S).obj
      ((DerivedCategory.Plus.singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} T) (-4)).obj
        (TopCat.Sheaf.const T (AddCommGrpCat.of ℚ))))
private opaque shiftedComparison : shiftedSource ≅ AddCommGrpCat.of (RelativeCohomology ℚ P 0) :=
  properCycle_shifted_derived_support_sheaf_iso T S 4 4 0 (by omega) ≪≫ relativeIso
private def d : shiftedSource := shiftedComparison.inv a
private lemma iso_apply_inv {A B : AddCommGrpCat.{0}} (e : A ≅ B) (b : B) :
    e.hom (e.inv b) = b := ConcreteCategory.congr_hom e.inv_hom_id b
private lemma d_image : shiftedComparison.hom d = a :=
  iso_apply_inv shiftedComparison a

/-- On the projective point, actual degree minus four derived supported sections of the rational object in degree minus four recover the normalized relative point coclass with evaluation one.
Source: Iversen, Cohomology of Sheaves, III and IX; properCycle_shifted_derived_support_sheaf_iso; complexSupportInjectiveSectionCohomologyEquiv.
HC no distance; AV milestone no distance. -/
theorem middle_support_identification_shifted_example :
    relativeCohomologyEquivDualHomology ℚ P 0 (shiftedComparison.hom d) z = 1 := by
  rw [d_image]
  exact a_eval

example : relativeCohomologyEquivDualHomology ℚ P 0
    (shiftedComparison.hom d) z = 1 := middle_support_identification_shifted_example

/-- Replacing the actual shifted identification by zero loses the normalized point value.
Source: Iversen, Cohomology of Sheaves, III and IX.
HC no distance; AV milestone no distance. -/
theorem middle_support_identification_zero_falsification :
    (0 : RelativeCohomology ℚ P 0) ≠ shiftedComparison.hom d := by
  intro h
  have hval := middle_support_identification_shifted_example
  rw [← h, map_zero, LinearMap.zero_apply] at hval
  exact zero_ne_one hval

example : (0 : RelativeCohomology ℚ P 0) ≠ shiftedComparison.hom d :=
  middle_support_identification_zero_falsification

/-- Reversing the shifted comparison loses the positive point normalization.
Source: Iversen, Cohomology of Sheaves, III and IX; normalizedRelativeCoclass_pairing_self.
HC no distance; AV milestone no distance. -/
theorem middle_support_identification_sign_falsification :
    -shiftedComparison.hom d ≠ shiftedComparison.hom d := by
  intro h
  have hv := congrArg (fun b => relativeCohomologyEquivDualHomology ℚ P 0 b z) h
  rw [map_neg, LinearMap.neg_apply, middle_support_identification_shifted_example] at hv
  norm_num at hv

example : -shiftedComparison.hom d ≠ shiftedComparison.hom d :=
  middle_support_identification_sign_falsification

/-- Doubling the shifted comparison changes the point coefficient from one to two.
Source: Iversen, Cohomology of Sheaves, III and IX; normalizedRelativeCoclass_pairing_self.
HC no distance; AV milestone no distance. -/
theorem middle_support_identification_double_falsification :
    shiftedComparison.hom d + shiftedComparison.hom d ≠ shiftedComparison.hom d := by
  intro h
  have hv := congrArg (fun b => relativeCohomologyEquivDualHomology ℚ P 0 b z) h
  rw [map_add, LinearMap.add_apply, middle_support_identification_shifted_example] at hv
  norm_num at hv

example : shiftedComparison.hom d + shiftedComparison.hom d ≠ shiftedComparison.hom d :=
  middle_support_identification_double_falsification

/- Positive-degree original collar cap recovery and its zero and sign mutations.
Source: Bredon, Sheaf Theory, V.9; ProperCyclePositiveSupportChecks.
HC no distance; AV milestone no distance. -/
example := ProperCyclePositiveSupportChecks.global_support_factorization_supported_example
example := ProperCyclePositiveSupportChecks.global_support_factorization_supported_zero_falsification
example := ProperCyclePositiveSupportChecks.global_support_factorization_supported_sign_falsification

end HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSplitChecks
