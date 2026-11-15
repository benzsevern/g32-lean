import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupportDefs
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-!
Rational supported classes and finite weighted cycle families.
Source: Hatcher, Algebraic Topology, §3.1; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped BigOperators
namespace AlgebraicTopology.Singular.SupportedClasses

theorem relativeToAbsolute_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (n : ℕ)
    (c : RelativeCohomology ℚ Q n) :
    relativeCohomologyToAbsolute ℚ P n (relativeCohomologyMap ℚ n a c) =
      cohomologyMap ℚ n (TopPair.Hom.fst a) (relativeCohomologyToAbsolute ℚ Q n c) := by
  apply (cohomologyEquivDualHomology ℚ P.fst n).injective
  ext z
  rw [cohomologyEquivDualHomology_relativeCohomologyToAbsolute,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    cohomologyEquivDualHomology_cohomologyMap,
    cohomologyEquivDualHomology_relativeCohomologyToAbsolute]
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact congrArg (relativeCohomologyEquivDualHomology ℚ Q n c)
    (ConcreteCategory.congr_hom h z)

/-- forget enlarge.
Source: SchoenCycleC2SupportedSumHelpers.s2e_enlargeSupport_absolute.
-/
theorem forget_enlarge_aux (X : TopCat.{0}) {S T : Set X} (hST : S ⊆ T)
    (n : ℕ) (c : CohomologyWithSupport ℚ X S n) :
    forgetSupport ℚ X T n (enlargeSupport ℚ X hST n c) =
      forgetSupport ℚ X S n c := by
  have h := relativeToAbsolute_naturality (supportInclusionPairMap X hST) n c
  change relativeCohomologyToAbsolute ℚ (TopPair.ofSubset Tᶜ) n
    (enlargeSupport ℚ X hST n c) =
    cohomologyMap ℚ n (𝟙 X) (forgetSupport ℚ X S n c) at h
  rw [cohomologyMap_id] at h
  exact h

/-- forget weightedSum.
Source: SchoenCycleC2SupportedSumHelpers.s2e_weightedSupportedClass_absolute.
-/
theorem forget_weightedSum_aux {ι : Type*} [Fintype ι] (X : TopCat.{0}) (n : ℕ)
    (S : ι → Set X) (T : Set X) (a : ι → ℚ)
    (hST : ∀ i, a i ≠ 0 → S i ⊆ T)
    (c : ∀ i, CohomologyWithSupport ℚ X (S i) n) :
    forgetSupport ℚ X T n (weightedSum X n S T a hST c) =
      ∑ i, a i • forgetSupport ℚ X (S i) n (c i) := by
  classical
  unfold weightedSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : a i ≠ 0
  · simp only [dite_eq_left h, map_smul, forget_enlarge_aux]
  · simp only [not_not.mp h, ne_eq, not_true_eq_false, dite_false, zero_smul, map_zero]

/-- pullback enlarge.
Source: SchoenCycleC2LocalSupportHelpers.s2e_enlargeSupport_restrict; general continuous-map version.
-/
theorem pullback_enlarge_aux {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y}
    (hST : S ⊆ T) (n : ℕ) (c : CohomologyWithSupport ℚ Y S n) :
    cohomologyWithSupportMap ℚ n f T (enlargeSupport ℚ Y hST n c) =
      enlargeSupport ℚ X (Set.preimage_mono hST) n
        (cohomologyWithSupportMap ℚ n f S c) := by
  unfold cohomologyWithSupportMap enlargeSupport
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  rfl

/-- pullback weightedSum.
Source: SchoenCycleC2WeightedRestrictionHelpers.s2e_weightedSupportedClass_restrict_single; finite-sum naturality before local vanishing.
-/
theorem pullback_weightedSum_aux {ι : Type*} [Fintype ι] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (S : ι → Set Y) (T : Set Y) (a : ι → ℚ)
    (hST : ∀ i, a i ≠ 0 → S i ⊆ T)
    (c : ∀ i, CohomologyWithSupport ℚ Y (S i) n) :
    cohomologyWithSupportMap ℚ n f T (weightedSum Y n S T a hST c) =
      weightedSum X n (fun i => f ⁻¹' S i) (f ⁻¹' T) a
        (fun i h => Set.preimage_mono (hST i h))
        (fun i => cohomologyWithSupportMap ℚ n f (S i) (c i)) := by
  classical
  unfold weightedSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : a i ≠ 0
  · simp only [dite_eq_left h, map_smul, pullback_enlarge_aux]
  · simp only [dite_eq_right h, map_zero]


-- Zero-input instances use linearity directly.
example (X : TopCat.{0}) {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    forgetSupport ℚ X T n (enlargeSupport ℚ X h n 0) =
      forgetSupport ℚ X S n 0 := by
  rw [map_zero, map_zero, map_zero]

example (X : TopCat.{0}) (n : ℕ) (S T : Set X) (h : S ⊆ T) :
    forgetSupport ℚ X T n
      (weightedSum X n (fun _ : Unit => S) T (fun _ => 1) (fun _ _ => h)
        (fun _ => 0)) = ∑ _ : Unit, (1 : ℚ) • forgetSupport ℚ X S n 0 := by
  classical
  simp [weightedSum]

example {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y} (h : S ⊆ T) (n : ℕ) :
    cohomologyWithSupportMap ℚ n f T (enlargeSupport ℚ Y h n 0) =
      enlargeSupport ℚ X (Set.preimage_mono h) n
        (cohomologyWithSupportMap ℚ n f S 0) := by
  simp only [map_zero]

example {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (S T : Set Y) (h : S ⊆ T) :
    cohomologyWithSupportMap ℚ n f T
      (weightedSum Y n (fun _ : Unit => S) T (fun _ => 1) (fun _ _ => h)
        (fun _ => 0)) =
      weightedSum X n (fun _ : Unit => f ⁻¹' S) (f ⁻¹' T) (fun _ => 1)
        (fun _ _ => Set.preimage_mono h) (fun _ => cohomologyWithSupportMap ℚ n f S 0) := by
  classical
  simp [weightedSum]

end AlgebraicTopology.Singular.SupportedClasses
