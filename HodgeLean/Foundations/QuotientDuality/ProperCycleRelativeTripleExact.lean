import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriple
import HodgeLean.Foundations.QuotientDuality.ProperCycleDualExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence

/-! # Exactness on the literal relative rational cohomology of a triple -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A relative rational class vanishing on the inner pair comes from the outer quotient pair, with the literal original cohomology maps.
Source: Hatcher, Algebraic Topology, section 3.1, exact cohomology sequence of a triple.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triple_cohomology_lift
    (X : TopCat) (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset A) n)
    (ha : relativeCohomologyMap ℚ n
      (properCycle_relative_triple_first X A B hAB) a = 0) :
    ∃ b : RelativeCohomology ℚ (TopPair.ofSubset B) n,
      relativeCohomologyMap ℚ n (properCycle_relative_triple_second X A B hAB) b = a := by
  have hex := (properCycle_relative_triple_sequence_shortExact X A B hAB).homology_exact₂ n
  have hfg := hex.moduleCat_range_eq_ker
  change LinearMap.range (HomologicalComplex.homologyMap
    (properCycle_relative_triple_sequence X A B hAB).f n).hom =
    LinearMap.ker (HomologicalComplex.homologyMap
    (properCycle_relative_triple_sequence X A B hAB).g n).hom at hfg
  rw [properCycle_relative_triple_first_map, properCycle_relative_triple_second_map] at hfg
  let f := relativeHomologyMap ℚ n (properCycle_relative_triple_first X A B hAB)
  let g := relativeHomologyMap ℚ n (properCycle_relative_triple_second X A B hAB)
  have hfg' : LinearMap.range f = LinearMap.ker g := hfg
  let a' := relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) n a
  have ha' : ∀ u, a' (f u) = 0 := by
    intro u
    change relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) n a
      (relativeHomologyMap ℚ n (properCycle_relative_triple_first X A B hAB) u) = 0
    rw [← relativeCohomologyEquivDualHomology_relativeCohomologyMap, ha, map_zero]
    rfl
  obtain ⟨b', hb'⟩ := properCycle_dual_exact_lift f g hfg' a' ha'
  let b := (relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n).symm b'
  refine ⟨b, (relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset A) n).injective ?_⟩
  ext z
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  change (relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset B) n) b (g z) = a' z
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun l : Module.Dual ℚ (RelativeHomology ℚ (TopPair.ofSubset A) n) => l z) hb'

/-- Exactness retains a class on the smaller support whenever its literal restriction to the complement vanishes.
Source: Hatcher, Algebraic Topology, section 3.1, the exact sequence for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_supported_descent_of_complement_zero
    (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (a : CohomologyWithSupport ℚ X T n)
    (ha : relativeCohomologyMap ℚ n
      (properCycle_relative_triple_first X Tᶜ Sᶜ (Set.compl_subset_compl.mpr hST)) a = 0) :
    ∃ b : CohomologyWithSupport ℚ X S n, enlargeSupport ℚ X hST n b = a := by
  obtain ⟨b, hb⟩ := properCycle_relative_triple_cohomology_lift X Tᶜ Sᶜ
    (Set.compl_subset_compl.mpr hST) n a ha
  refine ⟨b, ?_⟩
  have hm : properCycle_relative_triple_second X Tᶜ Sᶜ
      (Set.compl_subset_compl.mpr hST) = supportInclusionPairMap X hST := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  simpa only [hm, enlargeSupport] using hb

end HodgeLean.Foundations.QuotientDuality
