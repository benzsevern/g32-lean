import HodgeLean.Foundations.Program.G32Native.EulerModel.LocalOrientationSwap
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.PuncturedEuclidean

/-! # Signed supported cohomology action of an actual coordinate exchange -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- An actual adjacent real coordinate exchange acts by minus one on top supported cohomology. -/
theorem orientationAdjacentSwap_relativeCohomology (d i : ℕ) (hi : i + 1 < d)
    (α : RelativeCohomology ℚ (puncturedPair ℝ d) d) :
    relativeCohomologyMap ℚ d (orientationAdjacentSwapPairMap d i hi) α = -α := by
  have hs : Submodule.span ℚ {standardLocalClass ℚ d} = ⊤ := by
    cases d with
    | zero => omega
    | succ d =>
      cases d with
      | zero => omega
      | succ n => exact span_standardLocalClass_add_two_eq_top n
  apply (relativeCohomologyEquivDualHomology ℚ (puncturedPair ℝ d) d).injective
  apply LinearMap.ext_on hs
  intro z hz
  obtain rfl := Set.mem_singleton_iff.mp hz
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    orientationAdjacentSwap_standardLocalClass]
  simp only [map_neg, LinearMap.neg_apply]

#print axioms orientationAdjacentSwap_relativeCohomology

/-- An explicit composition of the specified actual adjacent-coordinate pair maps. -/
def orientationSwapListMap (d : ℕ) :
    List {i : ℕ // i + 1 < d} → (puncturedPair ℝ d ⟶ puncturedPair ℝ d)
  | [] => 𝟙 _
  | a :: l => orientationAdjacentSwapPairMap d a.1 a.2 ≫ orientationSwapListMap d l

/-- Every specified coordinate exchange contributes its exact factor minus one. -/
theorem orientationSwapList_relativeCohomology (d : ℕ) (l : List {i : ℕ // i + 1 < d})
    (α : RelativeCohomology ℚ (puncturedPair ℝ d) d) :
    relativeCohomologyMap ℚ d (orientationSwapListMap d l) α = (-1 : ℚ) ^ l.length • α := by
  induction l with
  | nil => simp [orientationSwapListMap]
  | cons a l ih =>
    rw [orientationSwapListMap, relativeCohomologyMap_comp, LinearMap.comp_apply, ih,
      map_smul, orientationAdjacentSwap_relativeCohomology]
    simp only [List.length_cons, pow_succ, mul_smul, neg_one_smul]

#print axioms orientationSwapList_relativeCohomology

/-- The specified exchanges of consecutive real coordinates in each of the k coordinate pairs. -/
def orientationPairedSwapList (k : ℕ) : List {i : ℕ // i + 1 < k * 2} :=
  List.ofFn (fun j : Fin k => ⟨2 * j.val, by have := j.isLt; omega⟩)

/-- The actual composition of the k pair exchanges has the exact top supported action `(-1)^k`. -/
theorem orientationPairedSwaps_relativeCohomology (k : ℕ)
    (α : RelativeCohomology ℚ (puncturedPair ℝ (k * 2)) (k * 2)) :
    relativeCohomologyMap ℚ (k * 2)
        (orientationSwapListMap (k * 2) (orientationPairedSwapList k)) α =
      (-1 : ℚ) ^ k • α := by
  simpa only [orientationPairedSwapList, List.length_ofFn] using
    orientationSwapList_relativeCohomology (k * 2) (orientationPairedSwapList k) α

#print axioms orientationPairedSwaps_relativeCohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
