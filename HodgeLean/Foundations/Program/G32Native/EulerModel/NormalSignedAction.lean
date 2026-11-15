import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalConjugationCohomology
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalScalarInvariance
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalChartHomotopy

/-! # The exact supported cohomology action of the signed normal section coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified signed conjugation is exactly rotated conjugation followed by the scalar `I`. -/
theorem normalChartPairMap_zero_factorization (k : ℕ) :
    normalChartPairMap k 0 = rotatedNormalConjugationPair k ≫ normalScalarIPair k := by
  have hf : TopPair.Hom.fst (normalChartPairMap k 0) =
      TopPair.Hom.fst (rotatedNormalConjugationPair k ≫ normalScalarIPair k) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    funext j
    change normalChartVector k 0 z j =
      (TopPair.Hom.fst (normalScalarIPair k))
        ((TopPair.Hom.fst (rotatedNormalConjugationPair k)) z) j
    rw [(normalChartVector_endpoints k z).1, normalScalarIPair_apply,
      rotatedNormalConjugationPair_apply]
    simp [← mul_assoc]
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply (TopPair.isEmbedding_map (puncturedPair ℂ k)).injective
    change (TopPair.Hom.snd (normalChartPairMap k 0) ≫ (puncturedPair ℂ k).map) x =
      (TopPair.Hom.snd (rotatedNormalConjugationPair k ≫ normalScalarIPair k) ≫
        (puncturedPair ℂ k).map) x
    rw [TopPair.Hom.w, TopPair.Hom.w, hf]
  · exact hf

#print axioms normalChartPairMap_zero_factorization

/-- The signed conjugation has the exact top supported action in any identified top degree. -/
theorem normalChartPairMap_zero_cohomology (k n : ℕ) (hn : n = k * 2)
    (α : RelativeCohomology ℚ (puncturedPair ℂ k) n) :
    relativeCohomologyMap ℚ n (normalChartPairMap k 0) α = (-1 : ℚ) ^ k • α := by
  subst n
  rw [normalChartPairMap_zero_factorization, relativeCohomologyMap_comp,
    LinearMap.comp_apply, normalScalarIPair_cohomology, rotatedNormalConjugationPair_cohomology]

#print axioms normalChartPairMap_zero_cohomology

/-- The actual Hermitian section chart has the exact signed action on top supported cohomology. -/
theorem normalChartPairMap_one_cohomology (k : ℕ)
    (α : RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k)) :
    relativeCohomologyMap ℚ (2 * k) (normalChartPairMap k 1) α = (-1 : ℚ) ^ k • α := by
  rw [← normalChartPairMap_cohomology_eq]
  exact normalChartPairMap_zero_cohomology k (2 * k) (by omega) α

#print axioms normalChartPairMap_one_cohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
