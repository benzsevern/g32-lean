import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLocalThom
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSectionLocalization

/-! # The actual normal section's local and global supported pullbacks -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual open kernel-chart inclusion retains the zero-section support. -/
def normalKernelChartInclusionPair (k : ℕ) :
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
      {v | v.1.1.2 = 0}ᶜ ⟶
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k))
      {v | v.1.2 = 0}ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (fun _ h => h)

/-- The actual first projective chart retains the distinguished point support. -/
def normalProjectiveChartPair (k : ℕ) :
    puncturedPair ℂ k ⟶
    TopPair.ofSubset (X := TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ))))
      ({normalProjectiveBase k} : Set _)ᶜ :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨normalProjectiveChart k, continuous_normalProjectiveChart k⟩)
    (by
      intro z hz
      change normalProjectiveChart k z ≠ normalProjectiveBase k
      intro h
      exact hz ((normalProjectiveChart_eq_base_iff k z).mp h))

#print axioms normalKernelChartInclusionPair
#print axioms normalProjectiveChartPair
/-- Restricting the actual global section to its base chart gives the actual local section pair map. -/
theorem normalKernelSection_chart_square (k : ℕ) :
    normalProjectiveChartPair k ≫ projectiveNormalSectionPairMap k =
      normalKernelLocalSectionPairMap k ≫ normalKernelChartInclusionPair k := by
  have hf : TopPair.Hom.fst (normalProjectiveChartPair k ≫ projectiveNormalSectionPairMap k) =
      TopPair.Hom.fst (normalKernelLocalSectionPairMap k ≫ normalKernelChartInclusionPair k) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact (normalKernelLocalSectionPairMap_apply k z).symm
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply (TopPair.isEmbedding_map _).injective
    change (TopPair.Hom.snd (normalProjectiveChartPair k ≫ projectiveNormalSectionPairMap k) ≫
        (TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k))
          {v | v.1.2 = 0}ᶜ).map) x =
      (TopPair.Hom.snd (normalKernelLocalSectionPairMap k ≫ normalKernelChartInclusionPair k) ≫
        (TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k))
          {v | v.1.2 = 0}ᶜ).map) x
    rw [TopPair.Hom.w, TopPair.Hom.w, hf]
  · exact hf

#print axioms normalKernelSection_chart_square
/-- The actual supported section pullback commutes with restriction to the specified kernel chart. -/
theorem normalKernelSection_chart_cohomology (k n : ℕ)
    (α : CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
      {v | v.1.2 = 0} n) :
    relativeCohomologyMap ℚ n (normalProjectiveChartPair k)
      (relativeCohomologyMap ℚ n (projectiveNormalSectionPairMap k) α) =
    relativeCohomologyMap ℚ n (normalKernelLocalSectionPairMap k)
      (relativeCohomologyMap ℚ n (normalKernelChartInclusionPair k) α) := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    normalKernelSection_chart_square, relativeCohomologyMap_comp, LinearMap.comp_apply]

#print axioms normalKernelSection_chart_cohomology
/-- Restriction of a global zero-section pullback is computed by the same local supported section map. -/
theorem projectiveNormalZeroSection_chart_localization (k n : ℕ)
    (α : CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
      {v | v.1.2 = 0} n) :
    cohomologyMap ℚ n (TopPair.Hom.fst (normalProjectiveChartPair k))
      (cohomologyMap ℚ n (TopCat.ofHom (projectiveNormalZeroSection k))
        (forgetSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
          {v | v.1.2 = 0} n α)) =
    relativeCohomologyToAbsolute ℚ (puncturedPair ℂ k) n
      (relativeCohomologyMap ℚ n (normalKernelLocalSectionPairMap k)
        (relativeCohomologyMap ℚ n (normalKernelChartInclusionPair k) α)) := by
  rw [projectiveNormalZeroSection_localization,
    ← RelativeTrace.forget_naturality, normalKernelSection_chart_cohomology]

#print axioms projectiveNormalZeroSection_chart_localization
end HodgeLean.Foundations.Program.G32Native.EulerModel
