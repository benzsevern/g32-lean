import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelThomSupport
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLeadingIdentity

/-! # The same global and original leading-chart kernel Thom coclass -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every vector in the original leading kernel domain lies in the actual leading atlas source. -/
theorem normalKernelLeading_mem_chart (k : ℕ) (v : NormalKernelChartDomain k) :
    v.1 ∈ normalKernelCoclassChartOpen k 0 := by
  change v.1 ∈ (normalCoordinateKernelChart k 0).source
  rw [normalCoordinateKernelChart_source, normalCoordinateKernelParam_range]
  change normalPermutationBaseHomeomorph k (Equiv.swap 0 0) v.1.1.1 ∈
    Set.range (normalProjectiveChart k)
  rw [normalPermutationBaseHomeomorph_swap_zero]
  exact v.2

#print axioms normalKernelLeading_mem_chart
/-- The original leading-domain inclusion into the actual leading chart retains its literal zero-vector complement. -/
def normalKernelLeadingChartOpenPair (k : ℕ) :
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k)) {v | v.1.1.2 = 0}ᶜ ⟶
      neighborhoodSupportComplementPair
        (normalKernelCoclassChartOpen k 0 : Set (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun v => ⟨v.1, normalKernelLeading_mem_chart k v⟩,
      continuous_subtype_val.subtype_mk _⟩) (fun _ h => h)

#print axioms normalKernelLeadingChartOpenPair
/-- The actual leading atlas normal projection is precisely the original normalized kernel fibre pair map. -/
theorem normalKernelLeadingChartOpenPair_projection (k : ℕ) :
    normalKernelLeadingChartOpenPair k ≫
      chartNormalProjectionPair (Fin k → ℂ) k (normalCoordinateKernelChart k 0)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support k 0)
        (normalKernelCoclassChartOpen k 0) (le_refl _) = normalKernelFibrePairMap k := by
  have hc (v : NormalKernelChartDomain k) :
      (normalCoordinateKernelChart k 0 v.1).2 = v.1.1.2.2 := by
    rw [normalCoordinateKernelChart_apply k 0 v.1 (normalKernelLeading_mem_chart k v)]
    exact congrArg Prod.snd (normalCoordinatePermutation_swap_zero k v.1.1.2)
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    apply Subtype.ext
    exact hc v.1
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    exact hc v

#print axioms normalKernelLeadingChartOpenPair_projection
/-- Both actual leading inclusions retain the same original vector in the all-space supported neighborhood pair. -/
theorem normalKernelLeadingChartOpenPair_square (k : ℕ) :
    normalKernelChartInclusionPair k ≫ (normalKernelUnivSupportPairIso k).inv =
      normalKernelLeadingChartOpenPair k ≫
        neighborhoodSupportInclusionPairMap
          (show (normalKernelCoclassChartOpen k 0 : Set (ProjectiveNormalTotalSpace k)) ⊆
            Set.univ from Set.subset_univ _) {w | w.1.2 = 0} := rfl

#print axioms normalKernelLeadingChartOpenPair_square
/-- The original global Thom coclass restricts to precisely the same original leading-chart normalized fibre coclass. -/
theorem normalKernelGlobalThomClass_chart (k : ℕ) :
    relativeCohomologyMap ℚ (2 * k) (normalKernelChartInclusionPair k)
      (normalKernelGlobalThomClass k) = normalKernelLocalThomClass k := by
  unfold normalKernelGlobalThomClass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    normalKernelLeadingChartOpenPair_square, relativeCohomologyMap_comp,
    LinearMap.comp_apply, normalKernelGlobalRelativeThomClass_restrict]
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    normalKernelLeadingChartOpenPair_projection]
  rfl

#print axioms normalKernelGlobalThomClass_chart
end HodgeLean.Foundations.Program.G32Native.EulerModel
