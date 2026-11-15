import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelThomSupport

/-! # Normalization of the actual model class on every ordered coordinate chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Inclusion of an entire original kernel coordinate chart into the actual zero-complement pair. -/
def coefficientModelChartInclusion (k : ℕ) (j : Fin (k + 1)) :
    neighborhoodSupportComplementPair
      (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} ⟶
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  neighborhoodSupportInclusionPairMap
    (show (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) ⊆
      Set.univ from Set.subset_univ _) {w | w.1.2 = 0} ≫
    (normalKernelUnivSupportPairIso k).hom

/-- The actual model class has the specified complex normalization on every entire original chart. -/
theorem coefficientModelChart_normalization (k : ℕ) (j : Fin (k + 1)) :
    relativeCohomologyMap ℚ (2 * k) (coefficientModelChartInclusion k j)
      (normalKernelGlobalThomClass k) =
    chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
      {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
      (normalKernelCoclassChartOpen k j) (le_refl _) := by
  unfold normalKernelGlobalThomClass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  have hsquare : coefficientModelChartInclusion k j ≫ (normalKernelUnivSupportPairIso k).inv =
      neighborhoodSupportInclusionPairMap
        (show (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) ⊆
          Set.univ from Set.subset_univ _) {w | w.1.2 = 0} := by
    unfold coefficientModelChartInclusion
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hsquare]
  exact normalKernelGlobalRelativeThomClass_restrict k j

end HodgeLean.Foundations.Program.G32Native
