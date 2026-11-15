import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelGlobalThom

/-! # Exact chart restrictions of the original global kernel Thom coclass -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual global supported section restricts to the same normalized normal coclass on each entire original chart. -/
theorem normalKernelCoclassSection_restrict (k : ℕ) (j : Fin (k + 1)) :
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.map
        (homOfLE (show normalKernelCoclassChartOpen k j ≤ ⊤ from le_top)).op
        (normalKernelCoclassSection k) =
      (supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
        {w | w.1.2 = 0} (2 * k)).app (op (normalKernelCoclassChartOpen k j))
        (chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
          {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
          (normalKernelCoclassChartOpen k j) (le_refl _)) := by
  apply TopCat.Presheaf.section_ext
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k))
  intro v hv
  rw [TopCat.Presheaf.Γgerm_res_apply]
  exact normalKernelCoclassSection_germ k j v hv

#print axioms normalKernelCoclassSection_restrict
/-- The global relative Thom coclass restricts exactly to the original normal-projection coclass on every specified entire kernel chart. -/
theorem normalKernelGlobalRelativeThomClass_restrict (k : ℕ) (j : Fin (k + 1)) :
    relativeCohomologyMap ℚ (2 * k)
      (neighborhoodSupportInclusionPairMap
        (show (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) ⊆
          Set.univ from Set.subset_univ _) {w | w.1.2 = 0})
      (normalKernelGlobalRelativeThomClass k) =
    chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
      {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
      (normalKernelCoclassChartOpen k j) (le_refl _) := by
  letI := normalKernelRelativeCohomologyToSheaf_isIso k (normalKernelCoclassChartOpen k j)
  apply (asIso ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
    {w | w.1.2 = 0} (2 * k)).app (op (normalKernelCoclassChartOpen k j)))).addCommGroupIsoToAddEquiv.injective
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).naturality
      (homOfLE (show normalKernelCoclassChartOpen k j ≤ ⊤ from le_top)).op)
    (normalKernelGlobalRelativeThomClass k)
  change (supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).app (op (normalKernelCoclassChartOpen k j)) _ =
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.map
      (homOfLE (show normalKernelCoclassChartOpen k j ≤ ⊤ from le_top)).op
      ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
        {w | w.1.2 = 0} (2 * k)).app (op ⊤) (normalKernelGlobalRelativeThomClass k)) at h
  rw [normalKernelGlobalRelativeThomClass_toSheaf, normalKernelCoclassSection_restrict] at h
  exact h

#print axioms normalKernelGlobalRelativeThomClass_restrict
end HodgeLean.Foundations.Program.G32Native.EulerModel
