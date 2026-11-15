import HodgeLean.Foundations.Program.G32Native.KernelThomModelCoordinates

/-! # Detection by the original entire model charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Bundle Opposite
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native
open EulerModel

/-- Product parameters identify the literal supported chart pair. -/
def kernelChartPairIso (k : ℕ) (j : Fin (k + 1)) :
    i1_productNormalPair (Fin k → ℂ) k ≅
      neighborhoodSupportComplementPair
        (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} := by
  let e := normalCoordinateKernelChart k j
  let h : ((Fin k → ℂ) × (Fin k → ℂ)) ≃ₜ (normalKernelCoclassChartOpen k j) := {
    toFun := fun za => ⟨normalCoordinateKernelParam k j za, by
      rw [normalKernelCoclassChartOpen, Opens.mem_mk, normalCoordinateKernelChart_source]
      exact Set.mem_range_self za⟩
    invFun := fun v => e v.1
    left_inv := normalCoordinateKernelChart_param k j
    right_inv := fun v => Subtype.ext (e.left_inv v.2)
    continuous_toFun := (isOpenEmbedding_normalCoordinateKernelParam k j).continuous.subtype_mk (by
      intro za
      rw [normalKernelCoclassChartOpen, Opens.mem_mk, normalCoordinateKernelChart_source]
      exact Set.mem_range_self za)
    continuous_invFun := e.continuousOn.domRestrict }
  exact TopPair.isoOfSubset h (fun za =>
    not_congr (normalCoordinateKernelChart_vector_zero_iff k j za))

/-- Entire chart inclusion into the original support pair. -/
def kernelChartInclusion (k : ℕ) (j : Fin (k + 1)) :
    neighborhoodSupportComplementPair
      (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} ⟶
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  neighborhoodSupportInclusionPairMap
    (show (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) ⊆
      Set.univ from Set.subset_univ _) {w | w.1.2 = 0} ≫
    (normalKernelUnivSupportPairIso k).hom

/-- Model product parameters factor through the actual entire chart. -/
theorem kernelChartPairIso_inclusion (k : ℕ) (j : Fin (k + 1)) :
    (kernelChartPairIso k j).hom ≫ kernelChartInclusion k j = kernelChartPairParam k j := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- The model's product parameters retain its specified complex normalization. -/
theorem kernelChartPairParam_normalization (k : ℕ) (j : Fin (k + 1)) :
    relativeCohomologyMap ℚ (2 * k) (kernelChartPairParam k j)
      (normalKernelGlobalThomClass k) =
    relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection (Fin k → ℂ) k)
      (normalizedPointCoclass k) := by
  rw [← kernelChartPairIso_inclusion, relativeCohomologyMap_comp, LinearMap.comp_apply]
  have hi : kernelChartInclusion k j ≫ (normalKernelUnivSupportPairIso k).inv =
      neighborhoodSupportInclusionPairMap
        (show (normalKernelCoclassChartOpen k j : Set (ProjectiveNormalTotalSpace k)) ⊆
          Set.univ from Set.subset_univ _) {w | w.1.2 = 0} := by
    unfold kernelChartInclusion
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc : relativeCohomologyMap ℚ (2 * k) (kernelChartInclusion k j)
      (normalKernelGlobalThomClass k) =
      chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
        (normalKernelCoclassChartOpen k j) (le_refl _) := by
    unfold normalKernelGlobalThomClass
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hi]
    exact normalKernelGlobalRelativeThomClass_restrict k j
  rw [hc]
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  apply congrArg (fun f => relativeCohomologyMap ℚ (2 * k) f (normalizedPointCoclass k))
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    exact Subtype.ext (congrArg Prod.snd (normalCoordinateKernelChart_param k j v.1))
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    exact congrArg Prod.snd (normalCoordinateKernelChart_param k j v)

/-- Restrictions to all original product charts detect supported model coclasses. -/
theorem kernelChartPairParam_ext (k : ℕ)
    (u v : CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k))
    (h : ∀ j : Fin (k + 1),
      relativeCohomologyMap ℚ (2 * k) (kernelChartPairParam k j) u =
      relativeCohomologyMap ℚ (2 * k) (kernelChartPairParam k j) v) : u = v := by
  apply i1_relativeCohomologyMap_iso_injective (normalKernelUnivSupportPairIso k) (2 * k)
  letI := normalKernelRelativeCohomologyToSheaf_isIso k ⊤
  apply (asIso ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
    {w | w.1.2 = 0} (2 * k)).app (op ⊤))).addCommGroupIsoToAddEquiv.injective
  apply TopCat.Presheaf.section_ext
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k))
  intro x hx
  obtain ⟨j, hj⟩ := normalCoordinateKernelChart_cover k x
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} (2 * k)
    (show normalKernelCoclassChartOpen k j ≤ ⊤ from le_top)
    (show normalKernelCoclassChartOpen k j ≤ ⊤ from le_top) x hj
  apply i1_relativeCohomologyMap_iso_injective (kernelChartPairIso k j) (2 * k)
  have hj := h j
  rw [← kernelChartPairIso_inclusion] at hj
  simp only [kernelChartInclusion, relativeCohomologyMap_comp, LinearMap.comp_apply] at hj
  convert hj using 1

#print axioms kernelChartPairParam_ext
#print axioms kernelChartPairParam_normalization
end HodgeLean.Foundations.Program.G32Native
