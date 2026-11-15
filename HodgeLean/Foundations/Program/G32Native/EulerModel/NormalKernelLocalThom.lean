import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelChartPair
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointCoclass

/-! # The specified fibre coclass in the actual kernel chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normal fibre coordinates as a map of pairs retaining the zero section. -/
def normalKernelFibrePairMap (k : ℕ) :
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
      {v | v.1.1.2 = 0}ᶜ ⟶ puncturedPair ℂ k :=
  (normalKernelTotalChartPairIso k).inv ≫
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
      (fun _ h => h)

/-- The actual local fibre coclass, with the specified complex normalization. -/
def normalKernelLocalThomClass (k : ℕ) :
    RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
        {v | v.1.1.2 = 0}ᶜ) (2 * k) :=
  relativeCohomologyMap ℚ (2 * k) (normalKernelFibrePairMap k)
    (normalizedPointCoclass k)

#print axioms normalKernelFibrePairMap
#print axioms normalKernelLocalThomClass
/-- The global normal section in its actual total-space chart, retaining the punctured subspaces. -/
def normalKernelLocalSectionPairMap (k : ℕ) :
    puncturedPair ℂ k ⟶
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
      {v | v.1.1.2 = 0}ᶜ :=
  TopPair.ofSubsetHom (B := {za : (Fin k → ℂ) × (Fin k → ℂ) | za.2 = 0}ᶜ)
    (TopCat.ofHom ⟨fun z => (z, normalChartVector k 1 z),
      continuous_id.prodMk ((continuous_normalChartVector k).comp
        (continuous_const.prodMk continuous_id))⟩)
    (by
      intro z hz
      change normalChartVector k 1 z ≠ 0
      intro h
      exact hz ((normalChartVector_zero_iff k 1 z).mp h)) ≫
      (normalKernelTotalChartPairIso k).hom

#print axioms normalKernelLocalSectionPairMap
/-- The local pair map is the specified global section, including its actual kernel vector. -/
theorem normalKernelLocalSectionPairMap_apply (k : ℕ) (z : Fin k → ℂ) :
    ((TopPair.Hom.fst (normalKernelLocalSectionPairMap k)) z).1 =
      projectiveNormalSectionMap k (normalProjectiveChart k z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (normalKernelChart k z (normalChartVector k 1 z)).1 =
      projectiveNormalSectionVector k (normalProjectiveChart k z)
    rw [(normalChartVector_endpoints k z).2]
    apply normalKernelChart_vector_tail
    rw [← projectiveNormalKernel_chart]
    exact projectiveNormalSectionVector_mem k (normalProjectiveChart k z)

#print axioms normalKernelLocalSectionPairMap_apply
/-- Fibre projection of the actual section pair map is exactly the previously normalized chart map. -/
theorem normalKernelLocalSection_fibre (k : ℕ) :
    normalKernelLocalSectionPairMap k ≫ normalKernelFibrePairMap k =
      normalChartPairMap k 1 := by
  simp only [normalKernelLocalSectionPairMap, normalKernelFibrePairMap,
    Category.assoc, Iso.hom_inv_id_assoc]
  rfl

#print axioms normalKernelLocalSection_fibre
/-- Pullback of the specified local fibre coclass by the actual normal section has its exact signed normalization. -/
theorem normalKernelLocalThomClass_section (k : ℕ) :
    relativeCohomologyMap ℚ (2 * k) (normalKernelLocalSectionPairMap k)
      (normalKernelLocalThomClass k) =
        (-1 : ℚ) ^ k • normalizedPointCoclass k := by
  unfold normalKernelLocalThomClass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    normalKernelLocalSection_fibre]
  exact normal_section_normalizedPointCoclass k

#print axioms normalKernelLocalThomClass_section
/-- The actual fibre inclusion with its specified complex-linear coordinates at a chart base point. -/
def normalKernelLocalFibreInclusion (k : ℕ) (z : Fin k → ℂ) :
    puncturedPair ℂ k ⟶
    TopPair.ofSubset (X := TopCat.of (NormalKernelChartDomain k))
      {v | v.1.1.2 = 0}ᶜ :=
  TopPair.ofSubsetHom
    (A := ({0} : Set (Fin k → ℂ))ᶜ)
    (B := {za : (Fin k → ℂ) × (Fin k → ℂ) | za.2 = 0}ᶜ)
    (TopCat.ofHom ⟨fun a => (z, a), continuous_const.prodMk continuous_id⟩)
    (fun _ h => h) ≫ (normalKernelTotalChartPairIso k).hom

#print axioms normalKernelLocalFibreInclusion
/-- Every actual fibre in the specified chart has the same normalized point coclass. -/
theorem normalKernelLocalThomClass_fibre (k : ℕ) (z : Fin k → ℂ) :
    relativeCohomologyMap ℚ (2 * k) (normalKernelLocalFibreInclusion k z)
      (normalKernelLocalThomClass k) = normalizedPointCoclass k := by
  have hf : normalKernelLocalFibreInclusion k z ≫ normalKernelFibrePairMap k =
      𝟙 (puncturedPair ℂ k) := by
    simp only [normalKernelLocalFibreInclusion, normalKernelFibrePairMap,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  unfold normalKernelLocalThomClass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hf,
    relativeCohomologyMap_id, LinearMap.id_apply]

#print axioms normalKernelLocalThomClass_fibre
end HodgeLean.Foundations.Program.G32Native.EulerModel
