import HodgeLean.Foundations.BundleThom.ChartLocalOrientationHelpers

/-! # Actual pair maps from product coordinates into supplied bundle charts

The source retains a continuous base parametrization and the exact punctured normal support.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B T : Type} [TopologicalSpace B] [TopologicalSpace T] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ] [e'.IsLinear ℂ]

/-- The actual inverse coordinates of one chart map a product complement pair into another supplied chart.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, overlap comparisons. -/
def i1_chartProductPairMap (f : T → B) (hf : Continuous f)
    (he : ∀ t, f t ∈ e.baseSet) (he' : ∀ t, f t ∈ e'.baseSet) :
    i1_productNormalPair T k ⟶ i1_chartPair k E e' :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun p => ⟨⟨f p.1, e.symm (f p.1) p.2⟩, e'.mem_source.mpr (he' p.1)⟩,
      (e.continuousOn_symm.comp_continuous
        ((hf.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨he p.1, trivial⟩)).subtype_mk _⟩) (by
      intro p hp hz
      apply hp
      apply (e.linearEquivAt ℂ (f p.1) (he p.1)).symm.injective
      exact hz.trans (map_zero _).symm)

/-- The actual source chart's normal coordinates undo its parametrized inverse pair map.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, normal coordinate identity. -/
theorem i1_chartProductPairMap_comp_ownNormal (f : T → B) (hf : Continuous f)
    (he : ∀ t, f t ∈ e.baseSet) :
    i1_chartProductPairMap k E e e f hf he he ≫ i1_chartNormal k E e =
      i1_productNormalProjection T k := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congrArg Prod.snd (e.apply_mk_symm (he p.1.1) p.1.2)
  · apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Prod.snd (e.apply_mk_symm (he p.1) p.2)

/-- Actual product parametrization pulls the source chart orientation back to the fixed normal coclass pullback.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local Thom orientation. -/
theorem i1_chartOrientation_productPullback (f : T → B) (hf : Continuous f)
    (he : ∀ t, f t ∈ e.baseSet) :
    relativeCohomologyMap ℚ (2 * k) (i1_chartProductPairMap k E e e f hf he he)
      (i1_chartOrientation k E e) =
      relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection T k)
        (HodgeLean.RealDefs.normalizedPointCoclass k) := by
  rw [i1_chartOrientation, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartProductPairMap_comp_ownNormal]

end HodgeLean.Foundations.BundleThom
