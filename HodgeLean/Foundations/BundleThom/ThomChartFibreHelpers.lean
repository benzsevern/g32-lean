import HodgeLean.Foundations.BundleThom.ThomOrientationHelpers

/-! # Normalization on actual fibres of bundle charts

The fibre maps use the supplied complex linear trivialization and its actual inverse.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ] (b : B) (hb : b ∈ e.baseSet)

/-- Inclusion of the actual chart fibre as a map of punctured pairs in its supplied complex coordinates.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, fibre normalization. -/
def i1_chartFibreInclusion : puncturedPair ℂ k ⟶ i1_chartPair k E e :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun w => ⟨⟨b, (e.continuousLinearEquivAt ℂ b hb).symm w⟩, e.mem_source.mpr hb⟩,
      ((FiberBundle.continuous_totalSpaceMk (Fin k → ℂ) E b).comp
        (e.continuousLinearEquivAt ℂ b hb).symm.continuous).subtype_mk _⟩) (by
      intro w hw hz
      exact hw ((e.continuousLinearEquivAt ℂ b hb).symm.injective
        (hz.trans (map_zero _).symm)))

/-- Chart normal coordinates undo the actual fibre inclusion exactly as maps of pairs.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local complex coordinates. -/
theorem i1_chartFibreInclusion_comp_normal :
    i1_chartFibreInclusion k E e b hb ≫ i1_chartNormal k E e = 𝟙 (puncturedPair ℂ k) := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro w
    exact Subtype.ext ((e.continuousLinearEquivAt ℂ b hb).apply_symm_apply w.1)
  · apply ConcreteCategory.hom_ext
    intro w
    exact (e.continuousLinearEquivAt ℂ b hb).apply_symm_apply w

/-- The specified chart orientation pulls back to the prescribed complex coclass on each actual fibre.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom class normalization. -/
theorem i1_chartOrientation_fibre :
    relativeCohomologyMap ℚ (2 * k) (i1_chartFibreInclusion k E e b hb)
      (i1_chartOrientation k E e) = normalizedPointCoclass k := by
  rw [i1_chartOrientation, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    i1_chartFibreInclusion_comp_normal, relativeCohomologyMap_id, LinearMap.id_apply]

end HodgeLean.Foundations.BundleThom
