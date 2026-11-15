import HodgeLean.Foundations.BundleThom.FiniteChartIntersectionHelpers
import HodgeLean.Foundations.BundleThom.FiniteRelativeSmallChainHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinitePositiveCoclassHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Actual supported complex bundle coclass detection by finite chart covers

The finite domain comparison retains the supplied actual total space and every supplied chart inclusion.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Restrictions to a nonempty finite actual linear chart cover detect supported rational classes of a complex bundle.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative finite-cover detection; Bott–Tu, §6. -/
theorem i1_rankFiniteCoverCoclass_ext {B ι : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : ι → Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin k → ℂ) E, ∃ i ∈ s, z ∈ (e i).source)
    (u v : i1_supportedClass k E)
    (h : ∀ i ∈ s, relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E (e i)) u =
      relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E (e i)) v) : u = v := by
  let X := i1_totalSpace k E
  let Z := (i1_zeroSupport k E)ᶜ
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  let U := fun i => i1_singularSubsetRange X (e i).source
  let K := s.sup U
  let p := i1_relativeSmallChainComparison X Z K
  haveI : QuasiIso p := i1_finiteRelativeSmallChainComparison_quasiIso X Z
    (fun i => (e i).source) s (fun i _ => (e i).open_source) hcover
  apply (i1_chainDualPullback_bijective (2 * k) p).1
  apply i1_relativeSubcomplexFinsetPositiveCoclass_ext (TopCat.toSSet.obj X)
    (i1_singularSubsetRange X Z) (2 * k) (by omega) U s hs
  · intro t ht m hm
    exact i1_chartFinsetRangeIntersectionHomology_isZero_of_lt k E e t ht m hm
  · intro i hi hUi
    change i1_chainDualPullback (2 * k) (F.map (homOfLE hUi)) (i1_chainDualPullback (2 * k) p u) =
      i1_chainDualPullback (2 * k) (F.map (homOfLE hUi)) (i1_chainDualPullback (2 * k) p v)
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
      i1_relativeSmallChainComparison_naturality,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
      i1_relativeSmallChainComparison_naturality]
    have he : relativeCohomologyMap ℚ (2 * k) (i1_subsetRelativePairInclusion X Z (e i).source) u =
        relativeCohomologyMap ℚ (2 * k) (i1_subsetRelativePairInclusion X Z (e i).source) v := h i hi
    have hr := congrArg (i1_subsetRelativeCoclassEquiv X Z (e i).source (2 * k)) he
    rw [i1_subsetRelativeCoclassEquiv_restriction, i1_subsetRelativeCoclassEquiv_restriction] at hr
    exact hr

end HodgeLean.Foundations.BundleThom
