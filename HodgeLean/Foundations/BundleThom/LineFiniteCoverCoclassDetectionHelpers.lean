import HodgeLean.Foundations.BundleThom.ChartRangeIntersectionHomologyHelpers
import HodgeLean.Foundations.BundleThom.FiniteRelativeSmallChainHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinsetCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Actual supported line-bundle coclass detection by finite chart covers

The finite domain comparison retains the supplied actual total space and every supplied chart inclusion.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- Restrictions to a nonempty finite actual linear chart cover detect supported rational classes of a complex line bundle.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative finite-cover detection; Bott–Tu, §6. -/
theorem i1_lineFiniteCoverCoclass_ext {B ι : Type} [TopologicalSpace B]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e : ι → Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin 1 → ℂ) E, ∃ i ∈ s, z ∈ (e i).source)
    (u v : i1_supportedClass 1 E)
    (h : ∀ i ∈ s, relativeCohomologyMap ℚ 2 (i1_chartInclusion 1 E (e i)) u =
      relativeCohomologyMap ℚ 2 (i1_chartInclusion 1 E (e i)) v) : u = v := by
  let X := i1_totalSpace 1 E
  let Z := (i1_zeroSupport 1 E)ᶜ
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  let U := fun i => i1_singularSubsetRange X (e i).source
  let K := s.sup U
  let p := i1_relativeSmallChainComparison X Z K
  haveI : QuasiIso p := i1_finiteRelativeSmallChainComparison_quasiIso X Z
    (fun i => (e i).source) s (fun i _ => (e i).open_source) hcover
  apply (i1_chainDualPullback_bijective 2 p).1
  apply i1_relativeSubcomplexFinsetCoclass_ext (TopCat.toSSet.obj X)
    (i1_singularSubsetRange X Z) U s hs
  · intro i hi j hj
    simpa only [inf_assoc, inf_idem] using
      i1_chartTripleRangeHomologyOne_isZero 1 E (e i) (e j) (e j) (by omega)
  · intro i hi j hj t ht
    simpa only [inf_assoc, inf_idem] using
      i1_chartQuadrupleRangeHomologyZero_isZero 1 E (e i) (e j) (e t) (e t) (by omega)
  · intro i hi hUi
    change i1_chainDualPullback 2 (F.map (homOfLE hUi)) (i1_chainDualPullback 2 p u) =
      i1_chainDualPullback 2 (F.map (homOfLE hUi)) (i1_chainDualPullback 2 p v)
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
      i1_relativeSmallChainComparison_naturality,
      ← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
      i1_relativeSmallChainComparison_naturality]
    have he : relativeCohomologyMap ℚ 2 (i1_subsetRelativePairInclusion X Z (e i).source) u =
        relativeCohomologyMap ℚ 2 (i1_subsetRelativePairInclusion X Z (e i).source) v := h i hi
    have hr := congrArg (i1_subsetRelativeCoclassEquiv X Z (e i).source 2) he
    rw [i1_subsetRelativeCoclassEquiv_restriction, i1_subsetRelativeCoclassEquiv_restriction] at hr
    exact hr

end HodgeLean.Foundations.BundleThom
