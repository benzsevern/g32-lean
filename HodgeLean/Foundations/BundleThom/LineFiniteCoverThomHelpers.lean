import HodgeLean.Foundations.BundleThom.LineFiniteChartRangeThomHelpers
import HodgeLean.Foundations.BundleThom.FiniteRelativeSmallChainHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Actual supported Thom classes from finite line-chart covers

The relative small-chain comparison transfers the glued range class to the prescribed bundle total space.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- A nonempty finite actual linear chart cover of a complex line bundle supplies a supported class with all specified chart normalizations.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, finite Thom construction; Hatcher, §2.2 and §3.1. -/
theorem i1_lineFiniteCoverThom_exists {B ι : Type} [TopologicalSpace B]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e : ι → Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty)
    (hcover : ∀ z : TotalSpace (Fin 1 → ℂ) E, ∃ i ∈ s, z ∈ (e i).source) :
    ∃ u : i1_supportedClass 1 E, ∀ i ∈ s,
      relativeCohomologyMap ℚ 2 (i1_chartInclusion 1 E (e i)) u = i1_chartOrientation 1 E (e i) := by
  let X := i1_totalSpace 1 E
  let Z := (i1_zeroSupport 1 E)ᶜ
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  let U := fun i => i1_singularSubsetRange X (e i).source
  let K := s.sup U
  let p := i1_relativeSmallChainComparison X Z K
  haveI : QuasiIso p := i1_finiteRelativeSmallChainComparison_quasiIso X Z
    (fun i => (e i).source) s (fun i _ => (e i).open_source) hcover
  obtain ⟨w, hw⟩ := i1_lineFiniteChartRangeThom_exists E e s hs
  obtain ⟨u, hu⟩ := (i1_chainDualPullback_bijective 2 p).2 w
  refine ⟨u, ?_⟩
  intro i hi
  apply (i1_subsetRelativeCoclassEquiv X Z (e i).source 2).injective
  change i1_subsetRelativeCoclassEquiv X Z (e i).source 2
      (relativeCohomologyMap ℚ 2 (i1_subsetRelativePairInclusion X Z (e i).source) u) =
    i1_subsetRelativeCoclassEquiv X Z (e i).source 2 (i1_chartOrientation 1 E (e i))
  rw [i1_subsetRelativeCoclassEquiv_restriction]
  change i1_chainDualPullback 2 (i1_relativeSmallChainComparison X Z (U i)) u =
    i1_lineChartRangeOrientation E (e i)
  have hp : F.map (homOfLE (Finset.le_sup hi)) ≫ p =
      i1_relativeSmallChainComparison X Z (U i) :=
    i1_relativeSmallChainComparison_naturality X Z (U i) K (Finset.le_sup hi)
  rw [← hp, i1_chainDualPullback_comp, LinearMap.comp_apply, hu]
  exact hw i hi (Finset.le_sup
    (f := fun j => i1_singularSubsetRange (i1_totalSpace 1 E) (e j).source) hi)

end HodgeLean.Foundations.BundleThom
