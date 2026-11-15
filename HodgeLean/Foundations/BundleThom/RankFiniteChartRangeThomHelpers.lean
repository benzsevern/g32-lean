import HodgeLean.Foundations.BundleThom.RankChartRangeOrientationHelpers
import HodgeLean.Foundations.BundleThom.FiniteChartIntersectionHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinitePositiveCoclassHelpers

/-! # Oriented Thom gluing over finite actual complex chart range domains

Every input is the specified actual chart orientation and every overlap calculation is supplied internally.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- The actual orientations on a nonempty finite family of complex charts have a relative coclass extension over their actual singular-domain union.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, finite Thom gluing; Hatcher, §2.2 and §3.1. -/
theorem i1_rankFiniteChartRangeThom_exists {B ι : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (e : ι → Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty) :
    ∃ z : ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).obj
      (s.sup (fun i => i1_singularSubsetRange (i1_totalSpace k E) (e i).source))).linearDualCochainComplex.homology (2 * k),
      ∀ (i : ι) (_ : i ∈ s)
        (hUi : i1_singularSubsetRange (i1_totalSpace k E) (e i).source ≤
          s.sup (fun j => i1_singularSubsetRange (i1_totalSpace k E) (e j).source)),
        i1_chainDualPullback (2 * k) ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
          (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).map (homOfLE hUi)) z =
          i1_rankChartRangeOrientation k E (e i) := by
  apply i1_relativeSubcomplexFinsetPositiveCoclass_gluing (TopCat.toSSet.obj (i1_totalSpace k E))
    (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)
    (2 * k) (by omega) (fun i => i1_singularSubsetRange (i1_totalSpace k E) (e i).source)
    (fun i => i1_rankChartRangeOrientation k E (e i)) s hs
  · intro t ht m hm
    exact i1_chartFinsetRangeIntersectionHomology_isZero_of_lt k E e t ht m hm
  · intro i hi j hj
    exact i1_rankChartRangeOrientation_compatible k E (e i) hk (e j)

end HodgeLean.Foundations.BundleThom
