import HodgeLean.Foundations.BundleThom.LineChartRangeOrientationHelpers
import HodgeLean.Foundations.BundleThom.ChartRangeIntersectionHomologyHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinsetCoclassGluingHelpers

/-! # Oriented Thom gluing over finite actual line-chart range domains

Every input is the specified actual chart orientation and every overlap calculation is supplied internally.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- The actual orientations on a nonempty finite family of complex line charts have a relative coclass extension over their actual singular-domain union.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, finite Thom gluing; Hatcher, §2.2 and §3.1. -/
theorem i1_lineFiniteChartRangeThom_exists {B ι : Type} [TopologicalSpace B]
    (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
    [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
    (e : ι → Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [∀ i, (e i).IsLinear ℂ] (s : Finset ι) (hs : s.Nonempty) :
    ∃ z : ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace 1 E))
      (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)).obj
      (s.sup (fun i => i1_singularSubsetRange (i1_totalSpace 1 E) (e i).source))).linearDualCochainComplex.homology 2,
      ∀ (i : ι) (_ : i ∈ s)
        (hUi : i1_singularSubsetRange (i1_totalSpace 1 E) (e i).source ≤
          s.sup (fun j => i1_singularSubsetRange (i1_totalSpace 1 E) (e j).source)),
        i1_chainDualPullback 2 ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace 1 E))
          (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)).map (homOfLE hUi)) z =
          i1_lineChartRangeOrientation E (e i) := by
  apply i1_relativeSubcomplexFinsetCoclass_gluing (TopCat.toSSet.obj (i1_totalSpace 1 E))
    (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)
    (fun i => i1_singularSubsetRange (i1_totalSpace 1 E) (e i).source)
    (fun i => i1_lineChartRangeOrientation E (e i)) s hs
  · intro i hi j hj t ht
    exact i1_chartTripleRangeHomologyOne_isZero 1 E (e i) (e j) (e t) (by omega)
  · intro i hi j hj t ht r hr
    exact i1_chartQuadrupleRangeHomologyZero_isZero 1 E (e i) (e j) (e t) (e r) (by omega)
  · intro i hi j hj
    exact i1_lineChartRangeOrientation_compatible E (e i) (e j)

end HodgeLean.Foundations.BundleThom
