import HodgeLean.Foundations.BundleThom.RankChartIntersectionOrientationHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeIntersectionCompatibilityHelpers

/-! # Actual bundle-chart orientations in singular-range relative coordinates

The range class retains the original complex chart normalization.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
variable (e : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- The actual bundle-chart orientation in its actual singular-range relative quotient coordinates.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, oriented bundle charts; Hatcher, §3.1. -/
def i1_rankChartRangeOrientation :
    ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).obj
      (i1_singularSubsetRange (i1_totalSpace k E) e.source)).linearDualCochainComplex.homology (2 * k) :=
  i1_subsetRelativeCoclassEquiv (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ e.source (2 * k)
    (i1_chartOrientation k E e)

/-- The actual bundle-chart range orientations have matching pullbacks to the actual range intersection.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation compatibility; Hatcher, §3.1. -/
theorem i1_rankChartRangeOrientation_compatible (hk : 0 < k)
    (e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
    [e'.IsLinear ℂ] :
    i1_chainDualPullback (2 * k) ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
      (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).map (homOfLE
        (inf_le_left : i1_singularSubsetRange (i1_totalSpace k E) e.source ⊓
          i1_singularSubsetRange (i1_totalSpace k E) e'.source ≤
          i1_singularSubsetRange (i1_totalSpace k E) e.source))) (i1_rankChartRangeOrientation k E e) =
      i1_chainDualPullback (2 * k) ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace k E))
        (i1_singularSubsetRange (i1_totalSpace k E) (i1_zeroSupport k E)ᶜ)).map (homOfLE
          (inf_le_right : i1_singularSubsetRange (i1_totalSpace k E) e.source ⊓
            i1_singularSubsetRange (i1_totalSpace k E) e'.source ≤
            i1_singularSubsetRange (i1_totalSpace k E) e'.source))) (i1_rankChartRangeOrientation k E e') := by
  exact i1_subsetRelativeCoclassEquiv_intersection_compatible (i1_totalSpace k E)
    (i1_zeroSupport k E)ᶜ e.source e'.source (2 * k) (i1_chartOrientation k E e) (i1_chartOrientation k E e')
    (i1_rankChartOrientations_actualIntersection_compatible k hk E e e')

end HodgeLean.Foundations.BundleThom
