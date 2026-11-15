import HodgeLean.Foundations.BundleThom.LineChartIntersectionOrientationHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeIntersectionCompatibilityHelpers

/-! # Actual line-chart orientations in singular-range relative coordinates

The range class retains the original complex chart normalization.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin 1 → ℂ) E)]
variable [FiberBundle (Fin 1 → ℂ) E] [VectorBundle ℂ (Fin 1 → ℂ) E]
variable (e : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
variable [e.IsLinear ℂ]

/-- The actual line-chart orientation in its actual singular-range relative quotient coordinates.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, oriented bundle charts; Hatcher, §3.1. -/
def i1_lineChartRangeOrientation :
    ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace 1 E))
      (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)).obj
      (i1_singularSubsetRange (i1_totalSpace 1 E) e.source)).linearDualCochainComplex.homology 2 :=
  i1_subsetRelativeCoclassEquiv (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ e.source 2
    (i1_chartOrientation 1 E e)

/-- The actual line-chart range orientations have matching pullbacks to the actual range intersection.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation compatibility; Hatcher, §3.1. -/
theorem i1_lineChartRangeOrientation_compatible
    (e' : Trivialization (Fin 1 → ℂ) (TotalSpace.proj : TotalSpace (Fin 1 → ℂ) E → B))
    [e'.IsLinear ℂ] :
    i1_chainDualPullback 2 ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace 1 E))
      (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)).map (homOfLE
        (inf_le_left : i1_singularSubsetRange (i1_totalSpace 1 E) e.source ⊓
          i1_singularSubsetRange (i1_totalSpace 1 E) e'.source ≤
          i1_singularSubsetRange (i1_totalSpace 1 E) e.source))) (i1_lineChartRangeOrientation E e) =
      i1_chainDualPullback 2 ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj (i1_totalSpace 1 E))
        (i1_singularSubsetRange (i1_totalSpace 1 E) (i1_zeroSupport 1 E)ᶜ)).map (homOfLE
          (inf_le_right : i1_singularSubsetRange (i1_totalSpace 1 E) e.source ⊓
            i1_singularSubsetRange (i1_totalSpace 1 E) e'.source ≤
            i1_singularSubsetRange (i1_totalSpace 1 E) e'.source))) (i1_lineChartRangeOrientation E e') := by
  exact i1_subsetRelativeCoclassEquiv_intersection_compatible (i1_totalSpace 1 E)
    (i1_zeroSupport 1 E)ᶜ e.source e'.source 2 (i1_chartOrientation 1 E e) (i1_chartOrientation 1 E e')
    (i1_lineChartOrientations_actualIntersection_compatible E e e')

end HodgeLean.Foundations.BundleThom
