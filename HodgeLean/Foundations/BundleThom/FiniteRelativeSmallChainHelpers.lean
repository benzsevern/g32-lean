import HodgeLean.Foundations.BundleThom.FiniteSmallSingularPreimageHelpers
import HodgeLean.Foundations.BundleThom.RelativeSmallChainComparisonHelpers

/-! # Actual rational relative small-chain comparison for finite open covers

Both the ambient and supplied relative-subspace small-chain comparisons are retained.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual relative small-chain comparison for a finite open cover is a quasi-isomorphism for every supplied relative subspace.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain approximation. -/
theorem i1_finiteRelativeSmallChainComparison_quasiIso {ι : Type} (X : TopCat) (Z : Set X)
    (U : ι → Set X) (s : Finset ι) (hU : ∀ i ∈ s, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i ∈ s, x ∈ U i) :
    QuasiIso (i1_relativeSmallChainComparison X Z
      (s.sup (fun i => i1_singularSubsetRange X (U i)))) :=
  i1_relativeSmallChainComparison_quasiIso X Z _
    (i1_finiteSmallChainInclusion_onSubset_quasiIso X U Z s hU hcover)
    (i1_finiteSmallChainInclusion_quasiIso X U s hU hcover)

end HodgeLean.Foundations.BundleThom
