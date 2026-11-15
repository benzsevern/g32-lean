import HodgeLean.Foundations.BundleThom.BinarySmallSingularCoverHelpers

/-! # Actual restricted small covers on a supplied topological subspace

The singular preimage is identified with the subset's own singular range, retaining the actual inclusion map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Restricting an actual singular subset range to a topological subspace gives the singular range of the restricted subset.
Source: Hatcher, Algebraic Topology, §2.2, restriction of small singular covers. -/
theorem i1_singularSubsetRange_preimage (X : TopCat) (U Z : Set X) :
    (i1_singularSubsetRange X U).preimage (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) =
      i1_singularSubsetRange (TopCat.of Z) {z : Z | z.1 ∈ U} := by
  ext n σ
  change (TopCat.toSSet.map (topologicalSubsetInclusion X Z)).app n σ ∈
    (i1_singularSubsetRange X U).obj n ↔
    σ ∈ (i1_singularSubsetRange (TopCat.of Z) {z : Z | z.1 ∈ U}).obj n
  rw [i1_mem_singularSubsetRange_iff, i1_mem_singularSubsetRange_iff]
  rfl

/-- Actual binary small chains restricted to any supplied subspace still compute its full rational chains.
Source: Hatcher, Algebraic Topology, §2.2, small-chain approximation on subspaces. -/
theorem i1_binarySmallChainInclusion_onSubset_quasiIso (X : TopCat) (U V Z : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (SSet.chainComplexMap
      (((i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V).preimage
        (TopCat.toSSet.map (topologicalSubsetInclusion X Z))).ι) (ModuleCat.of ℚ ℚ)) := by
  rw [SSet.Subcomplex.preimage_max, i1_singularSubsetRange_preimage,
    i1_singularSubsetRange_preimage]
  apply i1_binarySmallChainInclusion_quasiIso (TopCat.of Z)
  · exact hU.preimage continuous_subtype_val
  · exact hV.preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro z
    change z.1 ∈ U ∨ z.1 ∈ V
    have hz : z.1 ∈ U ∪ V := by rw [hcover]; trivial
    exact hz

end HodgeLean.Foundations.BundleThom
