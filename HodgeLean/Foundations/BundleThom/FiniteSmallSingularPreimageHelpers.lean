import HodgeLean.Foundations.BundleThom.FiniteSmallSingularCoverHelpers
import HodgeLean.Foundations.BundleThom.SingularSubsetPreimageHelpers

/-! # Actual finite small covers restricted to topological subspaces

The restricted singular ranges retain the actual inclusion of the supplied subspace.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Restriction of a finite actual singular-domain join to a supplied subspace is the finite join of its actual restricted domains.
Source: Hatcher, Algebraic Topology, §2.2, restriction of small singular covers. -/
theorem i1_finiteSingularSubsetRange_preimage {ι : Type} (X : TopCat)
    (U : ι → Set X) (Z : Set X) (s : Finset ι) :
    (s.sup (fun i => i1_singularSubsetRange X (U i))).preimage
        (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) =
      s.sup (fun i => i1_singularSubsetRange (TopCat.of Z) {z : Z | z.1 ∈ U i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty]
    ext n σ
    exact Iff.rfl
  | @insert a s ha ih =>
    rw [Finset.sup_insert, SSet.Subcomplex.preimage_max,
      i1_singularSubsetRange_preimage, ih, Finset.sup_insert]

/-- A supplied finite open cover computes rational singular chains after restriction to any actual topological subspace.
Source: Hatcher, Algebraic Topology, §2.2, small-chain approximation on subspaces. -/
theorem i1_finiteSmallChainInclusion_onSubset_quasiIso {ι : Type} (X : TopCat)
    (U : ι → Set X) (Z : Set X) (s : Finset ι) (hU : ∀ i ∈ s, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i ∈ s, x ∈ U i) :
    QuasiIso (SSet.chainComplexMap
      (((s.sup (fun i => i1_singularSubsetRange X (U i))).preimage
        (TopCat.toSSet.map (topologicalSubsetInclusion X Z))).ι) (ModuleCat.of ℚ ℚ)) := by
  rw [i1_finiteSingularSubsetRange_preimage]
  apply i1_finiteSmallChainInclusion_quasiIso (TopCat.of Z)
  · intro i hi
    exact (hU i hi).preimage continuous_subtype_val
  · intro z
    obtain ⟨i, hi, hz⟩ := hcover z.1
    exact ⟨i, hi, hz⟩

end HodgeLean.Foundations.BundleThom
