import HodgeLean.Foundations.BundleThom.BinarySmallSingularCoverHelpers
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual finite small singular covers

The finite union of supplied singular ranges retains the actual cover domains.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual small singular subcomplex of a supplied finite cover is the finite join of its actual singular subset ranges.
Source: Hatcher, Algebraic Topology, §2.2, small singular chains. -/
theorem i1_finiteSmallSingularSubcomplex_eq {ι : Type} (X : TopCat)
    (U : ι → Set X) (s : Finset ι) :
    coverSmallSingularSubcomplex X (fun i : s => U i.1) =
      s.sup (fun i => i1_singularSubsetRange X (U i)) := by
  ext n σ
  rw [Finset.sup_eq_iSup]
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, mem_coverSmallSingularSubcomplex_iff]
  constructor
  · rintro ⟨⟨i, hi⟩, hσ⟩
    exact ⟨i, hi, hσ⟩
  · rintro ⟨i, hi, hσ⟩
    exact ⟨⟨i, hi⟩, hσ⟩

/-- Actual rational finite small-chain inclusion is a quasi-isomorphism for a supplied finite open cover.
Source: Hatcher, Algebraic Topology, §2.2, subdivision and small-chain approximation. -/
theorem i1_finiteSmallChainInclusion_quasiIso {ι : Type} (X : TopCat)
    (U : ι → Set X) (s : Finset ι) (hU : ∀ i ∈ s, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i ∈ s, x ∈ U i) :
    QuasiIso (SSet.chainComplexMap (s.sup (fun i => i1_singularSubsetRange X (U i))).ι
      (ModuleCat.of ℚ ℚ)) := by
  have hopen : ∀ i : s, IsOpen (U i.1) := fun i => hU i.1 i.2
  have hc : ⋃ i : s, U i.1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hx⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hq := (coverSmallRationalChainHomotopyEquiv_of_openCover X (fun i : s => U i.1)
    hopen hc).quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hq
  change QuasiIso (SSet.chainComplexMap
    (coverSmallSingularSubcomplex X (fun i : s => U i.1)).ι (ModuleCat.of ℚ ℚ)) at hq
  rw [i1_finiteSmallSingularSubcomplex_eq] at hq
  exact hq

end HodgeLean.Foundations.BundleThom
