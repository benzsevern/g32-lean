import HodgeLean.Foundations.Program.SchoenTransferQ3ReducedPieceStalk
import HodgeLean.Adapters.CycleClassFlatPullback

/-! Actual reduced immersed pieces around generic inverse components. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A generic component has an actual reduced immersed neighbourhood whose
underlying image is open in the original, possibly nonreduced scheme. -/
theorem s4_q3_reduced_component_open_piece
    (K : Scheme) [IsNoetherian K] (η : K)
    (hη : closure ({η} : Set K) ∈ irreducibleComponents K) :
    ∃ U : K.Opens, η ∈ U ∧
      let I := ccm3_primeIdeal K η
      let ψ := (I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι
      IsOpenEmbedding ψ.base ∧ Set.range ψ = (U : Set K) := by
  obtain ⟨O, hO, ⟨t, ht⟩, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hη
  have hηO : η ∈ O :=
    (specializes_iff_mem_closure.mpr (hOC ht)).mem_open hO ht
  let U : K.Opens := ⟨O, hO⟩
  let I := ccm3_primeIdeal K η
  let ψ := (I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι
  have hI : Set.range I.subschemeι = closure ({η} : Set K) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hrange : Set.range ψ = (U : Set K) := by
    ext w
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hw
      obtain ⟨s, hs⟩ := hI.symm ▸ hOC hw
      refine ⟨⟨s, ?_⟩, ?_⟩
      · change I.subschemeι s ∈ U
        rwa [hs]
      · exact hs
  refine ⟨U, hηO, ?_⟩
  dsimp only
  exact ⟨{ toIsEmbedding := ψ.isEmbedding
           isOpen_range := hrange.symm ▸ U.isOpen }, hrange⟩

end HodgeLean.Foundations.Program
