import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Defs

/-! Pointed neighborhood transfer from a subspace containing a neighborhood.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology

lemma basis_at_of_neighborhood_subtype {S : Type*} [TopologicalSpace S]
    (K : Set S) (x : S) (hxK : x ∈ K) (hK : K ∈ nhds x)
    (hbase : ∀ (y : K) (U : Opens K), y ∈ U →
      ∃ V : Opens K, y ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (U : Opens S) (hxU : x ∈ U) :
    ∃ V : Opens S, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  obtain ⟨O, hOK, hO, hxO⟩ := mem_nhds_iff.mp hK
  let U' : Opens K := ⟨Subtype.val ⁻¹' (O ∩ U),
    (hO.inter U.isOpen).preimage continuous_subtype_val⟩
  obtain ⟨V, hxV, hcV, hVU⟩ := hbase ⟨x, hxK⟩ U' ⟨hxO, hxU⟩
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp V.isOpen
  have heq : Subtype.val '' (V : Set K) = W ∩ O := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by rw [← hWV] at hy; exact hy, (hVU hy).1⟩
    · rintro ⟨hzW, hzO⟩
      refine ⟨⟨z, hOK hzO⟩, ?_, rfl⟩
      rw [← hWV]
      exact hzW
  let T : Opens S := ⟨Subtype.val '' (V : Set K), heq ▸ hW.inter hO⟩
  refine ⟨T, ⟨⟨x, hxK⟩, hxV, rfl⟩, ?_, ?_⟩
  · exact (IsEmbedding.subtypeVal.homeomorphImage (V : Set K)).contractibleSpace_iff.mp hcV
  · rintro z ⟨y, hy, rfl⟩
    exact (hVU hy).2

end HodgeLean.Foundations.ComplexTopology
