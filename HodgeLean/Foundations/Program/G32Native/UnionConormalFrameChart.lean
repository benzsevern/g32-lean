import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Ambient affine neighborhoods subordinate to conormal frame neighborhoods -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A frame neighborhood on a closed component contains the preimage of
an ambient affine neighborhood of its specified point. -/
lemma unionConormal_exists_affine_frame_chart
    {X V : Scheme} (i : X ⟶ V) [IsClosedImmersion i]
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ W : V.Opens, IsAffineOpen W ∧ i x ∈ W ∧ i ⁻¹ᵁ W ≤ U := by
  obtain ⟨O, hO, he⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  have hxi : i x ∈ O := by
    change x ∈ i ⁻¹' O
    rw [he]
    exact hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hxi hO
  refine ⟨W, hW, hxW, ?_⟩
  intro y hy
  have hyo : i y ∈ O := hWO hy
  change y ∈ (U : Set X)
  rw [← he]
  exact hyo

#print axioms unionConormal_exists_affine_frame_chart
end HodgeLean.Foundations.Program.G32Native
