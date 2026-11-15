import HodgeLean.Foundations.Program.SchoenTransferQ3SharedCoordinateMorphisms

/-! Ambient refinement retaining exactly the specified support open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A specified support open inside an ambient open is the exact inverse image
of a smaller ambient open under the actual immersion. -/
theorem s4_q3_support_open_ambient_refinement
    {D W : Scheme} (j : D ⟶ W) [IsClosedImmersion j]
    (U : W.Opens) (V : D.Opens) (hVU : V ≤ j ⁻¹ᵁ U) :
    ∃ U' : W.Opens, U' ≤ U ∧ j ⁻¹ᵁ U' = V := by
  obtain ⟨O, hO, hpre⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let O' : W.Opens := ⟨O, hO⟩
  refine ⟨U ⊓ O', inf_le_left, ?_⟩
  have heq : j ⁻¹ᵁ O' = V := by
    exact SetLike.coe_injective hpre
  rw [Scheme.Hom.preimage_inf, heq, inf_eq_right.mpr hVU]

end HodgeLean.Foundations.Program
