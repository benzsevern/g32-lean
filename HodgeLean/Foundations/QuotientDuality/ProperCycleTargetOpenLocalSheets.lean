import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicLocalDegree

/-! # Actual local sheets above an open target neighborhood -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual local inverses of the open-target restriction give actual local sheets of the original map at every point above that target open.
Source: Mathlib, IsLocalHomeomorphOn.of_comp_right and open subtype inclusions.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_sheets_of_open_target_restriction
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (V : Set Y) (hV : IsOpen V)
    (hlocal : IsLocalHomeomorph (V.restrictPreimage f)) :
    IsLocalHomeomorphOn f (f ⁻¹' V) := by
  have hsrc := (hV.preimage hf).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have htgt := hV.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph (f ∘ (Subtype.val : (f ⁻¹' V) → X)) := htgt.comp hlocal
  have h := (hcomp.isLocalHomeomorphOn (s := Set.univ)).of_comp_right
    (hsrc.isLocalHomeomorphOn (s := Set.univ))
  intro x hx
  exact h x ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

end HodgeLean.Foundations.QuotientDuality
