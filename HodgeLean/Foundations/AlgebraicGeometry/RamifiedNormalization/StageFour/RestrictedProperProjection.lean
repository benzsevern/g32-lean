import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.LocalAtTarget

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restricting a proper projection to the inverse image of the selected base chart retains properness. -/
theorem proper_projection_restrict_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsProperMap f) (S : Set Y) :
    IsProperMap (S.restrictPreimage f) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf.continuous.restrictPreimage, hf.isClosedMap.restrictPreimage S, ?_⟩
  intro y
  rw [Subtype.isCompact_iff]
  have himage : Subtype.val '' ((S.restrictPreimage f) ⁻¹' {y}) = f ⁻¹' {y.val} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (show S.restrictPreimage f z = y from hz)
    · intro hx
      change f x = y.val at hx
      have hxS : f x ∈ S := by rw [hx]; exact y.property
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      change S.restrictPreimage f ⟨x, hxS⟩ = y
      exact Subtype.ext hx
  rw [himage]
  exact hf.isCompact_preimage isCompact_singleton

end AlgebraicGeometry.RamifiedNormalization.StageFour
