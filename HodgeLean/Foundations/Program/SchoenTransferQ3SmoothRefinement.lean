import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Smoothness on a smaller actual base open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smooth restriction stays smooth after refining the original base open. -/
theorem s4_q3_smooth_restriction_mono
    {X Y : Scheme.{0}} (f : X ⟶ Y) (U V : Y.Opens) (hVU : V ≤ U)
    (h : Smooth (f ∣_ U)) : Smooth (f ∣_ V) := by
  letI := h
  have hs : Smooth ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact (MorphismProperty.arrow_mk_iso_iff @Smooth
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f himage)).mp hs

end HodgeLean.Foundations.Program
