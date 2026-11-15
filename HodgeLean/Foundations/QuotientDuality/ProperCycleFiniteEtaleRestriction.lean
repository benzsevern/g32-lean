import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericAffineEtaleOpen

/-! # Literal finite etale maps on smaller base opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting a finite etale base open to any smaller actual open retains both properties on the literal original restricted morphism.
Source: SGA 1, Expose I, base change of finite etale morphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_etale_restriction_le {X Y : Scheme.{0}}
    (f : X ⟶ Y) (U W : Y.Opens) (hWU : W ≤ U)
    [IsFinite (f ∣_ U)] [Etale (f ∣_ U)] :
    IsFinite (f ∣_ W) ∧ Etale (f ∣_ W) := by
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hWU
  constructor
  · rw [← hVW]
    exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f U V)).mp inferInstance
  · rw [← hVW]
    exact (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictRestrict f U V)).mp inferInstance

end HodgeLean.Foundations.QuotientDuality
