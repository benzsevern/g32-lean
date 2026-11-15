import HodgeLean.Ported.Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral

/-! Integrality of the native blow-up of a nonzero ideal. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program

/-- A nonzero centre ideal on an integral locally Noetherian scheme has integral blow-up. -/
theorem g32l4_blowUp_isIntegral {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (K : X.IdealSheafData) (hK : K ≠ ⊥) : IsIntegral K.blowUp := by
  let J : X.IdealSheafData := ⊥
  letI : IsIso J.subschemeι := (Scheme.isIso_subschemeι_iff_eq_bot J).mpr rfl
  letI : IsIntegral J.subscheme := IsIntegral.of_isIso (inv J.subschemeι)
  have hnot : ¬ K ≤ J := by
    change ¬ K ≤ ⊥
    simpa only [le_bot_iff] using hK
  letI : IsIntegral (J.strictTransform K).subscheme :=
    isIntegral_strictTransform_subscheme K J hnot
  have hstrict : J.strictTransform K = ⊥ := by
    change ((⊥ : X.IdealSheafData).comap K.blowUpπ).saturate K.exceptionalDivisor = ⊥
    rw [Scheme.IdealSheafData.comap_bot]
    exact saturate_bot_of_isInvertible (blowUp.isInvertible_comap_π K)
  letI : IsIso (J.strictTransform K).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot (J.strictTransform K)).mpr hstrict
  exact IsIntegral.of_isIso (J.strictTransform K).subschemeι

end HodgeLean.Foundations.Program
