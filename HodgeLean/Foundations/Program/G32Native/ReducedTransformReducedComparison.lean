import HodgeLean.Foundations.Program.G32Native.ReducedTransformSaturation
import HodgeLean.Ported.Hironaka.Scheme.Snc.DictionaryOrder
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Composite

/-! Agreement with the saturation transform when its subscheme is reduced. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Reducedness removes the radical in the transform comparison. -/
theorem g32l4_reducedTransform_eq_strictTransformAlong {X Y : Scheme}
    [IsLocallyNoetherian X] (f : X ⟶ Y) (D K : Y.IdealSheafData)
    [IsReduced (D.strictTransformAlong f (K.comap f)).subscheme] :
    s2c_strictTransform f D K = D.strictTransformAlong f (K.comap f) := by
  rw [g32l4_reducedTransform_eq_radical_strictTransformAlong]
  exact radical_eq_self_of_isReduced_subscheme _

/-- The native blow-up uses the ported strict-transform ideal for a reduced transform. -/
theorem g32l4_reducedTransform_blowUp_eq_strictTransform {X : Scheme}
    [IsLocallyNoetherian X] (D K : X.IdealSheafData)
    [IsReduced (D.strictTransform K).subscheme] :
    s2c_strictTransform K.blowUpπ D K = D.strictTransform K := by
  letI : IsLocallyNoetherian K.blowUp := Scheme.IdealSheafData.blowUp.isLocallyNoetherian K
  haveI : IsReduced (D.strictTransformAlong K.blowUpπ (K.comap K.blowUpπ)).subscheme := by
    simpa only [Scheme.IdealSheafData.strictTransform,
      Scheme.IdealSheafData.exceptionalDivisor] using
      (inferInstance : IsReduced (D.strictTransform K).subscheme)
  exact g32l4_reducedTransform_eq_strictTransformAlong K.blowUpπ D K

end HodgeLean.Foundations.Program
