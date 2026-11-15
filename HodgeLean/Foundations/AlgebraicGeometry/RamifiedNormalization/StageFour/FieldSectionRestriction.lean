import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restricting a section before evaluation at the specified original field point retains its value. -/
theorem field_coefficient_comp
    {L : Type} [Field L] {X Y : Scheme}
    (η : Spec ↧L ⟶ X) (f : X ⟶ Y) :
    StageThree.fieldCoeff (η ≫ f) = (StageThree.fieldCoeff η).comp f.appTop.hom := by
  unfold StageThree.fieldCoeff
  rw [Scheme.Hom.comp_appTop]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
