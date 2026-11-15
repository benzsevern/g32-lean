import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedNormalSlices

/-! Actual restrictions of common tangential maps and their support composites. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified tangential restriction commutes with the full inverse
image of the chosen ambient open. -/
theorem s4_q3_tangential_resLE_square
    {X W T : Scheme.{0}} (q : X ⟶ W) (h : W ⟶ T)
    (A : T.Opens) (B : W.Opens) (hBA : B ≤ h ⁻¹ᵁ A) :
    (q ∣_ B) ≫ h.resLE A B hBA =
      (q ≫ h).resLE A (q ⁻¹ᵁ B) (fun y hy => hBA hy) := by
  apply (cancel_mono A.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, morphismRestrict_ι,
    Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- Smoothness of both actual ambient tangential maps survives restriction
to the same smaller ambient open over the common smooth base. -/
theorem s4_q3_smooth_tangential_open_restriction
    {X W T : Scheme.{0}} (q : X ⟶ W) (h : W ⟶ T)
    (A : T.Opens) (B : W.Opens) (hBA : B ≤ h ⁻¹ᵁ A)
    (hsW : Smooth (h ∣_ A)) (hsX : Smooth ((q ≫ h) ∣_ A)) :
    Smooth (h.resLE A B hBA) ∧ Smooth ((q ∣_ B) ≫ h.resLE A B hBA) := by
  letI := hsW
  letI := hsX
  constructor
  · dsimp only [Scheme.Hom.resLE]
    infer_instance
  · rw [s4_q3_tangential_resLE_square]
    dsimp only [Scheme.Hom.resLE]
    infer_instance

end HodgeLean.Foundations.Program
