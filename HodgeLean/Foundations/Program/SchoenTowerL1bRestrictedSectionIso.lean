import HodgeLean.Foundations.Program.SchoenTowerL1bUnitCentre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism on a whole inverse image gives an isomorphism of the actual section map. -/
theorem s2v_l1b_restricted_section_isIso
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
  have h : f.appLE U (f ⁻¹ᵁ U) le_rfl =
      U.topIso.inv ≫ (f ∣_ U).app ⊤ ≫ (f ⁻¹ᵁ U).topIso.hom := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_app_top]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [h]
  infer_instance

end HodgeLean.Foundations.Program
