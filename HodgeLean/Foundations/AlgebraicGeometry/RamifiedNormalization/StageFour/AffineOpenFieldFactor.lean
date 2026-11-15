import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The prescribed affine-open section evaluation factors the actual original field point through that affine open. -/
theorem affine_open_field_factor
    {L : Type} [Field L] {Y : Scheme}
    (η : Spec ↧L ⟶ Y) (U : Y.affineOpens) (hU : ⊤ ≤ η ⁻¹ᵁ U.1) :
    Spec.map (η.appLE U.1 ⊤ hU ≫ (Scheme.ΓSpecIso ↧L).hom) ≫ U.2.fromSpec = η := by
  rw [Spec.map_comp, Category.assoc,
    U.2.SpecMap_appLE_fromSpec η (isAffineOpen_top _) hU,
    IsAffineOpen.fromSpec_top,
    ← Scheme.isoSpec_Spec_hom, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.RamifiedNormalization.StageFour
