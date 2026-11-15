import HodgeLean.Foundations.Program.SchoenTowerConormalDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- Restriction of the actual pushed structure module to an ambient open
agrees with pushforward from its actual inverse-image scheme open. -/
def s2e_open_restrict_pushforward_unit_iso
    {Q W : Scheme.{0}} (k : Q ⟶ W) (U : W.Opens) :
    Scheme.Modules.restrict
      ((Scheme.Modules.pushforward k).obj (SheafOfModules.unit Q.ringCatSheaf)) U.ι ≅
      (Scheme.Modules.pushforward (k ∣_ U)).obj
        (SheafOfModules.unit (k ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let A := Scheme.Modules.restrict
    ((Scheme.Modules.pushforward k).obj (SheafOfModules.unit Q.ringCatSheaf)) U.ι
  let B := (Scheme.Modules.pushforward (k ∣_ U)).obj
    (SheafOfModules.unit (k ⁻¹ᵁ U).toScheme.ringCatSheaf)
  let c (V : U.toScheme.Opensᵒᵖ) : A.val.obj V ≅ B.val.obj V := by
    let e := Q.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage k U V.unop)).op
    refine (show A.val.obj V ≃ₗ[U.toScheme.ringCatSheaf.obj.obj V] B.val.obj V from ?_).toModuleIso
    refine
      { __ := e.commRingCatIsoToRingEquiv.toAddEquiv
        map_smul' := ?_ }
    intro r x
    change e.hom (k.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv r) *
      (show Γ(Q, k ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)) =
      (k ∣_ U).app V.unop r *
        (show Γ((k ⁻¹ᵁ U).toScheme, (k ∣_ U) ⁻¹ᵁ V.unop) from e.hom x)
    rw [U.ι_appIso]
    change e.hom (k.app (U.ι ''ᵁ V.unop) r *
      (show Γ(Q, k ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)) =
      (k ∣_ U).app V.unop r *
        (show Γ((k ⁻¹ᵁ U).toScheme, (k ∣_ U) ⁻¹ᵁ V.unop) from e.hom x)
    rw [morphismRestrict_app]
    exact map_mul e.hom.hom (k.app (U.ι ''ᵁ V.unop) r)
      (show Γ(Q, k ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)
  exact (SheafOfModules.fullyFaithfulForget U.toScheme.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk c (by
      intro V V' f
      ext x
      dsimp only [c]
      change Q.presheaf.map _ (Q.presheaf.map _
        (show Γ(Q, k ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x)) =
        Q.presheaf.map _ (Q.presheaf.map _
          (show Γ(Q, k ⁻¹ᵁ (U.ι ''ᵁ V.unop)) from x))
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl))

end HodgeLean.Foundations.Program
