import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffinePullbackCompatibility
import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers

/-! # The natural ideal comparison for ambient open restrictions
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- Restriction of the structure module transposes to the structure-sheaf map. -/
lemma restrictUnitIso_transpose {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  rw [Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change (f.appIso (f ⁻¹ᵁ U)).hom
      (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op r) = f.app U r
  apply (ConcreteCategory.bijective_of_isIso (f.appIso (f ⁻¹ᵁ U)).inv).injective
  rw [Iso.hom_inv_id_apply]
  exact (congrArg (fun t : Γ(Y, U) ⟶ Γ(Y, f ''ᵁ (f ⁻¹ᵁ U)) => t r)
    (f.app_appIso_inv U)).symm

/-- The pullback/restriction identification respects the structure-module comparison. -/
lemma pullbackUnit_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫ (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    ((Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)).hom.app _ ≫ _) = _
  rw [leftAdjointUniq_homEquiv_comp, restrictUnitIso_transpose]
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom).symm

/-- The existing open ideal isomorphism respects its kernel inclusion. -/
lemma openIdealIso_inclusion {Q W : Scheme.{0}} (i : Q ⟶ W) (U : W.Opens) :
    (s2e_idealModule_restrict_iso i U).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ∣_ U).toRingCatSheafHom) =
      (Scheme.Modules.restrictFunctor U.ι).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  unfold s2e_idealModule_restrict_iso
  rw [Iso.trans_hom, Category.assoc, kernel.mapIso_hom, kernel.map, kernel.lift_ι,
    ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The natural ideal comparison is invertible for an ambient open restriction. -/
lemma idealPullbackMap_open_isIso {Q W : Scheme.{0}} (i : Q ⟶ W) (U : W.Opens) :
    IsIso (idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
      (morphismRestrict_ι i U).symm) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (idealModule i) ≪≫
    s2e_idealModule_restrict_iso i U
  have he : e.hom = idealPullbackMap i (i ∣_ U) U.ι (i ⁻¹ᵁ U).ι
      (morphismRestrict_ι i U).symm := by
    apply (cancel_mono (kernel.ι
      (SheafOfModules.unitToPushforwardObjUnit (i ∣_ U).toRingCatSheafHom))).mp
    change ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app (idealModule i) ≫
      (s2e_idealModule_restrict_iso i U).hom) ≫ _ = _
    rw [Category.assoc, openIdealIso_inclusion, idealPullbackMap_inclusion]
    calc
      _ = (Scheme.Modules.pullback U.ι).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
          (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app _ ≫
          (Scheme.Modules.restrictUnitIso U.ι).hom := by
        rw [← Category.assoc]
        exact congrArg (fun t => t ≫ (Scheme.Modules.restrictUnitIso U.ι).hom)
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality _).symm
      _ = _ := by rw [pullbackUnit_restrict]
  rw [← he]
  infer_instance

end AlgebraicGeometry.Conormal
