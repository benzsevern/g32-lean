import HodgeLean.Foundations.WitnessSelection.TowerHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.WitnessSelection

theorem restriction_isIso_of_open_iso {X Y : Scheme} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (E : U.toScheme ≅ V.toScheme)
    (he : E.hom ≫ V.ι = U.ι ≫ f) (hpre : f ⁻¹ᵁ V = U) : IsIso (f ∣_ V) := by
  have hp : IsPullback E.hom U.ι V.ι f := by
    apply IsOpenImmersion.isPullback _ _ _ _ he.symm
    simpa only [Scheme.Opens.opensRange_ι] using hpre
  haveI : IsIso (pullback.snd f V.ι) := by
    rw [← hp.flip.isoPullback_inv_snd]
    infer_instance
  haveI : IsIso ((pullbackRestrictIsoRestrict f V).hom ≫ (f ∣_ V)) := by
    rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict f V).hom _

end HodgeLean.WitnessSelection
