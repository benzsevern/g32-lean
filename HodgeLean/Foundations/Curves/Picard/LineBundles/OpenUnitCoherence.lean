import HodgeLean.Foundations.Curves.Picard.LineBundles.OpenPullbackAdjunction
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullback

/-! # The structure module in open restriction and pullback

The canonical open comparison retains the actual structure-ring coefficient map.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The restricted structure-module comparison is adjoint to the coefficient map. -/
theorem restrictUnit_adjunct {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (Scheme.Modules.restrictUnitIso f).hom = pushforwardUnit f := by
  ext U s
  change (f.appIso (f ⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op s) = f.app U s
  apply (ConcreteCategory.bijective_of_isIso (f.appIso (f ⁻¹ᵁ U)).inv).injective
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
    ← CommRingCat.comp_apply, f.app_appIso_inv]
  rfl

/-- Open restriction and pullback have the same canonical structure-module comparison. -/
theorem restrictPullback_unit {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app (unit Y)).inv ≫
        (Scheme.Modules.restrictUnitIso f).hom = (pullbackUnit f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [restrictPullback_adjunct, pullbackUnit_adjunct, restrictUnit_adjunct]

end HodgeLean.Foundations.Curves.Picard.LineBundles
