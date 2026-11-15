import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullback

/-! # Vanishing of the ideal inclusion on its subscheme

The adjunction identifies the pulled-back inclusion with the kernel condition.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Pulling the ideal inclusion to its own subscheme gives zero. -/
theorem ideal_inclusion_pullback_zero {X : Scheme} (I : X.IdealSheafData) :
    (Scheme.Modules.pullback I.subschemeι).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
      (pullbackUnit I.subschemeι).hom = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, pullbackUnit_adjunct]
  change kernel.ι _ ≫ SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom = _
  rw [kernel.condition]
  simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

end HodgeLean.Foundations.Curves.Picard.LineBundles
