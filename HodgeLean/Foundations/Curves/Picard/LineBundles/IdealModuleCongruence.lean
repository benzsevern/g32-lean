import HodgeLean.Foundations.Curves.Picard.LineBundles.Transport

/-! # Actual ideal module congruence and its inclusion

Equality of ideal sheaves transports the kernel module with its specified monomorphism.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Actual ideal module transport retains the specified kernel inclusion. -/
theorem idealModule_congr_inclusion {X : Scheme} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg idealModule h)).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

end HodgeLean.Foundations.Curves.Picard.LineBundles
