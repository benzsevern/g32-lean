import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealPullbackMap
import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealModuleCongruence

/-! # Actual ideal pullback isomorphisms and target congruence

The generic inclusion formula keeps the invertibility instance abstract.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

/-- Composing actual ideal module transport retains its specified inclusion. -/
theorem idealModule_congr_comp_inclusion {X : Scheme} {M : X.Modules}
    {I J : X.IdealSheafData} (h : I = J) (e : M ⟶ idealModule I) :
    (e ≫ (eqToIso (congrArg (fun K : X.IdealSheafData => idealModule K) h)).hom) ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
      e ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

end HodgeLean.Foundations.Curves.Picard.LineBundles
