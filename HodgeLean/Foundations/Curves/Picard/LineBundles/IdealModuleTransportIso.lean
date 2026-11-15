import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealPullbackIsoCongruence

/-! # Actual ideal module isomorphisms with a transported target

A separate generic comparison keeps target equality transport abstract.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

/-- Transport the ideal target of an actual module isomorphism. -/
def idealModuleTransportIso {X : Scheme} {M : X.Modules} {I J : X.IdealSheafData}
    (h : I = J) (e : M ≅ idealModule I) : M ≅ idealModule J :=
  e ≪≫ eqToIso (congrArg (fun K : X.IdealSheafData => idealModule K) h)

/-- Actual ideal target transport retains the specified inclusion. -/
theorem idealModuleTransportIso_inclusion {X : Scheme} {M : X.Modules} {I J : X.IdealSheafData}
    (h : I = J) (e : M ≅ idealModule I) :
    (idealModuleTransportIso h e).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
      e.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom) := by
  cases h
  simp only [idealModuleTransportIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.comp_id]

end HodgeLean.Foundations.Curves.Picard.LineBundles
