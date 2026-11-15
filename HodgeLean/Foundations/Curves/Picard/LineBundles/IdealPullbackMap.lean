import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealSquareVanishing

/-! # The actual morphism to the pulled-back ideal module

The kernel universal property factors the pulled-back ideal inclusion.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The pulled-back ideal inclusion vanishes on the actual pulled-back subscheme. -/
theorem ideal_pullback_inclusion_vanishes {X Y : Scheme} (f : Y ⟶ X)
    (I : X.IdealSheafData) :
    (Scheme.Modules.pullback f).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
      (pullbackUnit f).hom ≫
      SheafOfModules.unitToPushforwardObjUnit (I.comap f).subschemeι.toRingCatSheafHom = 0 := by
  let J := I.comap f
  let g := (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
  have hsq : J.subschemeι ≫ f = g ≫ I.subschemeι := by
    dsimp [g, J]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      I.comapIso_hom_fst]
  have hz := unitValuedPullback_square_zero f J.subschemeι I.subschemeι g hsq
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom))
    (ideal_inclusion_pullback_zero I)
  have he := congrArg
    ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).homEquiv _ _) hz
  rw [Adjunction.homEquiv_naturality_left, pullbackUnit_adjunct] at he
  rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at he
  simpa only [Category.assoc, pushforwardUnit] using he

/-- The canonical actual module map to the comap ideal, retaining its inclusion. -/
def idealPullbackHom {X Y : Scheme} (f : Y ⟶ X) (I : X.IdealSheafData) :
    (Scheme.Modules.pullback f).obj (idealModule I) ⟶ idealModule (I.comap f) :=
  kernel.lift _
    ((Scheme.Modules.pullback f).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
        (pullbackUnit f).hom)
    (by simpa only [Category.assoc] using ideal_pullback_inclusion_vanishes f I)

/-- The canonical ideal pullback map preserves the actual ideal inclusion. -/
theorem idealPullbackHom_inclusion {X Y : Scheme} (f : Y ⟶ X) (I : X.IdealSheafData) :
    idealPullbackHom f I ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (I.comap f).subschemeι.toRingCatSheafHom) =
      (Scheme.Modules.pullback f).map
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
        (pullbackUnit f).hom :=
  kernel.lift_ι _ _ _

end HodgeLean.Foundations.Curves.Picard.LineBundles
