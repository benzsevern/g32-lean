import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealPullbackMap

/-! # Actual ideal pullback isomorphisms retaining their inclusions

Equality elimination identifies the target before constructing the comparison.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

/-- An invertible actual ideal pullback map gives a comparison to the specified comap ideal. -/
theorem idealPullbackIso_exists {X Y : Scheme} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (J : X.IdealSheafData) (h : J = I.comap f)
    [IsIso (idealPullbackHom f I)] :
    ∃ e : (Scheme.Modules.pullback f).obj (idealModule I) ≅ idealModule J,
      e.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom) =
        (Scheme.Modules.pullback f).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)) ≫
          (pullbackUnit f).hom := by
  subst J
  exact ⟨asIso (idealPullbackHom f I), idealPullbackHom_inclusion f I⟩

end HodgeLean.Foundations.Curves.Picard.LineBundles
