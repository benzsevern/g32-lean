import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullback
import HodgeLean.Foundations.Curves.Picard.LineBundles.AdjunctionComparison

/-! # Composition of structure-module pullback comparisons

The coefficient maps compose as the actual scheme structure-ring maps.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The actual coefficient maps respect scheme composition. -/
theorem pushforwardUnit_composition {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardUnit g ≫ (Scheme.Modules.pushforward g).map (pushforwardUnit f) ≫
      ((Scheme.Modules.pushforwardComp f g).app (unit X)).hom = pushforwardUnit (f ≫ g) := by
  ext U s
  rfl

/-- The actual pullback structure-module comparisons respect composition. -/
theorem pullbackUnit_composition {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((Scheme.Modules.pullbackComp f g).app (unit Z)).inv ≫
        (Scheme.Modules.pullback f).map (pullbackUnit g).hom ≫ (pullbackUnit f).hom =
      (pullbackUnit (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_adjunct, pullbackUnit_adjunct]
  change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map (pullbackUnit g).hom ≫ (pullbackUnit f).hom)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, pullbackUnit_adjunct,
    Adjunction.homEquiv_naturality_right, pullbackUnit_adjunct]
  exact pushforwardUnit_composition f g

end HodgeLean.Foundations.Curves.Picard.LineBundles
