import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullbackComposition

/-! # Composition for unit-valued module maps

The literal module comparison transports a pulled-back coefficient morphism.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Unit-valued module maps pull back compatibly with composition. -/
theorem unitValuedPullback_composition {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (h : M ⟶ unit Z) :
    ((Scheme.Modules.pullbackComp f g).app M).inv ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback g).map h ≫ (pullbackUnit g).hom) ≫
        (pullbackUnit f).hom =
      (Scheme.Modules.pullback (f ≫ g)).map h ≫ (pullbackUnit (f ≫ g)).hom := by
  rw [Functor.map_comp]
  have hn := (Scheme.Modules.pullbackComp f g).inv.naturality h
  change (Scheme.Modules.pullback (f ≫ g)).map h ≫
      ((Scheme.Modules.pullbackComp f g).app (unit Z)).inv =
      ((Scheme.Modules.pullbackComp f g).app M).inv ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map h) at hn
  calc
    _ = (((Scheme.Modules.pullbackComp f g).app M).inv ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map h)) ≫
        ((Scheme.Modules.pullback f).map (pullbackUnit g).hom ≫ (pullbackUnit f).hom) := by
      simp only [Category.assoc]
    _ = ((Scheme.Modules.pullback (f ≫ g)).map h ≫
        ((Scheme.Modules.pullbackComp f g).app (unit Z)).inv) ≫
        ((Scheme.Modules.pullback f).map (pullbackUnit g).hom ≫ (pullbackUnit f).hom) := by
      rw [← hn]
    _ = _ := by rw [Category.assoc, pullbackUnit_composition]

end HodgeLean.Foundations.Curves.Picard.LineBundles
