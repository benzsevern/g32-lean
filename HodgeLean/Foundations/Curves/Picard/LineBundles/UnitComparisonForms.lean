import HodgeLean.Foundations.Curves.Picard.LineBundles.OpenUnitCoherence
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitPullbackComposition

/-! # Convenient forms of actual unit comparisons

These formulas express the canonical comparisons in their forward orientations.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The forward open comparison carries the actual pullback structure-module map. -/
theorem restrictPullback_unit_hom {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictUnitIso f).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback f).app (unit Y)).hom ≫ (pullbackUnit f).hom := by
  rw [← restrictPullback_unit f, Iso.hom_inv_id_assoc]

/-- The forward pullback composition comparison preserves the actual unit map. -/
theorem pullbackUnit_composition_hom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullback f).map (pullbackUnit g).hom ≫ (pullbackUnit f).hom =
      ((Scheme.Modules.pullbackComp f g).app (unit Z)).hom ≫ (pullbackUnit (f ≫ g)).hom := by
  rw [← pullbackUnit_composition f g, Iso.hom_inv_id_assoc]

/-- Congruent scheme morphisms have the same actual pullback structure-module map. -/
theorem pullbackUnit_congr {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) :
    ((Scheme.Modules.pullbackCongr h).app (unit Y)).hom ≫ (pullbackUnit g).hom =
      (pullbackUnit f).hom := by
  cases h
  change (𝟙 _) ≫ (pullbackUnit f).hom = (pullbackUnit f).hom
  exact Category.id_comp _

end HodgeLean.Foundations.Curves.Picard.LineBundles
