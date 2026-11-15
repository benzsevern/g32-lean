import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # Inverse structure-unit comparisons for original composed point maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The inverse point-unit map is preserved by the actual pullback-composition
and congruence comparisons. -/
theorem pullbackUnit_inverse_composition_congr
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (h : f ≫ g = p) :
    (pullbackUnit f).inv ≫ (Scheme.Modules.pullback f).map (pullbackUnit g).inv ≫
      ((Scheme.Modules.pullbackComp f g).app (unit Z)).hom ≫
      ((Scheme.Modules.pullbackCongr h).app (unit Z)).hom = (pullbackUnit p).inv := by
  apply (cancel_mono (pullbackUnit p).hom).mp
  simp only [Category.assoc]
  rw [pullbackUnit_congr h, ← pullbackUnit_composition_hom f g,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, (Scheme.Modules.pullback f).map_id,
    Category.id_comp]
  simp only [Iso.inv_hom_id]

#print axioms pullbackUnit_inverse_composition_congr
end HodgeLean.Foundations.Program.G32Native
