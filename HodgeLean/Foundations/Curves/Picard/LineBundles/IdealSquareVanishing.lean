import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitValuedPullback
import HodgeLean.Foundations.Curves.Picard.LineBundles.IdealPullbackVanishing

/-! # Pullback of ideal vanishing through actual scheme squares

The composition comparisons transport the zero restriction to a subscheme.
HC no distance; AV milestone no distance.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Vanishing of a unit-valued map is preserved by an actual commutative square. -/
theorem unitValuedPullback_square_zero {X Y X' Y' : Scheme}
    (f : Y ⟶ X) (j : Y' ⟶ Y) (i : X' ⟶ X) (g : Y' ⟶ X')
    (hsq : j ≫ f = g ≫ i) {M : X.Modules} (m : M ⟶ unit X)
    (hm : (Scheme.Modules.pullback i).map m ≫ (pullbackUnit i).hom = 0) :
    (Scheme.Modules.pullback j).map
        ((Scheme.Modules.pullback f).map m ≫ (pullbackUnit f).hom) ≫
      (pullbackUnit j).hom = 0 := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp j f).app M).inv).mp
  rw [comp_zero, unitValuedPullback_composition, hsq,
    ← unitValuedPullback_composition g i m, hm, Functor.map_zero, zero_comp, comp_zero]

end HodgeLean.Foundations.Curves.Picard.LineBundles
