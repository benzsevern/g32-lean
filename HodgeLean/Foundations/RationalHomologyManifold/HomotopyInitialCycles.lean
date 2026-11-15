import Mathlib.Algebra.Homology.Homotopy

/-! Equality on actual initial cocycles under a natural-degree cochain homotopy.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Homotopic maps of natural-degree cochain complexes agree literally on every degree-zero cocycle morphism.
Source: Weibel, An Introduction to Homological Algebra, section 1.4; the homotopy equation in the initial degree.
HC no distance; AV milestone no distance.
-/
theorem homotopy_initial_cocycles {C : Type*} [Category* C] [Preadditive C]
    {A B : CochainComplex C ℕ} {f g : A ⟶ B} (h : Homotopy f g)
    {S : C} (u : S ⟶ A.X 0) (hu : u ≫ A.d 0 1 = 0) :
    u ≫ f.f 0 = u ≫ g.f 0 := by
  rw [h.comm 0, Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
    add_zero, Preadditive.comp_add, ← Category.assoc, hu, zero_comp, zero_add]

#print axioms homotopy_initial_cocycles
end HodgeLean.Foundations.RationalHomologyManifold
