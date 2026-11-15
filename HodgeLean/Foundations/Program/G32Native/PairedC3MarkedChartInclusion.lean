import HodgeLean.Foundations.Program.G32Native.PairedC3RulingDescent

/-! # Passing marked affine squares through the target chart inclusion -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An affine marked square remains a pullback after including its target
chart. This retains the original intersection object and both source maps. -/
theorem pairedC3_marked_square_chart_inclusion
    {D T X A C : Scheme} (a : D ⟶ T) (b : D ⟶ X)
    (c : T ⟶ A) (f : X ⟶ A) (j : A ⟶ C) [Mono j]
    (h : IsPullback a b c f) : IsPullback a b (c ≫ j) (f ≫ j) := by
  have hj : IsPullback f (𝟙 X) j (f ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.comp_id] using h.paste_vert hj

#print axioms pairedC3_marked_square_chart_inclusion
end HodgeLean.Foundations.Program.G32Native
