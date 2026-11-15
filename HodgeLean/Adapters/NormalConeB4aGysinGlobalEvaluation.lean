import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- A global constant pulled back from the base evaluates to that constant. -/
theorem a3b4a_gysin_evaluate_global_constant
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ))
    (w : ComplexPoint (Over.mk q)) (c : ℂ) :
    Point.evaluate (X := Over.mk q) ⊤
      (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) w = c := by
  have hwq : w.left ≫ q = 𝟙 (Spec (CommRingCat.of ℂ)) := w.w
  have hcomp : q.appTop ≫ w.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hwq, Scheme.Hom.id_appTop]
  rw [ComplexPoint.evaluate_top_eq_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((q.appTop ≫ w.left.appTop) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = c
  rw [hcomp]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = c
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply c

end HodgeLean.Adapters
