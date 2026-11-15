import HodgeLean.Adapters.NormalConeB4aGysinAffinePointHomeomorph

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- Restricting a point to an open subscheme preserves evaluation of sections. -/
theorem a3b4a_gysin_open_top_evaluation
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens)
    (s : Γ(X, U)) (z : ComplexPoint (ComplexPoint.openScheme (Over.mk q) U)) :
    Point.evaluate U s (Point.map (ComplexPoint.openInclusion (Over.mk q) U) z) =
      Point.evaluate ⊤ (U.topIso.inv s) z := by
  have h := ComplexPoint.evaluate_openEquiv (X := Over.mk q) U (U.topIso.inv s) z
  rw [Scheme.Opens.ι_appIso] at h
  have he := ComplexPoint.evaluate_eq (Y := Over.mk q) U.ι_image_top.symm s
    (Point.map (ComplexPoint.openInclusion (Over.mk q) U) z)
  exact he.trans h

end HodgeLean.Adapters
