import HodgeLean.Foundations.QuotientDuality.LocalImmersionOrientationFamily

/-! Canonical restriction maps between two open complex subschemes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

def openRestrictionMap (X : Over (Spec ↧ℂ)) {U V : X.left.Opens} (h : U ≤ V) :
    openScheme X U ⟶ openScheme X V :=
  Over.homMk (X.left.homOfLE h) (by
    dsimp only [openScheme, Over.mk_left, Over.mk_hom]
    rw [← Category.assoc, Scheme.homOfLE_ι])

instance openRestrictionMap_isOpenImmersion (X : Over (Spec ↧ℂ))
    {U V : X.left.Opens} (h : U ≤ V) : IsOpenImmersion (openRestrictionMap X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

theorem openRestrictionMap_inclusion (X : Over (Spec ↧ℂ))
    {U V : X.left.Opens} (h : U ≤ V) :
    openRestrictionMap X h ≫ openInclusion X V = openInclusion X U := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

#print axioms openRestrictionMap_inclusion
end HodgeLean.Foundations.QuotientDuality
