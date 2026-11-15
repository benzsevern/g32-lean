import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! The actual image of an open immersion as an open complex subscheme. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

def openImmersionImageIso
    {A X : Over (Spec ↧ℂ)} (j : A ⟶ X) [IsOpenImmersion j.left] :
    A ≅ openScheme X j.left.opensRange := by
  have hrange : Set.range j.left = Set.range j.left.opensRange.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let E := IsOpenImmersion.isoOfRangeEq j.left j.left.opensRange.ι hrange
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac j.left j.left.opensRange.ι hrange
  refine Over.isoMk E ?_
  change E.hom ≫ (j.left.opensRange.ι ≫ X.hom) = A.hom
  rw [← Category.assoc, hfac, j.w]

#print axioms openImmersionImageIso
end HodgeLean.Foundations.QuotientDuality
