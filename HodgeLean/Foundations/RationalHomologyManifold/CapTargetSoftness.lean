import HodgeLean.Foundations.RationalHomologyManifold.CapTargetComplex

/-! Softness of the actual signed and regraded orientation model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every term of the actual cap target is soft on the compact finite triangulated oriented space.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10 and VI.12; the bounded soft orientation model.
HC no distance; AV milestone no distance.
-/
theorem capTargetComplex_term_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1)) (p : ℕ) :
    IsSoft ((capTargetComplex X (n + 1)).X p) := by
  change IsSoft ((subdivisionTruncatedSheafComplex X (n + 1)).X
    ((p : ℤ) + -((n + 1 : ℕ) : ℤ)))
  exact subdivisionTruncatedSheafComplex_isSoft X t n o _

#print axioms capTargetComplex_term_isSoft
end HodgeLean.Foundations.RationalHomologyManifold
