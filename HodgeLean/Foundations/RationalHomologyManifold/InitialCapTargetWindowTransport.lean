import HodgeLean.Foundations.RationalHomologyManifold.InitialCapTargetWindow

/-! Actual initial cap windows with an explicitly specified total degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Retain the original initial cap window in a specified equal total degree, transporting only the incoming top chain before its boundary quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual degree transport at the good-truncation boundary.
HC no distance; AV milestone no distance.
-/
def initialCapTargetWindowComparisonOfEq (X : TopCat.{0}) (N q : ℕ) (hN : N = q + 2) :
    (subdivisionLimitSheafComplex X).sc' (q + 2) (q + 1) q ⟶
      (capTargetComplex X N).sc' 0 1 2 where
  τ₁ := -(((subdivisionLimitSheafComplex X).XIsoOfEq hN).inv ≫
    (subdivisionLimitSheafComplex X).pOpcycles N ≫ (capTargetZeroTermIso X N).inv)
  τ₂ := (capTargetTermIso X N 1 (q + 1) (by omega) (by omega)).inv
  τ₃ := (capTargetTermIso X N 2 q (by omega) (by omega)).inv
  comm₁₂ := by
    subst N
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, Category.id_comp]
    exact (initialCapTargetWindowComparison X q).comm₁₂
  comm₂₃ := by
    subst N
    exact (initialCapTargetWindowComparison X q).comm₂₃

#print axioms initialCapTargetWindowComparisonOfEq
end HodgeLean.Foundations.RationalHomologyManifold
