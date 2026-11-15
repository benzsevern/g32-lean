import HodgeLean.Foundations.Program.SchoenCycleComplexStalkPullback
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual complex geometric stalk pullback induces its canonical map on maximal-ideal formal coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
def s2e_formal_stalk_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (x : X.left) :
    letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
      (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
    AdicCompletion (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (f.left x)))
      (Y.left.presheaf.stalk (f.left x)) →ₐ[ℂ]
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x)) (X.left.presheaf.stalk x) := by
  letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
    (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
  exact s2e_adic_algebra_map _ _ (s2e_complex_stalk_pullback X Y f x)
    (s2e_complex_stalk_pullback_preserves_powers X Y f x)

#print axioms s2e_formal_stalk_pullback
end HodgeLean.Foundations.Program
