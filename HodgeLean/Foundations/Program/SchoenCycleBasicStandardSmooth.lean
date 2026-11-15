import HodgeLean.Foundations.Program.SchoenCycleComplexSectionRestriction
import Mathlib.RingTheory.Smooth.StandardSmooth

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Standard smooth affine coordinates retain their relative dimension on an actual basic open with its prescribed complex scalars.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_basicOpen_standardSmooth_dimension
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    letI := s2e_step1_sectionAlgebra X U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X.left, U)] (f : Γ(X.left, U)),
      letI := s2e_step1_sectionAlgebra X (X.left.basicOpen f)
      Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X.left, X.left.basicOpen f) := by
  letI := s2e_step1_sectionAlgebra X U
  intro h f
  letI := s2e_step1_sectionAlgebra X (X.left.basicOpen f)
  letI : IsScalarTower ℂ Γ(X.left, U) Γ(X.left, X.left.basicOpen f) :=
    IsScalarTower.of_algebraMap_eq (fun c =>
      ((s2e_complex_section_restriction X U (X.left.basicOpen f) (X.left.basicOpen_le f)).commutes c).symm)
  letI : IsLocalization.Away f Γ(X.left, X.left.basicOpen f) := hU.isLocalization_basicOpen f
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 Γ(X.left, U) Γ(X.left, X.left.basicOpen f) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away f
  simpa only [zero_add] using Algebra.IsStandardSmoothOfRelativeDimension.trans
    n 0 ℂ Γ(X.left, U) Γ(X.left, X.left.basicOpen f)

#print axioms s2e_basicOpen_standardSmooth_dimension
end HodgeLean.Foundations.Program
