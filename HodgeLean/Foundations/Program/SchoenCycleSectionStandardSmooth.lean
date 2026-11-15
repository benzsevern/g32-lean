import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction
import Mathlib.RingTheory.RingHom.StandardSmooth

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Standard smoothness for the prescribed complex section scalars gives standard smoothness for the actual scheme structure map on those sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_section_standardSmooth_dimension
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (n : ℕ) :
    letI := s2e_step1_sectionAlgebra X W
    Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(X.left, W) →
      (X.hom.appLE ⊤ W (by simp)).hom.IsStandardSmoothOfRelativeDimension n := by
  letI := s2e_step1_sectionAlgebra X W
  intro h
  have hs : (algebraMap ℂ Γ(X.left, W)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr h
  have hh := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2
    (algebraMap ℂ Γ(X.left, W)) (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv hs
  have he : (algebraMap ℂ Γ(X.left, W)).comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom =
      (X.hom.appLE ⊤ W (by simp)).hom := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W (by simp))).hom = _
    rw [Iso.hom_inv_id_assoc]
  change RingHom.IsStandardSmoothOfRelativeDimension n
    ((algebraMap ℂ Γ(X.left, W)).comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom) at hh
  rw [he] at hh
  exact hh

#print axioms s2e_section_standardSmooth_dimension
end HodgeLean.Foundations.Program
