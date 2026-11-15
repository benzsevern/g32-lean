import HodgeLean.Foundations.Program.SchoenCycleComplexSectionTower
import Mathlib.RingTheory.Adjoin.Tower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Affine sections of a complex scheme locally of finite type have the actual finite-type complex algebra structure.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_complex_affine_sections_finiteType
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    letI := s2e_step1_sectionAlgebra X U
    Algebra.FiniteType ℂ Γ(X.left, U) := by
  letI := s2e_step1_sectionAlgebra X U
  have hf := X.hom.finiteType_appLE (isAffineOpen_top (Spec ↧ℂ)) hU le_top
  have hi : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom :=
    ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).mp inferInstance).2
  exact hf.comp (RingHom.FiniteType.of_surjective _ hi)

#print axioms s2e_complex_affine_sections_finiteType
end HodgeLean.Foundations.Program
