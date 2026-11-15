import HodgeLean.Foundations.Program.SchoenCycleComplexAffineFiniteType

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite type of the actual complex affine section algebras detects local finite type of the structural morphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_locallyOfFiniteType_of_complex_affine_sections
    (X : Over (Spec ↧ℂ))
    (H : ∀ (U : X.left.Opens) (_ : IsAffineOpen U),
      letI := s2e_step1_sectionAlgebra X U
      Algebra.FiniteType ℂ Γ(X.left, U)) : LocallyOfFiniteType X.hom := by
  constructor
  intro U hU V hV hVU
  let Y : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
  let f : X ⟶ Y := Over.homMk X.hom (by simp [Y])
  letI : Algebra ℂ Γ((Spec ↧ℂ), U) := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X V
  letI : Algebra Γ((Spec ↧ℂ), U) Γ(X.left, V) := (X.hom.appLE U V hVU).hom.toAlgebra
  letI : IsScalarTower ℂ Γ((Spec ↧ℂ), U) Γ(X.left, V) := s2e_complex_section_pullback_tower X Y f U V hVU
  haveI : Algebra.FiniteType ℂ Γ(X.left, V) := H V hV
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ Γ((Spec ↧ℂ), U) Γ(X.left, V)

#print axioms s2e_locallyOfFiniteType_of_complex_affine_sections
end HodgeLean.Foundations.Program
