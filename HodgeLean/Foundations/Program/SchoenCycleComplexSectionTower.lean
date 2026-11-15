import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual section-ring extension of a complex scheme morphism has the prescribed complex scalar tower.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_section_pullback_tower
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (hV : V ≤ f.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X V
    letI : Algebra Γ(Y.left, U) Γ(X.left, V) := (f.left.appLE U V hV).hom.toAlgebra
    IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X V
  letI : Algebra Γ(Y.left, U) Γ(X.left, V) := (f.left.appLE U V hV).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  exact ((s2e_complex_section_pullback X Y f U V hV).commutes c).symm

/-- Pullback on the full inverse-image open gives the same actual complex scalar tower.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_section_app_tower
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens) :
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X (f.left ⁻¹ᵁ U)
    letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
    IsScalarTower ℂ Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := by
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X (f.left ⁻¹ᵁ U)
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  have h := (s2e_complex_section_pullback X Y f U (f.left ⁻¹ᵁ U) le_rfl).commutes c
  change (f.left.appLE U (f.left ⁻¹ᵁ U) le_rfl).hom _ = _ at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h.symm

#print axioms s2e_complex_section_app_tower
#print axioms s2e_complex_section_pullback_tower
end HodgeLean.Foundations.Program
