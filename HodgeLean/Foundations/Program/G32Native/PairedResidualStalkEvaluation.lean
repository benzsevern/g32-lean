import HodgeLean.Foundations.Program.SchoenCycleComplexAffineGerm
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation

/-! # The original complex evaluation through the actual section-to-stalk map -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The original section evaluation is the actual stalk augmentation after
the actual section germ homomorphism.
Source: Hartshorne, Algebraic Geometry, II.2. -/
theorem residual_stalk_section_evaluation
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (p : ComplexPoint X) (W : X.left.Opens) (hpW : p.underlying ∈ W) :
    letI := s2e_step1_sectionAlgebra X W
    letI : Algebra ℂ (X.left.presheaf.stalk p.underlying) :=
      (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    (s2e_complex_point_augmentation X p).comp
      (s2e_complex_section_germ X W p.underlying hpW) =
        s2e_step1_pointEvaluation X W p (s2e_step1_point_preimage X p W hpW) := by
  letI := s2e_step1_sectionAlgebra X W
  letI : Algebra ℂ (X.left.presheaf.stalk p.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  ext a
  have he := s2e_regular_evaluation_eq_pointEvaluation X W p hpW
    (s2e_step1_point_preimage X p W hpW) a
  rw [Point.evaluate, dif_pos hpW] at he
  exact he

#print axioms residual_stalk_section_evaluation
end HodgeLean.Foundations.Program.G32Native
