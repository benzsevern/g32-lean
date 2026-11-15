import HodgeLean.Foundations.Program.SchoenCycleMorphismSectionAlgebra
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation

/-! # Compatibility of the original section pullback and complex augmentations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The two actual point augmentations commute with the original section map.
Source: Hartshorne, Algebraic Geometry, II.2. -/
theorem residual_section_evaluation_pullback
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (p : ComplexPoint X)
    (V : Y.left.Opens) (W : X.left.Opens)
    (hpW : p.underlying ∈ W) (hpV : (Point.map f p).underlying ∈ V)
    (hWV : W ≤ f.left ⁻¹ᵁ V) :
    letI := s2e_step1_sectionAlgebra X W
    letI := s2e_step1_sectionAlgebra Y V
    (s2e_step1_pointEvaluation X W p (s2e_step1_point_preimage X p W hpW)).comp
      (s2e_morphismSectionAlgHom X Y f V W hWV) =
    s2e_step1_pointEvaluation Y V (Point.map f p)
      (s2e_step1_point_preimage Y (Point.map f p) V hpV) := by
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAlgebra Y V
  ext a
  change s2e_step1_pointEvaluation X W p _
    (s2e_morphismSectionAlgHom X Y f V W hWV a) =
      s2e_step1_pointEvaluation Y V (Point.map f p) _ a
  rw [← s2e_regular_evaluation_eq_pointEvaluation X W p hpW,
    ← s2e_regular_evaluation_eq_pointEvaluation Y V (Point.map f p) hpV]
  exact (Point.evaluate_res hWV (f.left.app V a) p hpW).symm.trans
    (Point.evaluate_map f V a p).symm

#print axioms residual_section_evaluation_pullback
end HodgeLean.Foundations.Program.G32Native
