import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveSmooth
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

/-! # Instances transported through the retained projective model -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Smoothness uses the supplied projective-model isomorphism. -/
theorem projective_model_smooth (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    Smooth Q.hom := by
  letI := s0_projective_space_smooth k (Spec ↧ℂ)
  rw [← Over.w eQ.hom]
  change Smooth (eQ.hom.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  infer_instance

/-- Projectivity uses that same isomorphism. -/
theorem projective_model_projective (Q : Over (Spec ↧ℂ)) (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    IsProjective Q.hom := by
  exact ⟨⟨{ ambientDimension := k,
             immersion := eQ.hom.left,
             immersion_toBase := Over.w eQ.hom }⟩⟩

#print axioms projective_model_smooth
#print axioms projective_model_projective
end HodgeLean.Foundations.Program.G32Native
