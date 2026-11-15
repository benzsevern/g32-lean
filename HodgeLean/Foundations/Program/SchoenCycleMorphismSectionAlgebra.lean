import HodgeLean.Foundations.Program.SchoenCycleAffineCoordinateRestriction

/-! # Scalar-compatible pullback on actual section rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Pullback along an actual complex scheme morphism is a complex algebra homomorphism on the stated opens.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
def s2e_morphismSectionAlgHom
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (V : Y.left.Opens) (W : X.left.Opens)
    (hWV : W ≤ f.left ⁻¹ᵁ V) :
    letI := s2e_step1_sectionAlgebra Y V
    letI := s2e_step1_sectionAlgebra X W
    Γ(Y.left, V) →ₐ[ℂ] Γ(X.left, W) := by
  letI := s2e_step1_sectionAlgebra Y V
  letI := s2e_step1_sectionAlgebra X W
  refine ⟨(f.left.appLE V W hWV).hom, ?_⟩
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      Y.hom.appLE ⊤ V le_top ≫ f.left.appLE V W hWV =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W le_top := by
    rw [Scheme.Hom.appLE_comp_appLE, Over.w f]
  exact congrArg (fun F : CommRingCat.of ℂ ⟶ Γ(X.left, W) => F.hom c) he

example (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (V : Y.left.Opens) (W : X.left.Opens)
    (hWV : W ≤ f.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    s2e_morphismSectionAlgHom X Y f V W hWV s = f.left.appLE V W hWV s := rfl

end HodgeLean.Foundations.Program
