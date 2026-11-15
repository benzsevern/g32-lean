import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual section pullback over the complex base is linear for the specified section scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_section_pullback
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (hV : V ≤ f.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAlgebra Y U
    letI := s2e_step1_sectionAlgebra X V
    Γ(Y.left, U) →ₐ[ℂ] Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra Y U
  letI := s2e_step1_sectionAlgebra X V
  refine ⟨(f.left.appLE U V hV).hom, ?_⟩
  intro c
  have he : Y.hom.appLE ⊤ U le_top ≫ f.left.appLE U V hV = X.hom.appLE ⊤ V le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact Over.w f
  change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appLE ⊤ U le_top) ≫
    f.left.appLE U V hV).hom c = _
  rw [Category.assoc, he]
  rfl

#print axioms s2e_complex_section_pullback
end HodgeLean.Foundations.Program
