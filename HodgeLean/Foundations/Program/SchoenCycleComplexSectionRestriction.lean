import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual restriction of regular sections preserves the prescribed complex scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.1–II.2. -/
def s2e_complex_section_restriction
    (X : Over (Spec ↧ℂ)) (U V : X.left.Opens) (hVU : V ≤ U) :
    letI := s2e_step1_sectionAlgebra X U
    letI := s2e_step1_sectionAlgebra X V
    Γ(X.left, U) →ₐ[ℂ] Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra X U
  letI := s2e_step1_sectionAlgebra X V
  refine ⟨(X.left.presheaf.map (homOfLE hVU).op).hom, ?_⟩
  have he : X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.map (homOfLE hVU).op =
      X.hom.appLE ⊤ V le_top := by
    dsimp only [Scheme.Hom.appLE]
    rw [Category.assoc, ← X.left.presheaf.map_comp]
    rfl
  intro c
  change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top) ≫
    X.left.presheaf.map (homOfLE hVU).op).hom c = _
  rw [Category.assoc, he]
  rfl

#print axioms s2e_complex_section_restriction
end HodgeLean.Foundations.Program
