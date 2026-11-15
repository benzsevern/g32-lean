import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Algebraic coordinates on smaller affine neighbourhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual restriction between section rings respects the complex scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
def s2e_sectionRestrictionAlgHom
    (X : Over (Spec ↧ℂ)) (U V : X.left.Opens) (hVU : V ≤ U) :
    letI := s2e_step1_sectionAlgebra X U
    letI := s2e_step1_sectionAlgebra X V
    Γ(X.left, U) →ₐ[ℂ] Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra X U
  letI := s2e_step1_sectionAlgebra X V
  refine ⟨(X.left.presheaf.map (homOfLE hVU).op).hom, ?_⟩
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.map (homOfLE hVU).op =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V le_top := by
    rw [Scheme.Hom.appLE_map]
  exact congrArg (fun F : CommRingCat.of ℂ ⟶ Γ(X.left, V) => F.hom c) he

example (X : Over (Spec ↧ℂ)) (U V : X.left.Opens) (hVU : V ≤ U)
    (s : Γ(X.left, U)) :
    s2e_sectionRestrictionAlgHom X U V hVU s =
      X.left.presheaf.map (homOfLE hVU).op s := rfl

/-- Restriction between actual affine section rings is etale.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.3 and II.8. -/
theorem s2e_affine_section_restriction_etale
    (X : Over (Spec ↧ℂ)) (U V : X.left.affineOpens) (hVU : V ≤ U) :
    letI := s2e_step1_sectionAlgebra X U.1
    letI := s2e_step1_sectionAlgebra X V.1
    (s2e_sectionRestrictionAlgHom X U.1 V.1 hVU).toRingHom.Etale := by
  have h := (𝟙 X.left : X.left ⟶ X.left).etale_appLE U.2 V.2
    (show V.1 ≤ (𝟙 X.left : X.left ⟶ X.left) ⁻¹ᵁ U.1 from hVU)
  change (X.left.presheaf.map (homOfLE (show V.1 ≤ U.1 from hVU)).op).hom.Etale
  simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using h

end HodgeLean.Foundations.Program
