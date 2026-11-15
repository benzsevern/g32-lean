import HodgeLean.Foundations.Program.SchoenCycleCoordinateEvaluation
import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A complex algebra map into actual global sections defines an actual affine scheme morphism over the original complex base.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_section_defined_affine_map
    (Y : Over (Spec ↧ℂ)) (A : Type) [CommRing A] [Algebra ℂ A] :
    letI := s2e_step1_sectionAlgebra Y ⊤
    (A →ₐ[ℂ] Γ(Y.left, ⊤)) → (Y ⟶ Over.mk (ComplexPoint.affineSpecStructureMap A)) := by
  letI := s2e_step1_sectionAlgebra Y ⊤
  intro G
  refine Over.homMk (Y.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom)) ?_
  change Y.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = Y.hom
  rw [← Spec.map_comp]
  apply ext_to_Spec
  refine (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _).trans ?_
  have hc : CommRingCat.ofHom (algebraMap ℂ A) ≫ CommRingCat.ofHom G.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appLE ⊤ ⊤ le_top :=
    congrArg CommRingCat.ofHom G.comp_algebraMap
  rw [hc]
  congr 1
  convert (Scheme.Hom.app_eq_appLE Y.hom (U := ⊤)).symm using 1 <;> rfl

#print axioms s2e_section_defined_affine_map
end HodgeLean.Foundations.Program
