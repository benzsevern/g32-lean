import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction
import HodgeLean.Foundations.Curves.CurvePoints

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual section germ map preserves the prescribed complex scalar structures on sections and stalks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_section_germ
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (U : X.left.Opens) (p : X.left) (hp : p ∈ U) :
    letI := s2e_step1_sectionAlgebra X U
    letI : Algebra ℂ (X.left.presheaf.stalk p) :=
      (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    Γ(X.left, U) →ₐ[ℂ] X.left.presheaf.stalk p := by
  letI := s2e_step1_sectionAlgebra X U
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  refine ⟨(X.left.presheaf.germ U p hp).hom, ?_⟩
  intro c
  have he : X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.germ U p hp =
      X.hom.appLE ⊤ ⊤ le_top ≫ X.left.presheaf.germ ⊤ p trivial := by
    dsimp only [Scheme.Hom.appLE]
    rw [Category.assoc, TopCat.Presheaf.germ_res, Category.assoc, TopCat.Presheaf.germ_res]
  change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U le_top) ≫
      X.left.presheaf.germ U p hp).hom c = _
  rw [Category.assoc, he]
  change _ = HodgeLean.Foundations.Curves.stalkC p c
  rfl

#print axioms s2e_complex_section_germ
end HodgeLean.Foundations.Program
