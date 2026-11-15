import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Sections on an actual ambient open identify with global sections on its open scheme over the native complex scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_open_top_section_equiv
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) :
    let Y := ComplexPoint.openScheme X V
    letI := s2e_step1_sectionAlgebra X V
    letI := s2e_step1_sectionAlgebra Y ⊤
    Γ(X.left, V) ≃ₐ[ℂ] Γ(Y.left, ⊤) := by
  let Y := ComplexPoint.openScheme X V
  letI := s2e_step1_sectionAlgebra X V
  letI := s2e_step1_sectionAlgebra Y ⊤
  refine { V.topIso.symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V le_top ≫ V.topIso.inv =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (V.ι ≫ X.hom).appTop := by
    apply (cancel_mono V.topIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.Hom.comp_appTop]
    rw [Scheme.Opens.ι_appTop_topIso_hom]
    rfl
  convert congrArg (fun f : CommRingCat.of ℂ ⟶ Γ(V.toScheme, ⊤) => f.hom c) he using 1
  · rfl
  · rfl
  · change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (V.ι ≫ X.hom).appLE ⊤ ⊤ le_top).hom c) = _
    have htop : (V.ι ≫ X.hom).appLE ⊤ ⊤ le_top = (V.ι ≫ X.hom).appTop := by
      convert (Scheme.Hom.app_eq_appLE (V.ι ≫ X.hom) (U := ⊤)).symm using 1 <;> rfl
    exact congrArg (fun m : Γ(Spec (CommRingCat.of ℂ), ⊤) ⟶ Γ(V.toScheme, ⊤) =>
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ m).hom c) htop

#print axioms s2e_complex_open_top_section_equiv
end HodgeLean.Foundations.Program
