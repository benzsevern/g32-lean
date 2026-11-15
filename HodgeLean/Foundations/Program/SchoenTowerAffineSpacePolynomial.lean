import HodgeLean.Foundations.Program.SchoenTowerAffineSpaceHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The actual global sections of complex affine space are its coordinate polynomial
algebra, with the specified structure-map scalar action. -/
def s2t_affineSpacePolynomialEquiv (ι : Type) :
    MvPolynomial ι ℂ ≃ₐ[ℂ]
      Γ((Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)).left, ⊤) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι ℂ))).symm ≪≫
    asIso (AffineSpace.SpecIso ι ↧ℂ).hom.appTop
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  change (AffineSpace.SpecIso ι ↧ℂ).hom.appTop
    ((Scheme.ΓSpecIso ↧(MvPolynomial ι ℂ)).inv (MvPolynomial.C c)) =
      (complexAffineSpace ι ↘ Spec ↧ℂ).appLE ⊤ ⊤ (by simp)
        ((Scheme.ΓSpecIso ↧ℂ).inv c)
  rw [SpecIso_hom_appTop_C]
  simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id]
  rw [(complexAffineSpace ι).presheaf.map_id, Category.comp_id]

end HodgeLean.Foundations.Program
