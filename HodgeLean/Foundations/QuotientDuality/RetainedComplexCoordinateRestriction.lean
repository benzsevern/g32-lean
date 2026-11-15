import HodgeLean.Foundations.QuotientDuality.RetainedAffineCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1bAffineGeneratorRefinement

/-! Restriction of actual complex polynomial coordinates to smaller affine opens. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

theorem complex_affine_coordinate_restriction
    (X : Over (Spec ↧ℂ)) (U V : X.left.affineOpens) (hV : V.1 ≤ U.1)
    {ι : Type} (z : ι → Γ(X.left, U))
    (hEt : (MvPolynomial.eval₂Hom (complexAffineCoefficient X U) z).Etale) :
    (MvPolynomial.eval₂Hom (complexAffineCoefficient X V)
      (fun j => (X.left.presheaf.map (homOfLE hV).op).hom (z j))).Etale := by
  let r := (X.left.presheaf.map (homOfLE hV).op).hom
  have hr : r.Etale := by
    have H := HasRingHomProperty.appLE (P := @Etale) (𝟙 X.left) inferInstance U V
      (show V.1 ≤ (𝟙 X.left) ⁻¹ᵁ U.1 from hV)
    simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using H
  have hc : r.comp (complexAffineCoefficient X U) = complexAffineCoefficient X V := by
    have H := complexAffineCoefficient_pullback X X (𝟙 X) U V hV
    simpa only [Over.id_left, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using H
  have heq := MvPolynomial.comp_eval₂Hom (complexAffineCoefficient X U) z r
  rw [hc] at heq
  rw [← heq]
  exact RingHom.Etale.stableUnderComposition _ _ hEt hr

#print axioms complex_affine_coordinate_restriction
end HodgeLean.Foundations.QuotientDuality
