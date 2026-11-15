import HodgeLean.Foundations.QuotientDuality.RetainedAffineCoefficients

/-! The coefficient spectrum map is the actual complex structure map of an affine chart. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

theorem complexAffineCoefficient_spec
    (X : Over (Spec ↧ℂ)) (U : X.left.affineOpens) :
    Spec.map (CommRingCat.ofHom (complexAffineCoefficient X U)) = U.2.fromSpec ≫ X.hom := by
  have H := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) U.2 (show U.1 ≤ X.hom ⁻¹ᵁ ⊤ from le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at H
  exact H

#print axioms complexAffineCoefficient_spec
end HodgeLean.Foundations.QuotientDuality
