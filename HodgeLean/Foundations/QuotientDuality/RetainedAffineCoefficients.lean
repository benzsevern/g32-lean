import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepOffCentre

/-! Actual complex coefficient maps on affine opens and their retained pullbacks. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

def complexAffineCoefficient (X : Over (Spec ↧ℂ)) (U : X.left.affineOpens) :
    ℂ →+* Γ(X.left, U) :=
  (X.hom.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

theorem complexAffineCoefficient_pullback
    (B X : Over (Spec ↧ℂ)) (f : X ⟶ B)
    (U : B.left.affineOpens) (V : X.left.affineOpens)
    (hV : V.1 ≤ f.left ⁻¹ᵁ U.1) :
    (f.left.appLE U.1 V.1 hV).hom.comp (complexAffineCoefficient B U) =
      complexAffineCoefficient X V := by
  ext t
  change ((B.hom.appLE ⊤ U.1 le_top) ≫ f.left.appLE U.1 V.1 hV)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv t) = _
  rw [Scheme.Hom.appLE_comp_appLE, Over.w f]
  rfl

#print axioms complexAffineCoefficient
#print axioms complexAffineCoefficient_pullback
end HodgeLean.Foundations.QuotientDuality
