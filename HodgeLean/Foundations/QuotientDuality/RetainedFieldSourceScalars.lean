import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChart
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericFieldFactor

/-! Scalar compatibility of actual original-field charts with the retained generic field embedding. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem fieldSourceChart_scalar_eq_generic
    (X : Scheme) [IsIntegral X] {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ X) (κ : X.functionField →+* L)
    (hκ : Spec.map (CommRingCat.ofHom κ) ≫ X.fromSpecStalk (genericPoint X) = η)
    (U : X.affineOpens) [Nonempty U.1] (hU : η ⁻¹ᵁ U.1 = ⊤) :
    (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom =
      κ.comp (X.germToFunctionField U.1).hom := by
  have H := s2v_i2a_generic_field_coefficients X η κ hκ U.1 hU.ge
  have heq : η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom =
      η.appLE U.1 ⊤ hU.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    dsimp [s2v_fieldSourceSectionsIso, Scheme.Hom.appLE]
    rfl
  rw [← heq] at H
  exact H.symm

#print axioms fieldSourceChart_scalar_eq_generic
end HodgeLean.Foundations.QuotientDuality
