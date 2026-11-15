import HodgeLean.Foundations.Program.G32Native.PairedConormalNativePresentation
import HodgeLean.Foundations.Program.G32Native.PairedConormalDistinguishedCoordinate
import HodgeLean.Foundations.Program.G32Native.PairedConormalRelationQuotientPullback

/-! # The actual native relation annihilates the supplied transported quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized native relation retains the actual original quotient's zero composition. -/
theorem conormal_native_quotient_relation_zero (k : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (M : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (π : (SheafOfModules.unit (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf ⊞
      SheafOfModules.free (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf)
        (Fin k)) ⟶ M)
    (hπ : HodgeLean.Foundations.NormalPresentation.relation
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) b ≫ π = 0) :
    HodgeLean.Foundations.NormalPresentation.relation
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom))
      (conormalNativeRetainedArrow k b) ≫
        conormalPresentationPullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
          k M π = 0 := by
  simpa only [conormalHyperplanePolynomialIdealIso_inv_inclusion,
    conormalNativeRetainedArrow] using
      (conormal_relation_quotient_pullback
        (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom k
        (conormalHyperplanePolynomialIdealIso k).inv
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (s2e_hyperplaneIdeal k).subschemeι.toRingCatSheafHom)) b M π hπ)

#print axioms conormal_native_quotient_relation_zero
end HodgeLean.Foundations.Program.G32Native
