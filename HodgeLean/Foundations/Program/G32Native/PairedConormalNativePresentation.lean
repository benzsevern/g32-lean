import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitFreePullback
import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalLinearForms
import HodgeLean.Foundations.BundleThom.ConormalFrameCoefficientHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ConormalSectionAlgebraHelpers
import HodgeLean.Foundations.BundleThom.DualCoordinateEvaluationHelpers
import HodgeLean.Foundations.BundleThom.FreePointProjectionHelpers
import HodgeLean.Foundations.BundleThom.FreeSectionSpecializationHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameContinuityHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameEvaluationHelpers
import HodgeLean.Foundations.BundleThom.LocalSectionRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionPullbackHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionTransportHelpers
import HodgeLean.Foundations.BundleThom.UnitCompositionHelpers
import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers
/-! # The supplied elementary presentation in the native polynomial model -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual retained arrow under the specified ideal and free-module comparisons. -/
def conormalNativeRetainedArrow (k : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)) :
    idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k) :=
  (conormalHyperplanePolynomialIdealIso k).inv ≫
    (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).map b ≫
    (SheafOfModules.pullbackObjFreeIso
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom.toRingCatSheafHom (Fin k)).hom

/-- Each actual retained native row is the original ideal row with its exact unit comparison. -/
theorem conormal_native_retained_arrow_row (k : ℕ)
    (b : idealModule (s2e_hyperplaneIdeal k) ⟶
      (SheafOfModules.free (Fin k) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules))
    (t : Fin k) :
    conormalNativeRetainedArrow k b ≫
      i1_freeSheafProjection (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)) k t =
      conormalOriginalIdealRow k k b t := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  let F := Scheme.Modules.pullback f
  have hp := i1_freeSheafProjection_pullback f k t
  dsimp only [conormalNativeRetainedArrow, conormalOriginalIdealRow]
  rw [Category.assoc, Category.assoc, ← hp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end HodgeLean.Foundations.Program.G32Native
