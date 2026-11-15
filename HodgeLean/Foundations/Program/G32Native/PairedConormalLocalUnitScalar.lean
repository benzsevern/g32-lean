import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalUnitSpecialization
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
/-! # Actual scalar evaluation of local structure-module sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
open HodgeLean.Foundations.BundleThom

/-- The specialized actual unit-section scalar is the regular value of its
literal original coefficient, with both canonical unit comparisons retained. -/
theorem conormal_local_unit_section_scalar {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit Q.left.ringCatSheaf))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((i1_localModuleSectionSpecialization (SheafOfModules.unit Q.left.ringCatSheaf)
        U s x hx ≫ (pullbackUnit x.left).hom).val.app (Opposite.op ⊤)
          (1 : Γ(Spec ↧ℂ, ⊤))) =
    Point.evaluate U (U.topIso.hom ((s ≫ (pullbackUnit U.ι).hom).val.app
      (Opposite.op ⊤) (1 : Γ(U.toScheme, ⊤)))) x := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let t := s ≫ (pullbackUnit U.ι).hom
  let r := U.topIso.hom (t.val.app (Opposite.op ⊤) (1 : Γ(U.toScheme, ⊤)))
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  have hp := i1_unitPullback_endomorphism_apply a t ⊤
  change ((pullbackUnit a).inv ≫ (Scheme.Modules.pullback a).map t ≫
      (pullbackUnit a).hom).val.app (Opposite.op ⊤) (1 : Γ(Spec ↧ℂ, ⊤)) =
    a.appTop (t.val.app (Opposite.op ⊤) (1 : Γ(U.toScheme, ⊤))) at hp
  have hp' := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z) hp
  have htop : (⊤ : (Spec ↧ℂ).Opens) ≤ x.left ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem x.left hx).ge
  have hc := ConcreteCategory.congr_hom (conormal_open_lift_section_map U x hx htop) r
  have hcancel : U.topIso.inv r = t.val.app (Opposite.op ⊤) (1 : Γ(U.toScheme, ⊤)) :=
    U.topIso.hom_inv_id_apply _
  change a.appTop (U.topIso.inv r) = x.left.appLE U ⊤ htop r at hc
  rw [hcancel] at hc
  have hr := conormal_regular_evaluation_eq_appLE U r x htop
  rw [conormal_local_unit_section_specialization]
  exact hp'.trans ((congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom z) hc).trans hr.symm)

end HodgeLean.Foundations.Program.G32Native
