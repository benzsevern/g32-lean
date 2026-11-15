import HodgeLean.Foundations.Program.G32Native.IdealTargetInclusion
import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # Original ideal inclusions on an ambient open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual restriction of the kernel ideal retains the original ideal
inclusion and the specified restricted structure module. -/
theorem idealOpenRestriction_inclusion {Q W : Scheme.{0}} (i : Q ⟶ W) (U : W.Opens) :
    (s2e_idealModule_restrict_iso i U).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ∣_ U).toRingCatSheafHom) =
    (Scheme.Modules.restrictFunctor U.ι).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom := by
  simp only [s2e_idealModule_restrict_iso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι]
  rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The actual ambient open pullback comparison retains the original
ideal inclusion with its specified structure-module pullback map. -/
theorem idealOpenPullback_inclusion {Q W : Scheme.{0}} (i : Q ⟶ W) (U : W.Opens) :
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (Conormal.idealModule i)) ≪≫
      s2e_idealModule_restrict_iso i U).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ∣_ U).toRingCatSheafHom) =
    (Scheme.Modules.pullback U.ι).map
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ≫
      (pullbackUnit U.ι).hom := by
  let jI := kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let α := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hn := α.inv.naturality jI
  change (Scheme.Modules.pullback U.ι).map jI ≫ (α.app (unit W)).inv =
    (α.app (Conormal.idealModule i)).inv ≫ (Scheme.Modules.restrictFunctor U.ι).map jI at hn
  change (α.app (Conormal.idealModule i)).inv ≫
    (s2e_idealModule_restrict_iso i U).hom ≫
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (i ∣_ U).toRingCatSheafHom) = _
  rw [idealOpenRestriction_inclusion, ← reassoc_of% hn, restrictPullback_unit]

#print axioms idealOpenPullback_inclusion
#print axioms idealOpenRestriction_inclusion
end HodgeLean.Foundations.Program.G32Native
