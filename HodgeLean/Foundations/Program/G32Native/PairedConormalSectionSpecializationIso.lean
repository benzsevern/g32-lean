import HodgeLean.Foundations.BundleThom.LocalSectionSpecializationHelpers
/-! # Detecting actual fibre maps through an invertible local section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.Program.G32Native

/-- An invertible actual local unit section stays invertible at the supplied complex point. -/
theorem conormal_local_section_specialization_isIso {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) [IsIso s]
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    IsIso (i1_localModuleSectionSpecialization M U s x hx) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  change IsIso (inv (SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom) ≫
    (Scheme.Modules.pullback a).map s ≫
      (Scheme.Modules.pullbackComp a U.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).hom.app M)
  infer_instance

/-- An invertible actual local section detects vanishing of the same pulled sheaf map. -/
theorem conormal_local_section_specialization_detects_zero {Q : Over (Spec ↧ℂ)}
    {M N : Q.left.Modules} (φ : M ⟶ N) (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) [IsIso s]
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization N U
      (s ≫ (Scheme.Modules.pullback U.ι).map φ) x hx = 0 ↔
        (Scheme.Modules.pullback x.left).map φ = 0 := by
  letI := conormal_local_section_specialization_isIso M U s x hx
  rw [i1_localModuleSectionSpecialization_naturality]
  constructor
  · intro h
    apply (cancel_epi (i1_localModuleSectionSpecialization M U s x hx)).mp
    simpa only [CategoryTheory.Limits.comp_zero] using h
  · intro h
    rw [h, CategoryTheory.Limits.comp_zero]

end HodgeLean.Foundations.Program.G32Native
