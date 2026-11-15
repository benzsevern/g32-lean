import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealSections

/-! # The actual coordinate equation vanishes under the original restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual structure-module restriction kills the original homogeneous
ratio because it is the inclusion of a specified actual ideal section. -/
theorem paired_c3_coordinate_ratio_restriction_zero (k : ℕ) (i j : Fin (k + 1)) :
    Scheme.Modules.Hom.app (X := pairedC3Proj k)
      (SheafOfModules.unitToPushforwardObjUnit
        (pairedC3CoordinateHyperplaneIdeal k j).subschemeι.toRingCatSheafHom)
        (ProjSpace.standardOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i j) = 0 := by
  let I := pairedC3CoordinateHyperplaneIdeal k j
  let q := SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom
  let U := ProjSpace.standardOpen ℂ k i
  let s := pairedC3CoordinateIdealStandardSection k i j
  have hk : Scheme.Modules.Hom.app (X := pairedC3Proj k) (kernel.ι q ≫ q) U s = 0 := by
    rw [kernel.condition, Scheme.Modules.Hom.zero_app]
    rfl
  change Scheme.Modules.Hom.app (X := pairedC3Proj k) q U ((kernel.ι q).val.app (op U) s) = 0 at hk
  have hi := paired_c3_coordinate_ideal_standard_section_inclusion k i j
  exact (congrArg (fun a => Scheme.Modules.Hom.app (X := pairedC3Proj k) q U a) hi).symm.trans hk

#print axioms paired_c3_coordinate_ratio_restriction_zero
end HodgeLean.Foundations.Program.G32Native
