import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers

/-! # Detection of actual ideal-kernel sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The categorical ideal inclusion detects sections of the original
kernel, for any scheme morphism and any ambient open. -/
theorem paired_c3_ideal_kernel_inclusion_injective {X Y : Scheme.{0}}
    (f : X ⟶ Y) (U : Y.Opens) :
    Function.Injective ((kernel.ι
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app (op U)) := by
  intro x y h
  apply (s2e_idealModule_sections_equiv f U).injective
  apply Subtype.ext
  rw [s2e_idealModule_sections_equiv_coe, s2e_idealModule_sections_equiv_coe]
  exact h

end HodgeLean.Foundations.Program.G32Native
