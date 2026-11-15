import HodgeLean.Foundations.BundleResolution.ModuleGlobalSectionHelpers
import HodgeLean.Foundations.Program.G32Native.OriginalIdealRestrictionComparison
import HodgeLean.Foundations.Program.SchoenCycleC2IdealModuleSectionsHelpers

/-! # Original ideal equations as module sections on an ambient open -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open BundleResolution HodgeLean.Foundations.Program

/-- An actual module section on an ambient open gives its unit-module arrow
on the corresponding open subscheme.
Source: `i1_module_unitHomEquivTop` and restriction of module sheaves,
Hartshorne, Algebraic Geometry, II.5. -/
def moduleOpenSectionOfValue {W : Scheme.{0}} (M : W.Modules) (A : W.Opens)
    (t : Γ(M, A)) :
    SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.restrictFunctor A.ι).obj M :=
  (i1_module_unitHomEquivTop ((Scheme.Modules.restrictFunctor A.ι).obj M)).symm
    (M.val.map (eqToHom A.ι_image_top).op t)

/-- The open section arrow retains the same original module section.
Source: `i1_module_unitHomEquivTop.apply_symm_apply`. -/
theorem moduleOpenSectionOfValue_top {W : Scheme.{0}} (M : W.Modules) (A : W.Opens)
    (t : Γ(M, A)) :
    (moduleOpenSectionOfValue M A t).val.app (.op ⊤) (1 : Γ(A.toScheme, ⊤)) =
      M.val.map (eqToHom A.ι_image_top).op t := by
  exact (i1_module_unitHomEquivTop ((Scheme.Modules.restrictFunctor A.ι).obj M)).apply_symm_apply _

#print axioms moduleOpenSectionOfValue_top
end HodgeLean.Foundations.TubularEuler
