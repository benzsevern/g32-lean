import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.Monoidal
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.Frames

/-! # Natural local linear maps underlying the actual sheaf dual -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The presheaf of natural families of local linear maps. -/
abbrev pairedC3HomPresheaf {X : Scheme.{0}} (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.ihomObj
    ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj M)
    ((SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj N)

/-- Natural families into a module sheaf form a module sheaf. -/
def pairedC3HomSheaf {X : Scheme.{0}} (M N : X.Modules) : X.Modules where
  val := pairedC3HomPresheaf M N
  isSheaf := PresheafOfModules.isSheaf_ihomObj _ _ N.isSheaf

/-- The existing internal Hom is identified with the sheaf of actual
natural families, via the module-sheafification counit. -/
def pairedC3DualPresheafIso {X : Scheme.{0}} (M : X.Modules) :
    M.dual ≅ pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property
    (pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf))

#print axioms pairedC3DualPresheafIso
end HodgeLean.Foundations.Program.G32Native
