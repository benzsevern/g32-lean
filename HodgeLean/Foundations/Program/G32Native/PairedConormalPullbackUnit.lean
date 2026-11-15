import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The actual unit module under scheme pullback -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native

/-- Scheme pullback identifies the actual structure modules by its canonical map. -/
def paired_module_pullbackUnitIso {X Y : Scheme} (p : X ⟶ Y) :
    (Scheme.Modules.pullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (Opens.map p.base).Final := CategoryTheory.final_of_representablyFlat _
  letI : (SheafOfModules.pushforward p.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward p).IsRightAdjoint)
  let makeUnitIso {C D : Type} [Category.{0} C] [Category.{0} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
      {S : Sheaf J RingCat} {T : Sheaf K RingCat}
      [Functor.IsContinuous F J K]
      (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj T)
      [(SheafOfModules.pushforward φ).IsRightAdjoint] [F.Final] :
      (SheafOfModules.pullback φ).obj (SheafOfModules.unit S) ≅ SheafOfModules.unit T :=
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  exact makeUnitIso p.toRingCatSheafHom

end HodgeLean.Foundations.Program.G32Native
