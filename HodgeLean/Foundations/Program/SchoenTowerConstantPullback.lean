import HodgeLean.Foundations.Program.SchoenExceptionalDefs
import Mathlib.CategoryTheory.Adjunction.Unique

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

def s2v_pullback_constantSheaf_iso {X Y : TopCat.{0}} (p : X ⟶ Y)
    (A : AddCommGrpCat.{0}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} p).obj
      ((TopCat.Sheaf.constantFunctor Y).obj A) ≅
      (TopCat.Sheaf.constantFunctor X).obj A := by
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  let adj : (constantSheaf JY AddCommGrpCat.{0} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{0} p) ⊣
      (sheafSections JX AddCommGrpCat.{0}).obj (op ⊤) :=
    (constantSheafAdj JY AddCommGrpCat.{0} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p)
  exact (adj.leftAdjointUniq
    (constantSheafAdj JX AddCommGrpCat.{0} isTerminalTop)).app A

end HodgeLean.Foundations.Program
