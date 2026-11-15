import HodgeLean.Foundations.Program.SchoenCycleC2IdealTargetIsoHelpers
import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs

/-! # Actual ideal modules under an ambient isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The ideal module in new ambient coordinates is the actual inverse
pullback of the original ideal module. -/
def idealTargetPullbackIso {Q W W' : Scheme.{0}} (i : Q ⟶ W) (e : W ≅ W') :
    (Scheme.Modules.pullback e.inv).obj (Conormal.idealModule i) ≅
      Conormal.idealModule (i ≫ e.hom) := by
  let j := i ≫ e.hom
  have hj : j ≫ e.inv = i := by simp [j]
  let E : (Scheme.Modules.pushforward e.inv).obj (Conormal.idealModule j) ≅
      Conormal.idealModule i :=
    s2e_idealModule_target_pushforward_iso j e.symm ≪≫
      eqToIso (congrArg Conormal.idealModule hj)
  exact (Scheme.Modules.restrictFunctorIsoPullback e.inv).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso E.symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app _

#print axioms idealTargetPullbackIso
end HodgeLean.Foundations.Program.G32Native
