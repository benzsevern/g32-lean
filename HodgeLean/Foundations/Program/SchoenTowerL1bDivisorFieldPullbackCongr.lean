import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Equal dominant maps have equal generic pullbacks, independently of the dominance witnesses. -/
theorem s2v_l1b_divisor_functionFieldPullback_congr
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g] (h : f = g) :
    s2v_l1b_functionFieldPullback f = s2v_l1b_functionFieldPullback g := by
  subst g
  rfl

end HodgeLean.Foundations.Program
