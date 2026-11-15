import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Ordered cups of actual divisor families commute with every specified geometric pullback.
Source: unit and cup naturality, iterated over the finite family. -/
theorem s4_selected_divisor_cup_pullback
    (X Z : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (n : ℕ) (D : Fin n → HQ Z 2) :
    homPullback f (2 * n) (s4_selected_divisor_cup Z n D) =
      s4_selected_divisor_cup X n (fun i => homPullback f 2 (D i)) := by
  induction n with
  | zero =>
    change homPullback f 0 (cupUnit Z) = cupUnit X
    exact spec_homPullback_unit f
  | succ n ih =>
    change homPullback f (2 * (n + 1))
      ((cupProductOf Z).cup (by omega : 2 + 2 * n = 2 * (n + 1))
        (D 0) (s4_selected_divisor_cup Z n (Fin.tail D))) =
      (cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1))
        (homPullback f 2 (D 0))
        (s4_selected_divisor_cup X n (fun i => homPullback f 2 (D i.succ)))
    rw [spec_homPullback_cup, ih]
    rfl

#print axioms s4_selected_divisor_cup_pullback
end HodgeLean.Foundations.Program
