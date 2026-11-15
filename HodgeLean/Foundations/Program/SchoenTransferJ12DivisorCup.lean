import HodgeLean.Foundations.Program.SchoenTransferLefschetzKernel

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- Ordered cup of an actual finite family of degree-two classes.
Source: the specified cup product, iterated with its actual degree transports. -/
def s4_selected_divisor_cup
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (n : ℕ) → (Fin n → HQ X 2) → HQ X (2 * n)
  | 0, _ => cupUnit X
  | n + 1, D => (cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1))
      (D 0) (s4_selected_divisor_cup X n (Fin.tail D))

/-- Actual algebraic divisor classes on an abelian variety have algebraic ordered cups.
Source: the abelian cycle-class product theorem, iterated over the specified finite family. -/
theorem s4_selected_divisor_cup_mem
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (D : Fin n → HQ X 2) (hD : ∀ i, D i ∈ cfd_cycleSpan X 1) :
    s4_selected_divisor_cup X n D ∈ cfd_cycleSpan X n := by
  induction n with
  | zero =>
    change cupUnit X ∈ algebraicCycleClassSpan X 0
    exact unitClass_mem_algebraicCycleClassSpan
  | succ n ih =>
    change (cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1))
      (D 0) (s4_selected_divisor_cup X n (Fin.tail D)) ∈ algebraicCycleClassSpan X (n + 1)
    exact (hc9k_cycleClassMultiplicative X).mem_of_eq (p := 1) (q := n) (r := n + 1)
      (by omega) _ _ (hD 0) (ih (Fin.tail D) (fun i => hD i.succ))

#print axioms s4_selected_divisor_cup_mem
end HodgeLean.Foundations.Program
