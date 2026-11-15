import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- Scaling each divisor factor scales the actual ordered cup by the product of the scalars.
Source: rational bilinearity of the actual cup product. -/
theorem s4_selected_divisor_cup_scalars
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) (c : Fin n → ℚ) (D : Fin n → HQ X 2) :
    s4_selected_divisor_cup X n (fun i => c i • D i) =
      (∏ i, c i) • s4_selected_divisor_cup X n D := by
  induction n with
  | zero =>
    change cupUnit X = (1 : ℚ) • cupUnit X
    exact (one_smul ℚ (cupUnit X)).symm
  | succ n ih =>
    change (cupProductOf X).cup (by omega : 2 + 2 * n = 2 * (n + 1))
      (c 0 • D 0) (s4_selected_divisor_cup X n (fun i => c i.succ • D i.succ)) = _
    rw [ih, map_smul, LinearMap.map_smul₂, smul_smul, Fin.prod_univ_succ]
    rw [mul_comm (∏ i : Fin n, c i.succ) (c 0)]
    rfl

#print axioms s4_selected_divisor_cup_scalars
end HodgeLean.Foundations.Program
