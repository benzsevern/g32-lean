import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks

/-! # Exact ordered point traces under coordinate permutations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The full point trace is invariant under every retained permutation, with no distinctness restriction. -/
theorem residual_ordered_point_trace_permute
    (Z : Over (Spec ↧ℂ)) (n : ℕ)
    {M : Type*} [AddCommMonoid M] (f : ComplexPoint Z → M)
    (σ : Equiv.Perm (Fin n)) (u : ComplexPoint (g3_power Z n)) :
    (∑ i, f (Point.map (g3_proj Z n i) (Point.map (s2_permute Z n σ) u))) =
      ∑ i, f (Point.map (g3_proj Z n i) u) := by
  classical
  have hi (i : Fin n) :
      Point.map (g3_proj Z n i) (Point.map (s2_permute Z n σ) u) =
        Point.map (g3_proj Z n (σ.symm i)) u := by
    rw [← Point.map_comp_apply]
    exact congrArg (fun v => Point.map v u) (s2_check_lift_proj n _ i)
  simp_rw [hi]
  exact Equiv.sum_comp σ.symm (fun i => f (Point.map (g3_proj Z n i) u))

#print axioms residual_ordered_point_trace_permute
end HodgeLean.Foundations.Program.G32Native
