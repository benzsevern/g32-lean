import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceContinuity

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual conjugacy transports a group element's period to the entire
complex-point map of the curve morphism. -/
theorem s2v_l1b_action_conjugate_period
    (Y : Over (Spec ↧ℂ)) {M G : Type} [TopologicalSpace M]
    [Group G] [MulAction G M] (E : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (E y) = E (g • y))
    (N : ℕ) (hperiod : g ^ N = 1) :
    ∀ q : ComplexPoint Y, (Point.map f)^[N] q = q := by
  have hi (n : ℕ) (y : M) : (Point.map f)^[n] (E y) = E ((fun y : M => g • y)^[n] y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        (congrArg (Point.map f) ih).trans (hequiv _)
  intro q
  obtain ⟨y, rfl⟩ := E.surjective q
  rw [hi, smul_iterate_apply, hperiod, one_smul]

end HodgeLean.Foundations.Program
