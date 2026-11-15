import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Exact pullback of the specified singular hyperplane powers -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual singular pullback preserves every specified hyperplane cup power, including the unit. -/
theorem hyperplanePower_pullback {X Y : TopCat.{0}} (f : X ⟶ Y)
    (H : Cohomology ℚ Y 2) (n : ℕ) :
    cohomologyMap ℚ (2 * n) f (s2e_hyperplanePower Y H n) =
      s2e_hyperplanePower X (cohomologyMap ℚ 2 f H) n := by
  induction n with
  | zero => exact HodgeLean.Foundations.Singular.cohomologyMap_unit Y f
  | succ n ih =>
    simp only [s2e_hyperplanePower, HodgeLean.Foundations.Singular.cohomologyMap_cup, ih]

#print axioms hyperplanePower_pullback
end HodgeLean.Foundations.Program.G32Native.EulerModel
