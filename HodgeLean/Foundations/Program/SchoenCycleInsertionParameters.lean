import HodgeLean.Foundations.Program.SchoenCycleParameterPermutations
import HodgeLean.Foundations.Program.SchoenCycleSymmetricBranch
import HodgeLean.Foundations.Program.SchoenCycleConstantParameters

/-! # Actual curve parameters under marked insertion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Marked insertion preserves every moving factor's actual regular parameter.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_branchInsertion_curvePowerParameter_succ
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n)) (i : Fin n) :
    (s2c_branchInsertion Z n a).left.stalkMap x.underlying
      (s2e_curvePowerParameter Z (n + 1)
        (Point.map (s2c_branchInsertion Z n a) x) i.succ) =
      s2e_curvePowerParameter Z n x i := by
  let q := s2c_branchInsertion Z n a
  change q.left.stalkMap x.underlying
      (s2e_curvePullbackParameter Z (g3_power Z (n + 1))
        (g3_proj Z (n + 1) i.succ) (Point.map q x)) =
    s2e_curvePullbackParameter Z (g3_power Z n) (g3_proj Z n i) x
  rw [s2e_curvePullbackParameter_comp]
  have he : q ≫ g3_proj Z (n + 1) i.succ = g3_proj Z n i :=
    s2_check_lift_proj (n + 1) _ i.succ
  rw [he]

/-- The fixed factor's actual regular parameter becomes zero under marked
insertion.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_branchInsertion_curvePowerParameter_zero
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n)) :
    (s2c_branchInsertion Z n a).left.stalkMap x.underlying
      (s2e_curvePowerParameter Z (n + 1)
        (Point.map (s2c_branchInsertion Z n a) x) 0) = 0 := by
  let q := s2c_branchInsertion Z n a
  change q.left.stalkMap x.underlying
      (s2e_curvePullbackParameter Z (g3_power Z (n + 1))
        (g3_proj Z (n + 1) 0) (Point.map q x)) = 0
  rw [s2e_curvePullbackParameter_comp]
  have he : q ≫ g3_proj Z (n + 1) 0 =
      CartesianMonoidalCategory.toUnit (g3_power Z n) ≫ a :=
    s2_check_lift_proj (n + 1) _ 0
  rw [he]
  exact s2e_curvePullbackParameter_constant_zero Z (g3_power Z n)
    (CartesianMonoidalCategory.toUnit (g3_power Z n)) a x

end HodgeLean.Foundations.Program
