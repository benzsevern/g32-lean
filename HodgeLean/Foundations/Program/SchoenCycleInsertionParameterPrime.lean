import HodgeLean.Foundations.Program.SchoenCycleInsertionStalkKernel
import HodgeLean.Foundations.Program.SchoenCycleInsertionPointRange

/-! # Primality of actual marked-coordinate parameter ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The marked regular parameter ideal at every actual insertion point is prime.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.9. -/
theorem s2e_branchInsertion_marked_parameter_prime
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n)) :
    (Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
      (Point.map (s2c_branchInsertion Z n a) x) 0))).IsPrime := by
  have hp := RingHom.ker_isPrime
    ((s2c_branchInsertion Z n a).left.stalkMap x.underlying).hom
  rwa [s2e_branchInsertion_stalk_kernel] at hp

/-- The first regular coordinate ideal is prime at every actual power point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curvePowerParameter_first_ideal_prime
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z (n + 1))) :
    (Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1) x 0))).IsPrime := by
  let a := Point.map (g3_proj Z (n + 1) 0) x
  let y := Point.map (s2e_dropFirstPowerCoordinate Z n) x
  have he : Point.map (s2c_branchInsertion Z n a) y = x :=
    s2e_branchInsertion_point_of_first_coordinate Z n a x rfl
  have hp := s2e_branchInsertion_marked_parameter_prime Z n a y
  rwa [he] at hp

end HodgeLean.Foundations.Program
