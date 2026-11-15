import HodgeLean.Foundations.Program.SchoenCycleCoordinateParameterNonzero
import HodgeLean.Foundations.Program.SchoenCycleInsertionPointRange
import HodgeLean.Foundations.Program.SchoenCycleInsertionParameters

/-! # Separation of actual coordinate parameter ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The first actual coordinate parameter does not divide any moving coordinate parameter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_first_curvePowerParameter_not_dvd_succ
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z (n + 1))) (j : Fin n) :
    ¬s2e_curvePowerParameter Z (n + 1) x 0 ∣
      s2e_curvePowerParameter Z (n + 1) x j.succ := by
  let a := Point.map (g3_proj Z (n + 1) 0) x
  let y := Point.map (s2e_dropFirstPowerCoordinate Z n) x
  let ins := s2c_branchInsertion Z n a
  have he : Point.map ins y = x := s2e_branchInsertion_point_of_first_coordinate Z n a x rfl
  have hd : ¬s2e_curvePowerParameter Z (n + 1) (Point.map ins y) 0 ∣
      s2e_curvePowerParameter Z (n + 1) (Point.map ins y) j.succ := by
    intro h
    have hm := map_dvd (ins.left.stalkMap y.underlying).hom h
    change ins.left.stalkMap y.underlying
      (s2e_curvePowerParameter Z (n + 1) (Point.map ins y) 0) ∣
      ins.left.stalkMap y.underlying
        (s2e_curvePowerParameter Z (n + 1) (Point.map ins y) j.succ) at hm
    rw [s2e_branchInsertion_curvePowerParameter_zero,
      s2e_branchInsertion_curvePowerParameter_succ] at hm
    exact s2e_curvePowerParameter_ne_zero Z n y j (zero_dvd_iff.mp hm)
  have ht : ∀ z : ComplexPoint (g3_power Z (n + 1)), Point.map ins y = z →
      ¬s2e_curvePowerParameter Z (n + 1) z 0 ∣ s2e_curvePowerParameter Z (n + 1) z j.succ := by
    rintro z rfl
    exact hd
  exact ht x he

end HodgeLean.Foundations.Program
