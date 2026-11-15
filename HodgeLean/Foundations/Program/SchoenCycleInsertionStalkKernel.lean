import HodgeLean.Foundations.Program.SchoenCycleInsertionStalkPowers
import HodgeLean.Foundations.Program.SchoenCycleLocalIdealSeparation

/-! # The actual principal ideal of marked insertion in curve powers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual insertion stalk kernel is precisely the marked regular
parameter ideal, including at repeated coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_branchInsertion_stalk_kernel
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n)) :
    RingHom.ker ((s2c_branchInsertion Z n a).left.stalkMap x.underlying).hom =
      Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
        (Point.map (s2c_branchInsertion Z n a) x) 0)) := by
  let q := s2c_branchInsertion Z n a
  let z := Point.map q x
  let Rt := (g3_power Z (n + 1)).left.presheaf.stalk z.underlying
  letI : IsLocallyNoetherian (g3_power Z (n + 1)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z (n + 1)).hom
  apply le_antisymm
  · intro r hr
    apply s2e_local_ideal_mem_of_all_power_neighbourhoods Rt
      (Ideal.span {s2e_curvePowerParameter Z (n + 1) z 0}) r
    intro N
    cases N with
    | zero => simp
    | succ N =>
      apply s2e_branchInsertion_stalk_power_kernel_control Z n a x (N + 1) (Nat.succ_pos N) r
      change (q.left.stalkMap x.underlying).hom r = 0 at hr
      rw [hr]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    intro r hr
    have he : r = s2e_curvePowerParameter Z (n + 1) z 0 := Set.mem_singleton_iff.mp hr
    subst r
    exact s2e_branchInsertion_curvePowerParameter_zero Z n a x

end HodgeLean.Foundations.Program
