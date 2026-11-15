import HodgeLean.Foundations.Program.SchoenSelectedGeometryProducts

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters MonoidalCategory CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tuple coordinates of a complex point are the algebraic product projections.
Source: the universal property of finite products. -/
theorem s0_power_point_homeomorph_projection (A : Over (Spec ↧ℂ)) (n : ℕ)
    (p : ComplexPoint (g3_power A n)) (i : Fin n) :
    s0_power_point_homeomorph A n p i = Point.map (g3_proj A n i) p := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · change s0_power_point_homeomorph A n (Point.map (snd A (g3_power A n)) p) j = _
        rw [ih]
        simp only [g3_proj, Fin.cases_succ, Point.map, Category.assoc]

#print axioms s0_power_point_homeomorph_projection
end HodgeLean.Foundations.Program
