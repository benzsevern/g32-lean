import HodgeLean.Foundations.Program.SchoenPowerComplexPoints
import HodgeLean.Foundations.Program.SchoenTowerN1bcHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Each projection of an actual scheme power is dominant over the retained complex base. -/
theorem s2v_l1b_divisor_projection_dominant
    (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom] (n : ℕ) (j : Fin n) :
    IsDominant (g3_proj Y n j).left := by
  apply n1bc_dominant_of_points_surjective
  intro y
  exact ⟨s2_lift n (fun _ => y), s2_check_lift_proj n (fun _ => y) j⟩

/-- The coordinate product of a rational function on an actual scheme power. -/
def s2v_l1b_divisor_product_function
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left] (u : Y.left.functionField) :
    (g3_power Y n).left.functionField := by
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  exact ∏ j, s2v_l1b_functionFieldPullback (g3_proj Y n j).left u

/-- Coordinate products preserve nonvanishing. -/
theorem s2v_l1b_divisor_product_function_ne_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (u : Y.left.functionField) (hu : u ≠ 0) :
    s2v_l1b_divisor_product_function Y n u ≠ 0 := by
  letI : ∀ j : Fin n, IsDominant (g3_proj Y n j).left :=
    s2v_l1b_divisor_projection_dominant Y n
  unfold s2v_l1b_divisor_product_function
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  simpa only [map_zero] using
    (s2v_l1b_functionFieldPullback (g3_proj Y n j).left).hom.injective.ne hu

end HodgeLean.Foundations.Program
