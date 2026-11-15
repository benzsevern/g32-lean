import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkComposition

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A map equal to the identity acts identically on its actual stalk and function field. -/
theorem s2v_l1b_divisor_identity_pullbacks
    (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ X) [IsDominant f]
    (hf : f = 𝟙 X) (p : X) (hp : f p = p) :
    (∀ v, s2e_fixed_point_stalkPullback X f p hp v = v) ∧
      s2v_l1b_functionFieldPullback f = 𝟙 X.functionField := by
  subst f
  exact ⟨s2v_l1b_divisor_fixed_stalk_id X p hp, s2v_l1b_functionFieldPullback_id X⟩

end HodgeLean.Foundations.Program
