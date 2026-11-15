import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordanOperator

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Actual algebraic divisor operators are stable under the unnormalized Jordan product. -/
theorem s4_selected_curve_divisor_operator_image_jordan
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    let D := s4_selected_curve_divisor_operator A Y f I
    let S := (cfd_cycleSpan A 1).map D
    ∀ U ∈ S, ∀ W ∈ S, U.comp W + W.comp U ∈ S := by
  dsimp only
  intro U hU W hW
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hU
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hW
  let D := s4_selected_curve_divisor_operator A Y f I
  let S := (cfd_cycleSpan A 1).map D
  have hj : D (s4_selected_curve_jordan A Y f I p q) ∈ S :=
    Submodule.mem_map_of_mem (s4_selected_curve_jordan_mem A Y hdim f I p q hp hq)
  have he := s4_selected_curve_jordan_operator A Y f I p q
  change D (s4_selected_curve_jordan A Y f I p q) =
    (2 : ℚ)⁻¹ • ((D p).comp (D q) + (D q).comp (D p)) at he
  rw [he] at hj
  have h := S.smul_mem (2 : ℚ) hj
  simpa only [smul_smul, mul_inv_cancel₀ (show (2 : ℚ) ≠ 0 by norm_num), one_smul] using h

#print axioms s4_selected_curve_divisor_operator_image_jordan
end HodgeLean.Foundations.Program
