import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordanCoordinates
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveDivisorOperator

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The Jordan operation on decomposable divisors induces the symmetrized operator product. -/
theorem s4_selected_curve_jordan_operator_cups
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (v w s t : HQ A 1) :
    let D := s4_selected_curve_divisor_operator A Y f I
    let p := (cupProductOf A).cup rfl v w
    let q := (cupProductOf A).cup rfl s t
    D (s4_selected_curve_jordan A Y f I p q) =
      (2 : ℚ)⁻¹ • ((D p).comp (D q) + (D q).comp (D p)) := by
  dsimp only
  have hB (a b : HQ A 1) :
      I ((cupProductOf Y).cup rfl (homPullback f 1 a) (homPullback f 1 b)) =
        -I ((cupProductOf Y).cup rfl (homPullback f 1 b) (homPullback f 1 a)) := by
    rw [CupProduct.cup_comm_one, map_neg]
  rw [s4_selected_curve_jordan_cups]
  ext z
  simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, RingHom.id_apply,
    s4_selected_curve_divisor_operator_cup]
  simp only [map_smul, map_add, map_sub, RingHom.id_apply,
    hB s v, hB t v, hB s w, hB t w]
  module

#print axioms s4_selected_curve_jordan_operator_cups
end HodgeLean.Foundations.Program
