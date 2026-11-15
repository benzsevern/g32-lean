import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordan

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The fibre-integral Jordan operation as a rational bilinear map. -/
def s4_selected_curve_jordan_linear
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) : HQ A 2 →ₗ[ℚ] HQ A 2 →ₗ[ℚ] HQ A 2 where
  toFun p :=
    { toFun := s4_selected_curve_jordan A Y f I p
      map_add' := by
        intro q r
        simp only [s4_selected_curve_jordan, map_add, LinearMap.add_apply,
          add_smul, smul_add]
        module
      map_smul' := by
        intro c q
        simp only [s4_selected_curve_jordan, map_smul, LinearMap.smul_apply,
          RingHom.id_apply]
        module }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro r
    change s4_selected_curve_jordan A Y f I (p + q) r =
      s4_selected_curve_jordan A Y f I p r + s4_selected_curve_jordan A Y f I q r
    simp only [LinearMap.add_apply, s4_selected_curve_jordan, map_add,
      add_smul, smul_add]
    module
  map_smul' := by
    intro c p
    apply LinearMap.ext
    intro q
    change s4_selected_curve_jordan A Y f I (c • p) q =
      c • s4_selected_curve_jordan A Y f I p q
    simp only [LinearMap.smul_apply, RingHom.id_apply, s4_selected_curve_jordan, map_smul]
    module

#print axioms s4_selected_curve_jordan_linear
end HodgeLean.Foundations.Program
