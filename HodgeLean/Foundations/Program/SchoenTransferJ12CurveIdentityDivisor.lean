import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordanImage
import HodgeLean.Foundations.Program.SchoenTransferJ12JordanIdentity
import HodgeLean.RealDefs.FiniteBettiCompact

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- An injective algebraic divisor operator supplies an algebraic divisor whose actual operator is the identity. -/
theorem s4_selected_curve_identity_divisor_of_injective_operator
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ)
    (p : HQ A 2) (hp : p ∈ cfd_cycleSpan A 1)
    (hinj : Function.Injective (s4_selected_curve_divisor_operator A Y f I p)) :
    ∃ q : HQ A 2, q ∈ cfd_cycleSpan A 1 ∧
      s4_selected_curve_divisor_operator A Y f I q = LinearMap.id := by
  letI := (finbetti_finiteBetti A).finite 1
  let D := s4_selected_curve_divisor_operator A Y f I
  let S := (cfd_cycleSpan A 1).map D
  have hid : LinearMap.id ∈ S := s4_selected_identity_mem_jordan_submodule S
    (s4_selected_curve_divisor_operator_image_jordan A Y hdim f I) (D p)
    (Submodule.mem_map_of_mem hp) hinj
  exact Submodule.mem_map.mp hid

#print axioms s4_selected_curve_identity_divisor_of_injective_operator
end HodgeLean.Foundations.Program
