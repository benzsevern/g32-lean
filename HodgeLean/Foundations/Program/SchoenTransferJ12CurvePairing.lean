import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCupDuality
import HodgeLean.RealDefs.FiniteBettiCompact

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf

/-- The curve cup pairing identifies degree one with its rational dual. -/
theorem s4_selected_curve_pairing_bijective
    (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) :
    Function.Bijective (((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂
      I.toLinearMap) := by
  letI := (finbetti_finiteBetti Y).finite 1
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  have hi : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply s4_selected_curve_cup_nondegenerate Y hdim I v
    intro w
    exact LinearMap.congr_fun hv w
  have hflip : Function.Injective P.flip := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply s4_selected_curve_cup_nondegenerate Y hdim I v
    intro w
    have hw : I ((cupProductOf Y).cup rfl w v) = 0 :=
      LinearMap.congr_fun hv w
    rw [(cupProductOf Y).graded_comm (i := 1) (j := 1) rfl rfl w v]
    simpa only [Nat.mul_one, pow_one, neg_one_smul, map_neg, hw, neg_zero]
  exact (LinearMap.IsPerfPair.of_injective hi hflip).bijective_left

#print axioms s4_selected_curve_pairing_bijective
end HodgeLean.Foundations.Program
