import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Addition along an arbitrary curve map pulls degree one back to its two actual coordinate terms. -/
theorem s4_selected_curve_add_pullback_one
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (v : HQ A 1) :
    homPullback (s4_selected_curve_add_map A Y f) 1 v =
      homPullback (fst A Y) 1 v + homPullback (snd A Y) 1 (homPullback f 1 v) := by
  have hadd : s4_selected_curve_add_map A Y f = (snd A Y ≫ f) * fst A Y := by
    simp [s4_selected_curve_add_map, cfd_shear, MonObj.comp_mul]
  rw [hadd, s4_homPullback_mul, spec_homPullback_comp]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  exact add_comm _ _

#print axioms s4_selected_curve_add_pullback_one
end HodgeLean.Foundations.Program
