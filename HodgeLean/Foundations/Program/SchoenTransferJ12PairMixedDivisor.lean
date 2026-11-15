import HodgeLean.Foundations.Program.SchoenTransferJ12MixedDivisorKernel
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedDivisor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Pair pullback of the actual abelian mixed polarization is the mixed divisor of the specified map.
Source: actual group-sum naturality and the three defining polarization pullbacks. -/
theorem s4_selected_pair_mixed_divisor
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (pol : HQ A 2) :
    homPullback (lift (fst A Y) (snd A Y ≫ f)) 2 (s4_mixedPolarization A pol) =
      s4_selected_curve_mixed_divisor A Y f pol := by
  let m : A ⊗ Y ⟶ A ⊗ A := lift (fst A Y) (snd A Y ≫ f)
  have hmap : m ≫ (fst A A * snd A A) = s4_selected_curve_add_map A Y f := by
    simp [m, s4_selected_curve_add_map, cfd_shear, MonObj.comp_mul, mul_comm]
  have h1 : homPullback m 2 (homPullback (fst A A * snd A A) 2 pol) =
      homPullback (s4_selected_curve_add_map A Y f) 2 pol := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hmap]
  have h2 : homPullback m 2 (homPullback (fst A A) 2 pol) = homPullback (fst A Y) 2 pol := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
  have h3 : homPullback m 2 (homPullback (snd A A) 2 pol) =
      homPullback (snd A Y) 2 (homPullback f 2 pol) := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
      spec_homPullback_comp, LinearMap.comp_apply]
  unfold s4_mixedPolarization s4_selected_curve_mixed_divisor
  change homPullback m 2 _ = _
  rw [map_sub, map_sub, h1, h2, h3]

#print axioms s4_selected_pair_mixed_divisor
end HodgeLean.Foundations.Program
