import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedCup
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveCrossAction
import HodgeLean.Foundations.Program.SchoenTransferJ12KernelLinearMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual mixed divisor acts by the difference of its two fibre cup pairings.
Source: Fulton, Intersection Theory, §16.1; Birkenhake–Lange, Complex Abelian Varieties, §2.5. -/
theorem s4_selected_curve_mixed_divisor_action
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (v w : HQ A 1) (u : HQ Y 1) :
    s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num)
      (s4_selected_curve_mixed_divisor A Y f ((cupProductOf A).cup rfl v w)) u =
      I ((cupProductOf Y).cup rfl (homPullback f 1 w) u) • v -
        I ((cupProductOf Y).cup rfl (homPullback f 1 v) u) • w := by
  rw [s4_selected_curve_mixed_divisor_cup]
  have hs := LinearMap.congr_fun
    ((s4_selected_kernel_linear_map A Y 1 I 1 1 1 (by norm_num)).map_sub
      ((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (CategoryTheory.CartesianMonoidalCategory.fst A Y) 1 v)
        (homPullback (CategoryTheory.CartesianMonoidalCategory.snd A Y) 1 (homPullback f 1 w)))
      ((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback (CategoryTheory.CartesianMonoidalCategory.fst A Y) 1 w)
        (homPullback (CategoryTheory.CartesianMonoidalCategory.snd A Y) 1 (homPullback f 1 v)))) u
  change s4_selected_corr_action A Y 1 I 1 1 1 _ (_ - _) u =
    s4_selected_corr_action A Y 1 I 1 1 1 _ _ u -
      s4_selected_corr_action A Y 1 I 1 1 1 _ _ u at hs
  rw [hs, s4_selected_curve_cross_action, s4_selected_curve_cross_action]

#print axioms s4_selected_curve_mixed_divisor_action
end HodgeLean.Foundations.Program
