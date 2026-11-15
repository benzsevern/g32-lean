import HodgeLean.Foundations.Program.SchoenTransferJ12MixedDivisorKernel
import HodgeLean.Foundations.Program.SchoenTransferJ12DivisorCupPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The actual mixed divisor product pulls back by composing its specified source maps.
Source: cup naturality and the actual pair-map composition in the product category. -/
theorem s4_selected_mixed_divisor_kernel_pullback
    (A B Z : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (g : Z ⟶ B) (n : ℕ) (l : Fin n → (B ⟶ A)) (pol : HQ A 2) :
    homPullback (lift (fst A Z) (snd A Z ≫ g)) (2 * n)
      (s4_selected_mixed_divisor_kernel A B n l pol) =
      s4_selected_mixed_divisor_kernel A Z n (fun i => g ≫ l i) pol := by
  unfold s4_selected_mixed_divisor_kernel
  rw [s4_selected_divisor_cup_pullback]
  congr 1
  funext i
  rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
  have hm : lift (fst A Z) (snd A Z ≫ g) ≫ lift (fst A B) (snd A B ≫ l i) =
      lift (fst A Z) (snd A Z ≫ (g ≫ l i)) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]
  rw [hm]

#print axioms s4_selected_mixed_divisor_kernel_pullback
end HodgeLean.Foundations.Program
