import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs

namespace HodgeLean.Foundations.Program

/-- An actual retained finite power of an open immersion is an open immersion. -/
theorem s2t_power_openImmersion (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    [IsOpenImmersion f.left] (n : ℕ) : IsOpenImmersion (s2_powerMap f n).left := by
  induction n with
  | zero =>
    change IsOpenImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  | succ h ih =>
    have heq : s2_powerMap f (h + 1) =
        f ⊗ₘ s2_powerMap f h := by
      apply s2_product_hom_ext (h + 1)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [s2_powerMap, s2_check_lift_proj]
        exact (CartesianMonoidalCategory.tensorHom_fst _ _).symm
      · change s2_powerMap f (h + 1) ≫
          (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y h j) =
          (f ⊗ₘ s2_powerMap f h) ≫
            (CartesianMonoidalCategory.snd _ _ ≫ g3_proj Y h j)
        simp only [← Category.assoc, CartesianMonoidalCategory.tensorHom_snd]
        rw [Category.assoc]
        change s2_powerMap f (h + 1) ≫ g3_proj Y (h + 1) j.succ =
          CartesianMonoidalCategory.snd _ _ ≫ (s2_powerMap f h ≫ g3_proj Y h j)
        simp only [s2_powerMap, s2_check_lift_proj]
        exact Category.assoc _ _ _
    rw [heq, Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance ih
      (Over.w f).symm (Over.w (s2_powerMap f h)).symm

end HodgeLean.Foundations.Program
