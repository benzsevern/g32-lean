import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs

namespace HodgeLean.Foundations.Program

/-- Actual retained finite powers of an affine complex scheme are affine. -/
theorem s2t_power_isAffine (X : Over (Spec ↧ℂ)) [IsAffine X.left] (n : ℕ) :
    IsAffine (g3_power X n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsAffine (Spec ↧ℂ))
  | succ n ih =>
    letI := ih
    change IsAffine (Limits.pullback X.hom (g3_power X n).hom)
    infer_instance

/-- The actual retained power map commutes with each retained factor permutation. -/
theorem s2t_powerMap_equivariant {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_powerMap f n ≫ s2_permute Y n σ = s2_permute X n σ ≫ s2_powerMap f n := by
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_permute, s2_powerMap, s2_check_lift_proj]
  rw [← Category.assoc, s2_check_lift_proj]

end HodgeLean.Foundations.Program
