import HodgeLean.Foundations.Curves.Picard.Families.OrderedPermutation
import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction

/-! # Comparing literal ordered powers with retained recursive powers

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.Picard.Families
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

/-- The retained comparison between literal and recursive scheme powers.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
def orderedRecursiveIso (C : Over (Spec ↧ℂ)) (n : ℕ) : OrderedPower C n ≅ g3_power C n where
  hom := s2_lift n (fun i => Pi.π (fun _ : Fin n => C) i)
  inv := Pi.lift (fun i => g3_proj C n i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp [Category.assoc, s2_check_lift_proj]
  inv_hom_id := by
    apply s2_product_hom_ext n
    intro i
    simp [Category.assoc, s2_check_lift_proj]

/-- Transport a permutation from the literal power to the recursive power.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
theorem orderedRecursiveIso_permute (C : Over (Spec ↧ℂ)) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    orderedPermutation C n σ ≫ (orderedRecursiveIso C n).hom =
      (orderedRecursiveIso C n).hom ≫ s2_permute C n σ⁻¹ := by
  apply s2_product_hom_ext n
  intro i
  simp [orderedPermutation, orderedRecursiveIso, s2_permute,
    Category.assoc, s2_check_lift_proj]
  rfl

/-- Transport a permutation in the inverse comparison direction.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
theorem orderedRecursiveIso_inv_permute (C : Over (Spec ↧ℂ)) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    s2_permute C n σ ≫ (orderedRecursiveIso C n).inv =
      (orderedRecursiveIso C n).inv ≫ orderedPermutation C n σ⁻¹ := by
  apply Pi.hom_ext
  intro i
  simp [orderedPermutation, orderedRecursiveIso, s2_permute,
    Category.assoc, s2_check_lift_proj] <;> rfl

example (C : Over (Spec ↧ℂ)) :
    (orderedRecursiveIso C 2).hom ≫ g3_proj C 2 1 =
      Pi.π (fun _ : Fin 2 => C) 1 := by
  exact s2_check_lift_proj _ _ _

example (C : Over (Spec ↧ℂ)) :
    orderedPermutation C 2 (Equiv.swap 0 1) ≫ (orderedRecursiveIso C 2).hom ≫
      g3_proj C 2 0 = Pi.π (fun _ : Fin 2 => C) 1 := by
  simp [orderedRecursiveIso, Category.assoc, s2_check_lift_proj,
    orderedPermutation, Pi.lift_π, Equiv.swap_apply_left]

example (C : Over (Spec ↧ℂ)) :
    s2_permute C 2 (Equiv.swap 0 1) ≫ (orderedRecursiveIso C 2).inv ≫
      Pi.π (fun _ : Fin 2 => C) 0 = g3_proj C 2 1 := by
  simp [orderedRecursiveIso, Category.assoc, Pi.lift_π,
    s2_permute, s2_check_lift_proj, Equiv.swap_apply_left]

end HodgeLean.Foundations.Curves.Picard.Families
