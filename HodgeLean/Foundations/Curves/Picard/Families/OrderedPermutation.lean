import HodgeLean.Foundations.Curves.Picard.Families.Defs

/-! # Literal permutations of the ordered scheme power

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.Families
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000

/-- The retained permutation of the literal ordered power.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
def orderedPermutation (C : Over (Spec ↧ℂ)) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    OrderedPower C n ⟶ OrderedPower C n :=
  Pi.lift (fun i => Pi.π (fun _ : Fin n => C) (σ i))

/-- Composition of literal coordinate permutations.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
theorem orderedPermutation_comp (C : Over (Spec ↧ℂ)) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) :
    orderedPermutation C n σ ≫ orderedPermutation C n τ = orderedPermutation C n (σ * τ) := by
  apply Pi.hom_ext
  intro i
  simp [orderedPermutation, Equiv.Perm.mul_apply]

/-- The identity permutation fixes every ordered coordinate.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
theorem orderedPermutation_one (C : Over (Spec ↧ℂ)) (n : ℕ) :
    orderedPermutation C n 1 = 𝟙 (OrderedPower C n) := by
  apply Pi.hom_ext
  intro i
  simp [orderedPermutation]

/-- A literal coordinate permutation and its inverse.
Source: Hartshorne, Algebraic Geometry, II.3, universal property of finite products. -/
def orderedPermutationIso (C : Over (Spec ↧ℂ)) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    OrderedPower C n ≅ OrderedPower C n where
  hom := orderedPermutation C n σ
  inv := orderedPermutation C n σ⁻¹
  hom_inv_id := by
    rw [orderedPermutation_comp, mul_inv_cancel, orderedPermutation_one]
  inv_hom_id := by
    rw [orderedPermutation_comp, inv_mul_cancel, orderedPermutation_one]

example (C : Over (Spec ↧ℂ)) :
    orderedPermutation C 2 (Equiv.swap 0 1) ≫ Pi.π (fun _ : Fin 2 => C) 0 =
      Pi.π (fun _ : Fin 2 => C) 1 := by
  simp [orderedPermutation, Pi.lift_π, Equiv.swap_apply_left]

example (C : Over (Spec ↧ℂ)) :
    orderedPermutation C 2 (1 : Equiv.Perm (Fin 2)) = 𝟙 _ := by
  apply Pi.hom_ext
  intro i
  simp [orderedPermutation, Pi.lift_π, Category.id_comp, Equiv.Perm.one_apply]

example (C : Over (Spec ↧ℂ)) :
    (orderedPermutationIso C 2 (Equiv.swap 0 1)).hom ≫
      Pi.π (fun _ : Fin 2 => C) 0 = Pi.π (fun _ : Fin 2 => C) 1 := by
  simp [orderedPermutationIso, orderedPermutation, Pi.lift_π, Equiv.swap_apply_left]

example (C : Over (Spec ↧ℂ)) :
    orderedPermutation C 2 (Equiv.swap 0 1) ≫ orderedPermutation C 2 (Equiv.swap 0 1) =
      𝟙 _ := by
  apply Pi.hom_ext
  intro i
  simp [Category.assoc, orderedPermutation, Pi.lift_π, Equiv.swap_apply_self,
    Category.id_comp]

end HodgeLean.Foundations.Curves.Picard.Families
