import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual retained identity factor permutation is the identity on the scheme power. -/
theorem s2_permute_one (X : Over (Spec ↧ℂ)) (n : ℕ) :
    s2_permute X n (1 : Equiv.Perm (Fin n)) = 𝟙 (g3_power X n) := by
  apply s2_product_hom_ext n
  intro i
  simp only [s2_permute, s2_check_lift_proj, Equiv.Perm.one_symm,
    Equiv.Perm.one_apply, Category.id_comp]

/-- Actual retained factor permutations compose contravariantly with their permutation product. -/
theorem s2_permute_mul (X : Over (Spec ↧ℂ)) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) :
    s2_permute X n (σ * τ) = s2_permute X n τ ≫ s2_permute X n σ := by
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_permute, s2_check_lift_proj]
  rfl

/-- Every actual retained factor permutation is an automorphism of the scheme power. -/
def s2_permuteIso (X : Over (Spec ↧ℂ)) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    g3_power X n ≅ g3_power X n where
  hom := s2_permute X n σ
  inv := s2_permute X n σ⁻¹
  hom_inv_id := by rw [← s2_permute_mul, inv_mul_cancel, s2_permute_one]
  inv_hom_id := by rw [← s2_permute_mul, mul_inv_cancel, s2_permute_one]

/-- The actual symmetric group action on a retained scheme power. -/
def s2_symmetricPowerAction (X : Over (Spec ↧ℂ)) (n : ℕ) :
    Equiv.Perm (Fin n) →* Aut (g3_power X n) where
  toFun σ := Aut.of (s2_permuteIso X n σ)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact s2_permute_one X n
  map_mul' σ τ := by
    apply Aut.ext
    apply Iso.ext
    exact s2_permute_mul X n σ τ

end HodgeLean.Foundations.Program
