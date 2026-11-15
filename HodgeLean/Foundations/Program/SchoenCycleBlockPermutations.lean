import Mathlib.Algebra.Group.End

/-! # Unique independent permutations of indexed blocks -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A permutation preserving block labels is uniquely a family of within-block permutations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_block_permutation_unique
    {α : Type*} {β : α → Type*} (τ : Equiv.Perm (Σ a, β a))
    (hτ : ∀ v, (τ v).1 = v.1) :
    ∃! ρ : ∀ a, Equiv.Perm (β a), τ = Equiv.Perm.sigmaCongrRight ρ := by
  let F (a : α) : β a ≃ {v : Σ a, β a // v.1 = a} :=
    { toFun := fun i => ⟨⟨a, i⟩, rfl⟩
      invFun := fun v => v.property ▸ v.val.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨a', i⟩, h⟩ => by cases h; rfl }
  have hs (a : α) (v : Σ a, β a) : v.1 = a ↔ (τ v).1 = a := by rw [hτ v]
  let ρ (a : α) := ((F a).trans (τ.subtypeEquiv (hs a))).trans (F a).symm
  have hρ : τ = Equiv.Perm.sigmaCongrRight ρ := by
    apply Equiv.ext
    rintro ⟨a, i⟩
    change τ ⟨a, i⟩ = ⟨a, ρ a i⟩
    have he : F a (ρ a i) = (τ.subtypeEquiv (hs a)) (F a i) :=
      (F a).apply_symm_apply _
    exact (congrArg Subtype.val he).symm
  refine ⟨ρ, hρ, ?_⟩
  intro ρ' hρ'
  apply Equiv.Perm.sigmaCongrRightHom_injective
  exact hρ'.symm.trans hρ

#print axioms s2e_block_permutation_unique
end HodgeLean.Foundations.Program
