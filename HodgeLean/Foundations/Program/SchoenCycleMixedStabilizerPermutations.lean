import HodgeLean.Foundations.Program.SchoenCycleMixedStabilizer
import HodgeLean.Foundations.Program.SchoenCycleBlockPermutations

/-! # Independent block permutations of actual collision tuples -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every actual mixed-tuple stabilizer element has a unique independent block-permutation description.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_tuple_stabilizer_iff_block_permutations
    (X : Over (Spec ↧ℂ)) (n b : ℕ) (x : ComplexPoint (g3_power X n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint X) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj X n (ι ⟨a, i⟩)) x = p a)
    (σ : Equiv.Perm (Fin n)) :
    Point.map (s2_permute X n σ) x = x ↔
      ∃! ρ : (a : Fin b) → Equiv.Perm (Fin (m a)),
        σ = ι.permCongr (Equiv.Perm.sigmaCongrRight ρ) := by
  rw [s2e_mixed_tuple_stabilizer_iff_blocks X n b x m ι p hp hx σ]
  constructor
  · intro hσ
    let τ := ι.symm.permCongr σ
    have hτ : ∀ v : Σ a, Fin (m a), (τ v).1 = v.1 := by
      rintro ⟨a, i⟩
      change (ι.symm (σ (ι ⟨a, i⟩))).1 = a
      simpa only [ι.symm_apply_apply] using hσ (ι ⟨a, i⟩)
    obtain ⟨ρ, hρ, _⟩ := s2e_block_permutation_unique τ hτ
    have hστ : σ = ι.permCongr τ := (ι.permCongr.apply_symm_apply σ).symm
    have he : σ = ι.permCongr (Equiv.Perm.sigmaCongrRight ρ) :=
      hστ.trans (congrArg ι.permCongr hρ)
    refine ⟨ρ, he, ?_⟩
    intro ρ' hρ'
    apply Equiv.Perm.sigmaCongrRightHom_injective
    apply ι.permCongr.injective
    exact hρ'.symm.trans he
  · rintro ⟨ρ, hρ, _⟩ i
    rw [hρ]
    simp only [Equiv.permCongr_apply, ι.symm_apply_apply]
    rfl

#print axioms s2e_mixed_tuple_stabilizer_iff_block_permutations
end HodgeLean.Foundations.Program
