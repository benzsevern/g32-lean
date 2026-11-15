import HodgeLean.Foundations.Program.SchoenCycleAdicRenameEquiv
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMapComp
import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Reindexing roots and the entire permutation family retains the actual formal invariant algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
def s2e_adic_renamed_reindexed_invariants
    {R σ τ G H : Type*} [CommRing R]
    (e : σ ≃ τ) (t : G ≃ H) (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ)
    (h : ∀ g, e.permCongr (a g) = b (t g)) :
    let P := AdicCompletion (idealOfVars σ R) (MvPolynomial σ R)
    let Q := AdicCompletion (idealOfVars τ R) (MvPolynomial τ R)
    let α g := s2e_adic_algebra_map _ _ (rename (a g))
      (s2e_rename_preserves_origin_powers (a g))
    let β g : Q →ₐ[R] Q := s2e_adic_algebra_map _ _ (rename (b g))
      (s2e_rename_preserves_origin_powers (b g))
    (⨅ g, AlgHom.equalizer (α g) (AlgHom.id R P) : Subalgebra R P) ≃ₐ[R]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id R Q) : Subalgebra R Q) := by
  dsimp only
  let Q := AdicCompletion (idealOfVars τ R) (MvPolynomial τ R)
  let β g : Q →ₐ[R] Q := s2e_adic_algebra_map _ _ (rename (b g))
    (s2e_rename_preserves_origin_powers (b g))
  let K : Subalgebra R Q := ⨅ g : G, AlgHom.equalizer (β (t g)) (AlgHom.id R Q)
  let L : Subalgebra R Q := ⨅ g : H, AlgHom.equalizer (β g) (AlgHom.id R Q)
  have hKL : K = L := by
    ext p
    simp only [K, L, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro hp g
      obtain ⟨g, rfl⟩ := t.surjective g
      exact hp g
    · intro hp g
      exact hp (t g)
  let C := s2e_intertwining_invariant_algebras_equiv (s2e_adic_rename_equiv (R := R) e)
    (fun g => s2e_adic_algebra_map _ _ (rename (a g))
      (s2e_rename_preserves_origin_powers (a g))) (fun g => β (t g)) (by
      intro g
      change (s2e_adic_algebra_map _ _ (rename (b (t g))) (s2e_rename_preserves_origin_powers (b (t g)))).comp
          (s2e_adic_algebra_map _ _ (rename e) (s2e_rename_preserves_origin_powers e)) =
        (s2e_adic_algebra_map _ _ (rename e) (s2e_rename_preserves_origin_powers e)).comp
          (s2e_adic_algebra_map _ _ (rename (a g)) (s2e_rename_preserves_origin_powers (a g)))
      rw [s2e_adic_algebra_map_comp, s2e_adic_algebra_map_comp]
      congr 1
      apply AlgHom.ext
      intro p
      change rename (b (t g)) (rename e p) = rename e (rename (a g) p)
      rw [← h g, rename_rename, rename_rename]
      apply congrArg (fun f : σ → τ => rename f p)
      funext i
      simp only [Function.comp_apply, Equiv.permCongr_apply, e.symm_apply_apply])
  exact C.trans (Subalgebra.equivOfEq K L hKL)

#print axioms s2e_adic_renamed_reindexed_invariants
end HodgeLean.Foundations.Program
