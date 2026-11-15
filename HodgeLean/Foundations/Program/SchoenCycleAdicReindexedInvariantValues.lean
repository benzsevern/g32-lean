import HodgeLean.Foundations.Program.SchoenCycleAdicRenamedInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Reindexing the full formal invariant family retains the actual root-renaming map on ambient values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_adic_reindexed_invariants_val
    {R σ τ G H : Type*} [CommRing R]
    (e : σ ≃ τ) (t : G ≃ H) (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ)
    (h : ∀ g, e.permCongr (a g) = b (t g)) :
    let P := AdicCompletion (idealOfVars σ R) (MvPolynomial σ R)
    let Q := AdicCompletion (idealOfVars τ R) (MvPolynomial τ R)
    let α g := s2e_adic_algebra_map _ _ (rename (a g))
      (s2e_rename_preserves_origin_powers (a g))
    let β g : Q →ₐ[R] Q := s2e_adic_algebra_map _ _ (rename (b g))
      (s2e_rename_preserves_origin_powers (b g))
    ∀ x : (⨅ g, AlgHom.equalizer (α g) (AlgHom.id R P) : Subalgebra R P),
      (s2e_adic_renamed_reindexed_invariants e t a b h x).val =
        s2e_adic_rename_equiv e x.val := by
  dsimp only
  intro x
  rfl

#print axioms s2e_adic_reindexed_invariants_val
end HodgeLean.Foundations.Program
