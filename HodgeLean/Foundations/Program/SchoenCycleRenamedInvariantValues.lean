import HodgeLean.Foundations.Program.SchoenCycleRenamedInvariantAlgebras

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The invariant algebra transport retains the actual polynomial variable renaming.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_renamed_invariant_apply
    {R σ τ G H : Type*} [CommRing R]
    (e : σ ≃ τ) (t : G ≃ H) (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ)
    (h : ∀ g, e.permCongr (a g) = b (t g))
    (p : (⨅ g, AlgHom.equalizer (rename (a g)) (AlgHom.id R (MvPolynomial σ R)) :
      Subalgebra R (MvPolynomial σ R))) :
    (s2e_renamed_reindexed_invariant_equiv e t a b h p).val = rename e p.val := rfl

/-- The inverse invariant algebra transport retains the actual inverse variable renaming.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_renamed_invariant_symm_apply
    {R σ τ G H : Type*} [CommRing R]
    (e : σ ≃ τ) (t : G ≃ H) (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ)
    (h : ∀ g, e.permCongr (a g) = b (t g))
    (p : (⨅ g, AlgHom.equalizer (rename (b g)) (AlgHom.id R (MvPolynomial τ R)) :
      Subalgebra R (MvPolynomial τ R))) :
    ((s2e_renamed_reindexed_invariant_equiv e t a b h).symm p).val = rename e.symm p.val := by
  let E := s2e_renamed_reindexed_invariant_equiv (R := R) e t a b h
  apply (renameEquiv R e).injective
  have he := s2e_renamed_invariant_apply e t a b h (E.symm p)
  change (E (E.symm p)).val = rename e (E.symm p).val at he
  rw [E.apply_symm_apply] at he
  change rename e (E.symm p).val = (renameEquiv R e) ((renameEquiv R e).symm p.val)
  rw [AlgEquiv.apply_symm_apply]
  exact he.symm

end HodgeLean.Foundations.Program
