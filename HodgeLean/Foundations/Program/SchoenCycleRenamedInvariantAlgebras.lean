import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras
import Mathlib.Algebra.MvPolynomial.Rename

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Renaming variables and reindexing the actual permutation family retain its invariant algebra and original polynomial map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_renamed_reindexed_invariant_equiv
    {R σ τ G H : Type*} [CommRing R]
    (e : σ ≃ τ) (t : G ≃ H) (a : G → Equiv.Perm σ) (b : H → Equiv.Perm τ)
    (h : ∀ g, e.permCongr (a g) = b (t g)) :
    (⨅ g, AlgHom.equalizer (rename (a g)) (AlgHom.id R (MvPolynomial σ R)) :
      Subalgebra R (MvPolynomial σ R)) ≃ₐ[R]
    (⨅ g, AlgHom.equalizer (rename (b g)) (AlgHom.id R (MvPolynomial τ R)) :
      Subalgebra R (MvPolynomial τ R)) := by
  let K : Subalgebra R (MvPolynomial τ R) :=
    ⨅ g : G, AlgHom.equalizer (rename (b (t g))) (AlgHom.id R (MvPolynomial τ R))
  let L : Subalgebra R (MvPolynomial τ R) :=
    ⨅ g : H, AlgHom.equalizer (rename (b g)) (AlgHom.id R (MvPolynomial τ R))
  have hKL : K = L := by
    ext p
    simp only [K, L, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro hp g
      obtain ⟨g, rfl⟩ := t.surjective g
      exact hp g
    · intro hp g
      exact hp (t g)
  let C := s2e_intertwining_invariant_algebras_equiv (renameEquiv R e)
    (fun g => rename (a g)) (fun g => rename (b (t g))) (by
      intro g
      apply AlgHom.ext
      intro p
      change rename (b (t g)) (rename e p) = rename e (rename (a g) p)
      rw [← h g, rename_rename, rename_rename]
      apply congrArg (fun f : σ → τ => rename f p)
      funext i
      simp only [Function.comp_apply, Equiv.permCongr_apply, e.symm_apply_apply])
  exact C.trans (Subalgebra.equivOfEq K L hKL)

end HodgeLean.Foundations.Program
