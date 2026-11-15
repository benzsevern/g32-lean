import HodgeLean.Foundations.Program.SchoenCycleSumElementaryInvariants
import HodgeLean.Foundations.Program.SchoenCycleBlockHeadTail
import HodgeLean.Foundations.Program.SchoenCycleRenamedInvariantAlgebras

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Elementary coordinates in all indexed blocks identify their polynomial algebra with the invariants of the actual independent block permutations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_mixed_polynomial_invariant_coordinates
    (R : Type*) [CommRing R] (b : ℕ) (m : Fin b → ℕ) :
    MvPolynomial (Σ a, Fin (m a)) R ≃ₐ[R]
      (⨅ ρ : (a : Fin b) → Equiv.Perm (Fin (m a)),
        AlgHom.equalizer (rename (Equiv.Perm.sigmaCongrRight ρ))
          (AlgHom.id R (MvPolynomial (Σ a, Fin (m a)) R)) :
        Subalgebra R (MvPolynomial (Σ a, Fin (m a)) R)) := by
  classical
  induction b with
  | zero =>
    let P := MvPolynomial (Σ a, Fin (m a)) R
    let K : Subalgebra R P := ⨅ ρ : (a : Fin 0) → Equiv.Perm (Fin (m a)),
      AlgHom.equalizer (rename (Equiv.Perm.sigmaCongrRight ρ)) (AlgHom.id R P)
    have hmem (p : P) : p ∈ K := by
      simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      intro ρ
      have he : Equiv.Perm.sigmaCongrRight ρ = Equiv.refl (Σ a, Fin (m a)) := by
        apply Equiv.ext
        intro v
        exact Fin.elim0 v.1
      rw [he]
      exact rename_id_apply p
    let f : P →ₐ[R] K := (AlgHom.id R P).codRestrict K hmem
    apply AlgEquiv.ofBijective f
    constructor
    · intro p q h
      exact congrArg Subtype.val h
    · intro p
      exact ⟨p.val, Subtype.ext rfl⟩
  | succ b ih =>
    let β := fun a : Fin (b + 1) => Fin (m a)
    let T := Σ a : Fin b, Fin (m a.succ)
    let e := s2e_sigma_head_tail β
    let t := Equiv.Perm.sigmaCongrRightHom (fun a : Fin b => Fin (m a.succ))
    let D := s2e_renamed_reindexed_invariant_equiv (R := R) e
      (s2e_block_family_head_tail β).toEquiv
      (fun ρ => Equiv.Perm.sigmaCongrRight ρ)
      (fun v => Equiv.sumCongr v.1 (t v.2))
      (s2e_sigma_head_tail_permutation β)
    let H : MvPolynomial (Fin (m 0))
        (⨅ ρ : (a : Fin b) → Equiv.Perm (Fin (m a.succ)),
          AlgHom.equalizer (rename (Equiv.Perm.sigmaCongrRight ρ)) (AlgHom.id R (MvPolynomial T R)) :
          Subalgebra R (MvPolynomial T R)) ≃ₐ[R]
        (⨅ v : Equiv.Perm (Fin (m 0)) × ((a : Fin b) → Equiv.Perm (Fin (m a.succ))),
          AlgHom.equalizer (rename (Sum.map v.1 (t v.2)))
            (AlgHom.id R (MvPolynomial (Fin (m 0) ⊕ T) R)) :
          Subalgebra R (MvPolynomial (Fin (m 0) ⊕ T) R)) := by
      let F : Subalgebra R (MvPolynomial T R) := ⨅ ρ : (a : Fin b) → Equiv.Perm (Fin (m a.succ)),
        AlgHom.equalizer (rename (Equiv.Perm.sigmaCongrRight ρ)) (AlgHom.id R (MvPolynomial T R))
      exact ((renameEquiv F (finCongr (Fintype.card_fin (m 0)).symm)).restrictScalars R).trans
        (s2e_sum_elementary_invariant_equiv (R := R) (σ := Fin (m 0)) t)
    exact (renameEquiv R e).trans ((sumAlgEquiv R (Fin (m 0)) T).trans
      ((MvPolynomial.mapAlgEquiv (Fin (m 0)) (ih (fun a => m a.succ))).trans (H.trans D.symm)))

end HodgeLean.Foundations.Program
