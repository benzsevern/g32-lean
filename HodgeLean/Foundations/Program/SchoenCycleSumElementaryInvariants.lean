import HodgeLean.Foundations.Program.SchoenCycleSymmetricCoefficientInvariants
import HodgeLean.Foundations.Program.SchoenCycleSumBlockInvariants

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Taking elementary coordinates in one block retains the invariant coefficient algebra of all remaining blocks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_sum_elementary_invariant_equiv
    {R σ τ G : Type*} [CommRing R] [Group G] [Fintype σ]
    (t : G →* Equiv.Perm τ) :
    let F : Subalgebra R (MvPolynomial τ R) := ⨅ g,
      AlgHom.equalizer (rename (t g)) (AlgHom.id R (MvPolynomial τ R))
    MvPolynomial (Fin (Fintype.card σ)) F ≃ₐ[R]
      (⨅ v : Equiv.Perm σ × G,
        AlgHom.equalizer (rename (Sum.map v.1 (t v.2)))
          (AlgHom.id R (MvPolynomial (σ ⊕ τ) R)) : Subalgebra R (MvPolynomial (σ ⊕ τ) R)) := by
  classical
  dsimp only
  let F : Subalgebra R (MvPolynomial τ R) := ⨅ g,
    AlgHom.equalizer (rename (t g)) (AlgHom.id R (MvPolynomial τ R))
  let P : Subalgebra R (MvPolynomial σ (MvPolynomial τ R)) := ⨅ g,
    AlgHom.equalizer (MvPolynomial.mapAlgHom (rename (t g)))
      (AlgHom.id R (MvPolynomial σ (MvPolynomial τ R)))
  let K := (symmetricSubalgebra σ (MvPolynomial τ R)).restrictScalars R ⊓ P
  let L : Subalgebra R (MvPolynomial (σ ⊕ τ) R) := ⨅ v : Equiv.Perm σ × G,
    AlgHom.equalizer (rename (Sum.map v.1 (t v.2))) (AlgHom.id R (MvPolynomial (σ ⊕ τ) R))
  let E := sumAlgEquiv R σ τ
  have hL (p : MvPolynomial (σ ⊕ τ) R) : p ∈ L ↔ E p ∈ K := by
    simp only [L, K, P, Algebra.mem_iInf, Algebra.mem_inf, AlgHom.mem_equalizer,
      AlgHom.id_apply, Subalgebra.mem_restrictScalars]
    change (∀ v : Equiv.Perm σ × G, rename (Sum.map v.1 (t v.2)) p = p) ↔
      (E p).IsSymmetric ∧ ∀ g, map (rename (t g)).toRingHom (E p) = E p
    simpa only [Prod.forall] using s2e_sum_block_invariants_iff t p
  let e : K →ₐ[R] L := (E.symm.toAlgHom.comp K.val).codRestrict L (fun p => by
    apply (hL _).mpr
    change E (E.symm p.val) ∈ K
    rw [E.apply_symm_apply]
    exact p.property)
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact E.symm.injective (congrArg Subtype.val h)
    · intro p
      exact ⟨⟨E p.val, (hL p.val).mp p.property⟩,
        Subtype.ext (E.symm_apply_apply p.val)⟩
  exact (s2e_symmetric_coefficient_invariant_equiv (σ := σ) (fun g => rename (t g))).trans
    (AlgEquiv.ofBijective e he)

end HodgeLean.Foundations.Program
