import HodgeLean.Foundations.Program.SchoenCyclePolynomialCoefficientInvariants
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Symmetric polynomials invariant under coefficient actions have their actual elementary coordinates over the invariant coefficient algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_symmetric_coefficient_invariant_equiv
    {k S G σ : Type*} [CommRing k] [CommRing S] [Algebra k S] [Fintype σ]
    (α : G → S →ₐ[k] S) :
    let F : Subalgebra k S := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S)
    let P : Subalgebra k (MvPolynomial σ S) := ⨅ g,
      AlgHom.equalizer (MvPolynomial.mapAlgHom (α g)) (AlgHom.id k (MvPolynomial σ S))
    MvPolynomial (Fin (Fintype.card σ)) F ≃ₐ[k]
      ((symmetricSubalgebra σ S).restrictScalars k ⊓ P : Subalgebra k (MvPolynomial σ S)) := by
  classical
  dsimp only
  let F : Subalgebra k S := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S)
  let P : Subalgebra k (MvPolynomial σ S) := ⨅ g,
    AlgHom.equalizer (MvPolynomial.mapAlgHom (α g)) (AlgHom.id k (MvPolynomial σ S))
  let K := (symmetricSubalgebra σ S).restrictScalars k ⊓ P
  let E := s2e_polynomial_coefficient_invariant_equiv (σ := σ) α
  let f : symmetricSubalgebra σ F →ₐ[k] MvPolynomial σ S :=
    (MvPolynomial.mapAlgHom F.val).comp ((symmetricSubalgebra σ F).val.restrictScalars k)
  have hmem (q : symmetricSubalgebra σ F) : f q ∈ K := by
    constructor
    · exact q.property.map F.val.toRingHom
    · exact (E q.val).property
  let e := f.codRestrict K hmem
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      apply Subtype.ext
      apply MvPolynomial.map_injective F.val.toRingHom Subtype.val_injective
      exact congrArg Subtype.val h
    · intro p
      obtain ⟨q, hq⟩ := E.surjective ⟨p.val, p.property.2⟩
      have hq' : MvPolynomial.map F.val.toRingHom q = p.val := congrArg Subtype.val hq
      have hs : q.IsSymmetric := by
        intro ρ
        apply MvPolynomial.map_injective F.val.toRingHom Subtype.val_injective
        rw [map_rename, hq']
        exact p.property.1 ρ
      exact ⟨⟨q, hs⟩, Subtype.ext hq'⟩
  exact ((esymmAlgEquiv σ F rfl).restrictScalars k).trans (AlgEquiv.ofBijective e he)

end HodgeLean.Foundations.Program
