import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Coefficientwise invariants in a polynomial algebra are polynomials over the actual invariant coefficient subalgebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_polynomial_coefficient_invariant_equiv
    {k S G σ : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (α : G → S →ₐ[k] S) :
    MvPolynomial σ (⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S) : Subalgebra k S) ≃ₐ[k]
      (⨅ g, AlgHom.equalizer (MvPolynomial.mapAlgHom (α g))
        (AlgHom.id k (MvPolynomial σ S)) : Subalgebra k (MvPolynomial σ S)) := by
  classical
  let F : Subalgebra k S := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id k S)
  let P : Subalgebra k (MvPolynomial σ S) := ⨅ g,
    AlgHom.equalizer (MvPolynomial.mapAlgHom (α g)) (AlgHom.id k (MvPolynomial σ S))
  let f := MvPolynomial.mapAlgHom (σ := σ) F.val
  have hmem (q : MvPolynomial σ F) : f q ∈ P := by
    simp only [P, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    intro g
    apply MvPolynomial.ext
    intro d
    change α g ((q.coeff d).val) = (q.coeff d).val
    exact Algebra.mem_iInf.mp (q.coeff d).property g
  let e := f.codRestrict P hmem
  apply AlgEquiv.ofBijective e
  constructor
  · intro p q h
    apply MvPolynomial.map_injective F.val.toRingHom Subtype.val_injective
    exact congrArg Subtype.val h
  · intro p
    have hcoeff (d : σ →₀ ℕ) : p.val.coeff d ∈ F := by
      simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      intro g
      have hh := Algebra.mem_iInf.mp p.property g
      have he := congrArg (fun q : MvPolynomial σ S => q.coeff d) hh
      exact he
    have hrange : p.val ∈ Set.range (MvPolynomial.map F.val.toRingHom) := by
      apply mem_range_map_iff_coeffs_subset.mpr
      intro c hc
      obtain ⟨d, _, rfl⟩ := mem_coeffs_iff.mp hc
      exact ⟨⟨p.val.coeff d, hcoeff d⟩, rfl⟩
    obtain ⟨q, hq⟩ := hrange
    exact ⟨q, Subtype.ext hq⟩

end HodgeLean.Foundations.Program
