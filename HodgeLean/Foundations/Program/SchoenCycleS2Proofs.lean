module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # S2 affine residue intersection infrastructure
Implication from distinct coordinate equations to their actual quotient ring.
This is the first affine piece; projective gluing, conormal sheaves and tower
compatibility are separate review units. HC no distance; AV milestone no distance.
-/
public section

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program
/-- The residue chart equations retain their full ideal, including multiplicity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi),
printed pp. 13–14; Lemma 2.4 proof, printed p. 15.
This is the polynomial chart calculation, before identification with the slice. -/
theorem s2e_chain_residue_coordinate_kernel_aux
    (n : ℕ) (T : Finset (Fin n)) :
    RingHom.ker (MvPolynomial.killCompl
      (R := ℂ) (f := fun i : {i : Fin n // i ∉ T} => i.val)
      Subtype.val_injective).toRingHom =
      Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n))) := by
  classical
  let f : {i : Fin n // i ∉ T} → Fin n := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  ext p
  rw [RingHom.mem_ker, MvPolynomial.mem_ideal_span_X_image]
  change killCompl hf p = 0 ↔ _
  constructor
  · intro hp m hm
    by_contra h
    have hs : ↑m.support ⊆ Set.range f := by
      intro i hi
      refine ⟨⟨i, ?_⟩, rfl⟩
      intro hiT
      exact h ⟨i, hiT, Finsupp.mem_support_iff.mp hi⟩
    have hc := congrArg (fun r : MvPolynomial {i : Fin n // i ∉ T} ℂ =>
      r.coeff (m.comapDomain f hf.injOn)) hp
    rw [MvPolynomial.coeff_killCompl,
      Finsupp.mapDomain_comapDomain f hf m hs, AddMonoidAlgebra.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  · intro hp
    ext m
    rw [MvPolynomial.coeff_killCompl, AddMonoidAlgebra.coeff_zero]
    by_contra h
    obtain ⟨i, hiT, hi⟩ := hp _ (MvPolynomial.mem_support_iff.mpr h)
    have hs := Finsupp.mapDomain_support (f := f) (s := m)
      (Finsupp.mem_support_iff.mpr hi)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hs
    subst i
    exact j.property hiT

/-- The affine intersection has precisely the remaining polynomial coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(vi),
printed pp. 13–14; Lemma 2.4 proof, printed p. 15.
This is an affine coordinate-ring assertion, without projective gluing. -/
theorem s2e_chain_residue_coordinate_quotient_aux
    (n : ℕ) (T : Finset (Fin n)) :
    ∃ e : (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n)))) ≃ₐ[ℂ]
          MvPolynomial {i : Fin n // i ∉ T} ℂ,
      ∀ p, e (Ideal.Quotient.mk _ p) =
        MvPolynomial.killCompl (R := ℂ)
          (f := fun i : {i : Fin n // i ∉ T} => i.val) Subtype.val_injective p := by
  let f := MvPolynomial.killCompl (R := ℂ)
    (f := fun i : {i : Fin n // i ∉ T} => i.val) Subtype.val_injective
  have hf : Function.Surjective f := fun p =>
    ⟨MvPolynomial.rename Subtype.val p,
      MvPolynomial.killCompl_rename_app Subtype.val_injective p⟩
  have hker : RingHom.ker f =
      Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n))) := by
    exact s2e_chain_residue_coordinate_kernel_aux n T
  refine ⟨(Ideal.quotientEquivAlgOfEq ℂ hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf), ?_⟩
  intro p
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end HodgeLean.Foundations.Program
