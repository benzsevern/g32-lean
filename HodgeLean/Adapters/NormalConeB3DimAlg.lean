import HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension
import HodgeLean.Adapters.KleimanCoheightAlgebra

/-! # Diagonal cone coefficient: dimension theory of finite-type algebras over a field

The transcendence degree computes the Krull dimension of a finitely generated domain over a field,
quasi-finite maps preserve the dimension of prime quotients, and the dimension formula
`ht P + dim S/P = dim S` holds for finitely generated domains. These are the statements of the
HodgeConjecture package and of `hc9k8_height_add_ringKrullDim_quotient`, for algebras in an
arbitrary universe.
-/

noncomputable section
namespace HodgeLean.Adapters
open Ideal

universe u

section
variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- A finite-type domain over a field has finite Krull dimension equal to its transcendence degree.
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; Mathlib,
`exists_finite_inj_algHom_of_fg` (Noether normalization). -/
theorem a3b3_exists_ringKrullDim_eq_trdeg :
    ∃ n : ℕ, ringKrullDim A = n ∧ Algebra.trdeg k A = n := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
  let : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : Algebra.IsIntegral (MvPolynomial (Fin n) k) A :=
    ⟨hfinite.to_isIntegral⟩
  refine ⟨n, ?_, ?_⟩
  · rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    simp
  · have h := trdeg_add_eq k (MvPolynomial (Fin n) k) (A := A)
    have hzero : Algebra.trdeg (MvPolynomial (Fin n) k) A = 0 := trdeg_eq_zero
    rw [hzero, add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin] at h
    rw [← h]
    simp

end

section
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- Passing from a prime quotient to its fraction field preserves transcendence degree.
Source: Mathlib, `trdeg_add_eq`. -/
theorem a3b3_trdeg_quotient_eq_residueField (P : Ideal R) [P.IsPrime] :
    Algebra.trdeg k (R ⧸ P) = Algebra.trdeg k P.ResidueField := by
  have h := trdeg_add_eq k (R ⧸ P) (A := P.ResidueField)
  have hzero : Algebra.trdeg (R ⧸ P) P.ResidueField = 0 := trdeg_eq_zero
  rw [hzero, add_zero] at h
  exact h

variable {S : Type u} [CommRing S] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra.QuasiFinite R S]

/-- A quasi-finite map induces algebraic extensions of residue fields.
Source: Mathlib, `trdeg_add_eq`; HodgeConjecture, `Algebra.QuasiFinite.trdeg_residueField_eq`. -/
theorem a3b3_quasiFinite_trdeg_residueField_eq (P : Ideal S) [P.IsPrime] :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k (P.under R).ResidueField := by
  let q : Ideal R := P.under R
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver q P
  have h := trdeg_add_eq k q.ResidueField (A := P.ResidueField)
  have hzero : Algebra.trdeg q.ResidueField P.ResidueField = 0 := trdeg_eq_zero
  rw [hzero, add_zero] at h
  exact h.symm

variable [Algebra.FiniteType k R] [Algebra.FiniteType k S]

include k in
/-- A quasi-finite map between finite-type algebras over a field preserves the dimension of prime
quotients.
Source: HodgeConjecture, `Algebra.QuasiFinite.ringKrullDim_quotient_eq`. -/
theorem a3b3_quasiFinite_ringKrullDim_quotient_eq (P : Ideal S) [P.IsPrime] :
    ringKrullDim (S ⧸ P) = ringKrullDim (R ⧸ P.under R) := by
  let q : Ideal R := P.under R
  obtain ⟨n, hnDim, hnTrdeg⟩ := a3b3_exists_ringKrullDim_eq_trdeg (k := k) (A := R ⧸ q)
  obtain ⟨m, hmDim, hmTrdeg⟩ := a3b3_exists_ringKrullDim_eq_trdeg (k := k) (A := S ⧸ P)
  have htr : Algebra.trdeg k (S ⧸ P) = Algebra.trdeg k (R ⧸ q) :=
    (a3b3_trdeg_quotient_eq_residueField (k := k) P).trans
      ((a3b3_quasiFinite_trdeg_residueField_eq (k := k) (R := R) P).trans
        (a3b3_trdeg_quotient_eq_residueField (k := k) q).symm)
  have hmn : m = n := by exact_mod_cast hmTrdeg.symm.trans (htr.trans hnTrdeg)
  rw [hmDim, hnDim, hmn]

end

/-- The dimension formula: for a finitely generated domain over a field, the height of a prime plus
the dimension of its quotient is the dimension of the ring.
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; theorem
`hc9k8_height_add_ringKrullDim_quotient`. -/
theorem a3b3_height_add_ringKrullDim_quotient {k S : Type u} [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.FiniteType k S] (P : Ideal S) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (S ⧸ P) = ringKrullDim S := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k S
  let : Algebra (MvPolynomial (Fin n) k) S := g.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) S :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have : FaithfulSMul (MvPolynomial (Fin n) k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Module.Finite (MvPolynomial (Fin n) k) S := hfinite
  have : Algebra.IsIntegral (MvPolynomial (Fin n) k) S := inferInstance
  have hheight : P.height = (P.under (MvPolynomial (Fin n) k)).height :=
    hc9k8_height_eq_height_under P
  have hquot : ringKrullDim (S ⧸ P) =
      ringKrullDim (MvPolynomial (Fin n) k ⧸ P.under (MvPolynomial (Fin n) k)) :=
    a3b3_quasiFinite_ringKrullDim_quotient_eq (k := k) (R := MvPolynomial (Fin n) k) P
  have hdim : ringKrullDim S = n := by
    rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    simp
  rw [hheight, hquot, hdim]
  exact PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin _

end HodgeLean.Adapters
