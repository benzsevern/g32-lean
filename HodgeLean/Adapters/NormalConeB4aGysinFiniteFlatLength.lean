import HodgeLean.Adapters.NormalConeB4aGysinLocalLengthDimension
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Length conservation in finite flat families

The dimension of a finite algebra is the sum of its local lengths when the
ground field is algebraically closed.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- A finite algebra over an algebraically closed field has dimension equal
to the sum of the lengths at its points. -/
theorem a3b4a_gysin_finrank_eq_sum_local_lengths
    {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Module.Finite k A] [Fintype (PrimeSpectrum A)] :
    (Module.finrank k A : ℕ∞) = ∑ p : PrimeSpectrum A,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  letI : IsArtinianRing A := isArtinian_of_tower k (inferInstance : IsArtinian k A)
  have (p : PrimeSpectrum A) : Module.Finite k (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective
      (Algebra.algHom k A (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum A k, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (a3b4a_gysin_local_length_eq_finrank (k := k)).symm

/-- A reduced finite algebra over an algebraically closed field has one
unit of dimension for each point of its prime spectrum. -/
theorem a3b4a_gysin_reduced_finrank_eq_card
    {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsReduced A]
    [Algebra k A] [Module.Finite k A] [Fintype (PrimeSpectrum A)] :
    Module.finrank k A = Fintype.card (PrimeSpectrum A) := by
  letI : IsArtinianRing A := isArtinian_of_tower k (inferInstance : IsArtinian k A)
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum A k]
  have hone (p : PrimeSpectrum A) : Module.finrank k (Localization.AtPrime p.asIdeal) = 1 := by
    let L := Localization.AtPrime p.asIdeal
    have : Module.Finite k L :=
      Module.Finite.of_surjective (Algebra.algHom k A L).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl L)
    letI : Field L := (IsArtinianRing.isField_of_isReduced_of_isLocalRing L).toField
    exact Module.finrank_of_bijective_algebraMap
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := L))
  simp_rw [hone]
  simp

/-- In a finite flat family over a domain, the length of a local fibre is
the number of points of any reduced fibre with algebraically closed residue field. -/
theorem a3b4a_gysin_local_fibre_length_eq_reduced_fibre_card
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsAlgClosed p.ResidueField] [IsAlgClosed q.ResidueField]
    [IsLocalRing (p.Fiber A)] [IsReduced (q.Fiber A)]
    [Fintype (PrimeSpectrum (q.Fiber A))] :
    Module.length (p.Fiber A) (p.Fiber A) =
      (Fintype.card (PrimeSpectrum (q.Fiber A)) : ℕ∞) := by
  rw [a3b4a_gysin_local_length_eq_finrank (k := p.ResidueField),
    ← a3b4a_gysin_reduced_finrank_eq_card (k := q.ResidueField),
    p.finrank_fiber_eq_finrank, q.finrank_fiber_eq_finrank]

set_option backward.isDefEq.respectTransparency.types false in
/-- The points of a finite algebra over an algebraically closed field are
its ground-field-valued algebra homomorphisms, including for nonreduced algebras. -/
def a3b4a_gysin_algHomEquivPrimeSpectrum
    (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Module.Finite k A] : (A →ₐ[k] k) ≃ PrimeSpectrum A where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ p.asIdeal))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
        (K := A ⧸ p.asIdeal))).symm.toAlgHom
    (Ideal.Quotient.mkₐ k p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ RingHom.ker f))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
        (K := A ⧸ RingHom.ker f))).injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.coe_ofBijective, Algebra.ofId_apply,
      IsScalarTower.algebraMap_apply k A]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom, AlgEquiv.toAlgHom_toRingHom,
      AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, ← RingHom.ker_coe_toRingHom,
      Ideal.Quotient.mkₐ_ker]

/-- A local special fibre retains the number of ground-field-valued points
of a reduced fibre in a finite flat family over a domain. -/
theorem a3b4a_gysin_local_fibre_length_eq_point_count
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsAlgClosed p.ResidueField] [IsAlgClosed q.ResidueField]
    [IsLocalRing (p.Fiber A)] [IsReduced (q.Fiber A)] :
    Module.length (p.Fiber A) (p.Fiber A) =
      (Nat.card (q.Fiber A →ₐ[q.ResidueField] q.ResidueField) : ℕ∞) := by
  classical
  letI : IsArtinianRing (q.Fiber A) :=
    isArtinian_of_tower q.ResidueField (inferInstance : IsArtinian q.ResidueField (q.Fiber A))
  letI : Fintype (PrimeSpectrum (q.Fiber A)) := Fintype.ofFinite _
  rw [a3b4a_gysin_local_fibre_length_eq_reduced_fibre_card p q,
    Nat.card_congr (a3b4a_gysin_algHomEquivPrimeSpectrum q.ResidueField (q.Fiber A)),
    Nat.card_eq_fintype_card]

/-- Finite flatness conserves the sum of exact local lengths even when the
comparison fibre is nonreduced. -/
theorem a3b4a_gysin_local_fibre_length_eq_sum_fibre_lengths
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsAlgClosed p.ResidueField] [IsAlgClosed q.ResidueField]
    [IsLocalRing (p.Fiber A)] [Fintype (PrimeSpectrum (q.Fiber A))] :
    Module.length (p.Fiber A) (p.Fiber A) =
      ∑ x : PrimeSpectrum (q.Fiber A),
        Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal) := by
  rw [a3b4a_gysin_local_length_eq_finrank (k := p.ResidueField),
    ← a3b4a_gysin_finrank_eq_sum_local_lengths (k := q.ResidueField),
    p.finrank_fiber_eq_finrank, q.finrank_fiber_eq_finrank]

/-- The exact local lengths of an enumerated comparison fibre sum to the
local special fibre length, as rational coefficients. -/
theorem a3b4a_gysin_sum_fibre_length_coefficients
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsAlgClosed p.ResidueField] [IsAlgClosed q.ResidueField]
    [IsLocalRing (p.Fiber A)]
    {ι : Type*} [Fintype ι] (e : ι ≃ PrimeSpectrum (q.Fiber A)) :
    (∑ x : ι, ((Module.length (Localization.AtPrime (e x).asIdeal)
      (Localization.AtPrime (e x).asIdeal)).toNat : ℚ)) =
        ((Module.length (p.Fiber A) (p.Fiber A)).toNat : ℚ) := by
  classical
  letI : Fintype (PrimeSpectrum (q.Fiber A)) := Fintype.ofEquiv ι e
  letI : IsArtinianRing (q.Fiber A) :=
    isArtinian_of_tower q.ResidueField (inferInstance : IsArtinian q.ResidueField (q.Fiber A))
  have (x : PrimeSpectrum (q.Fiber A)) :
      Module.Finite q.ResidueField (Localization.AtPrime x.asIdeal) :=
    Module.Finite.of_surjective
      (Algebra.algHom q.ResidueField (q.Fiber A) (Localization.AtPrime x.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective x.asIdeal.primeCompl _)
  simp_rw [a3b4a_gysin_local_length_eq_finrank (k := q.ResidueField), ENat.toNat_natCast]
  rw [← Nat.cast_sum, e.sum_comp (fun x =>
    Module.finrank q.ResidueField (Localization.AtPrime x.asIdeal)),
    ← IsArtinianRing.finrank_eq_sum_primeSpectrum (q.Fiber A) q.ResidueField,
    q.finrank_fiber_eq_finrank,
    a3b4a_gysin_local_length_eq_finrank (k := p.ResidueField),
    ENat.toNat_natCast, p.finrank_fiber_eq_finrank]

end HodgeLean.Adapters
