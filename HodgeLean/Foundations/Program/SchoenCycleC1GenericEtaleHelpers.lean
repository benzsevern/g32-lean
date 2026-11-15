import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.FractionRing

/-! # Etale neighbourhoods of the generic source of a finite cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A separable extension of the actual fraction fields gives etaleness
at the generic source prime of the ring extension. -/
theorem s2e_c1_etaleAt_generic_of_fractionFields
    (R S K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing S L] [Algebra.IsSeparable K L] :
    Algebra.IsEtaleAt R (⊥ : Ideal S) := by
  haveI : Algebra.FormallyEtale R K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  haveI : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R K L
  have heq : (⊥ : Ideal S).primeCompl = nonZeroDivisors S := by
    ext x
    simp only [Ideal.mem_primeCompl_iff, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsLocalization (⊥ : Ideal S).primeCompl L := by
    rw [heq]
    infer_instance
  let e := (IsLocalization.algEquiv (⊥ : Ideal S).primeCompl L
    (Localization.AtPrime (⊥ : Ideal S))).restrictScalars R
  exact Algebra.FormallyEtale.of_equiv e

/-- For a finite domain extension, generic source etaleness extends over
a nonempty basic open of the base, retaining the entire inverse image. -/
theorem s2e_c1_exists_base_etale_basicOpen
    (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Algebra.FinitePresentation R S]
    [Algebra.IsEtaleAt R (⊥ : Ideal S)] :
    ∃ r : R, r ≠ 0 ∧ Algebra.Etale R (Localization.Away (algebraMap R S r)) := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  let Z := (Algebra.etaleLocus R S)ᶜ
  have hZ : IsClosed Z := (Algebra.isOpen_etaleLocus (R := R) (A := S)).isClosed_compl
  have hc : IsClosed (f '' Z) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S)
      (fun x => Algebra.IsIntegral.isIntegral x) Z hZ
  have hb : (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ (f '' Z)ᶜ := by
    rintro ⟨q, hq, he⟩
    have hqbot : q.asIdeal = ⊥ :=
      Ideal.eq_bot_of_under_eq_bot (congrArg PrimeSpectrum.asIdeal he)
    have heq : q = (⟨⊥, inferInstance⟩ : PrimeSpectrum S) := PrimeSpectrum.ext hqbot
    subst q
    exact hq (inferInstance : Algebra.IsEtaleAt R (⊥ : Ideal S))
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hb hc.isOpen_compl
  refine ⟨r, ?_, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  · change r ∉ (⊥ : Ideal R) at hr
    simpa only [Ideal.mem_bot] using hr
  · intro q hq
    by_contra hn
    have hqr : f q ∈ PrimeSpectrum.basicOpen r := hq
    exact hsub hqr ⟨q, hn, rfl⟩


/-- A finite injective domain extension in characteristic zero has an
etale entire inverse image over some nonempty base basic open. -/
theorem s2e_c1_finite_charZero_exists_base_etale_basicOpen
    (R S : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    ∃ r : R, r ≠ 0 ∧ Algebra.Etale R (Localization.Away (algebraMap R S r)) := by
  let K := FractionRing R
  let L := FractionRing S
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Algebra.IsAlgebraic K L := isAlgebraic_of_isFractionRing R S K L
  haveI : Algebra.IsEtaleAt R (⊥ : Ideal S) :=
    s2e_c1_etaleAt_generic_of_fractionFields R S K L
  exact s2e_c1_exists_base_etale_basicOpen R S


end HodgeLean.Foundations.Program
