import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Valuations of a Dedekind domain through a localization

For a Dedekind domain `R` with fraction field `K` and a nonzero prime `v`, the valuation of the
DVR `R_v` on `K` is the `v`-adic valuation, and both equal `exp (-count_v (f))`. So the order of
vanishing `Ring.ordFrac R_v` reads off the exponent of `v` in the factorization of `(f)`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open IsDedekindDomain FractionalIdeal WithZero
open scoped nonZeroDivisors

namespace HodgeLean.Foundations.Curves.DedekindValuation

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)
variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalization.AtPrime S v.asIdeal]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra S K]
  [IsFractionRing S K] [IsScalarTower R S K]

theorem mem_map_pow_iff (r : R) (n : ℕ) :
    algebraMap R S r ∈ (IsLocalRing.maximalIdeal S) ^ n ↔ r ∈ v.asIdeal ^ n := by
  have := IsLocalization.AtPrime.isLocalRing S v.asIdeal
  rcases n with _ | n
  · simp
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal S, ← Ideal.map_pow]
  have hprim : (v.asIdeal ^ (n + 1)).IsPrimary := by
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [Ideal.radical_pow v.asIdeal (Nat.succ_ne_zero n), v.isPrime.radical]
    exact v.isMaximal
  have hdisj : Disjoint (v.asIdeal.primeCompl : Set R) (v.asIdeal ^ (n + 1) : Ideal R) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact ha (Ideal.pow_le_self (Nat.succ_ne_zero n) ha')
  conv_rhs => rw [← IsLocalization.under_map_of_isPrimary_disjoint v.asIdeal.primeCompl S hprim hdisj]
  rfl

theorem intValuation_algebraMap (r : R) :
    (IsDiscreteValuationRing.maximalIdeal S).intValuation (algebraMap R S r) =
      v.intValuation r := by
  by_cases hr : r = 0
  · simp [hr]
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  have hr' : algebraMap R S r ≠ 0 := fun h ↦ hr (hinj (h.trans (map_zero _).symm))
  rw [HeightOneSpectrum.intValuation_if_neg _ hr', HeightOneSpectrum.intValuation_if_neg _ hr]
  set k := (Associates.mk (IsDiscreteValuationRing.maximalIdeal S).asIdeal).count
    (Associates.mk (Ideal.span {algebraMap R S r})).factors
  set l := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors
  have key : ∀ n : ℕ, exp (-(k : ℤ)) ≤ exp (-(n : ℤ)) ↔ exp (-(l : ℤ)) ≤ exp (-(n : ℤ)) := by
    intro n
    have h1 := (IsDiscreteValuationRing.maximalIdeal S).intValuation_le_pow_iff_mem
      (algebraMap R S r) n
    have h2 := v.intValuation_le_pow_iff_mem r n
    rw [HeightOneSpectrum.intValuation_if_neg _ hr'] at h1
    rw [HeightOneSpectrum.intValuation_if_neg _ hr] at h2
    rw [h1, h2]
    exact mem_map_pow_iff v r n
  have hkl : k = l := by
    apply le_antisymm
    · have := (key k).mp le_rfl
      rw [exp_le_exp] at this
      omega
    · have := (key l).mpr le_rfl
      rw [exp_le_exp] at this
      omega
  rw [hkl]

theorem valuation_eq (f : K) :
    (IsDiscreteValuationRing.maximalIdeal S).valuation K f = v.valuation K f := by
  have h : ∀ r : R, (IsDiscreteValuationRing.maximalIdeal S).valuation K (algebraMap R K r) =
      v.valuation K (algebraMap R K r) := by
    intro r
    rw [HeightOneSpectrum.valuation_of_algebraMap, IsScalarTower.algebraMap_apply R S K r,
      HeightOneSpectrum.valuation_of_algebraMap, intValuation_algebraMap (S := S) v]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, map_div₀, h, h]

theorem valuation_eq_exp_neg_count (f : K) (hf : f ≠ 0) :
    v.valuation K f = exp (-count K v (spanSingleton R⁰ f)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hspan : ∀ r : R, r ≠ 0 →
      count K v (spanSingleton R⁰ (algebraMap R K r)) =
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors := by
    intro r hr
    rw [← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]
  have hne : ∀ r : R, r ≠ 0 → spanSingleton R⁰ (algebraMap R K r) ≠ 0 := by
    intro r hr
    rw [ne_eq, spanSingleton_eq_zero_iff]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hr))
  rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, ← spanSingleton_inv,
    count_mul K v (hne a ha0) (inv_ne_zero (hne b hb0)), count_inv, hspan a ha0, hspan b hb0,
    map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha0,
    HeightOneSpectrum.intValuation_if_neg _ hb0, ← exp_neg, ← exp_add]
  congr 1
  ring

/-- The order of vanishing in the localization `R_v` is the exponent of `v` in `(f)`.
Source: Neukirch, *Algebraic Number Theory*, I.11; Mathlib `Ring.ordFrac_eq_valuation_inv`. -/
theorem ordFrac_eq_exp_count (f : K) (hf : f ≠ 0) :
    Ring.ordFrac S f = exp (count K v (spanSingleton R⁰ f)) := by
  rw [Ring.ordFrac_eq_valuation_inv, valuation_eq v, valuation_eq_exp_neg_count v f hf, ← exp_neg,
    neg_neg]

end HodgeLean.Foundations.Curves.DedekindValuation
