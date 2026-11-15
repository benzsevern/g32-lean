import HodgeLean.Foundations.Curves.CurveValuation
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Ramification over `ℂ[t]` in a function field

Let `t` be transcendental in a field `K` finite over `ℂ⟮t⟯`. The integral closure `A` of `ℂ[t]`
in `K` is a Dedekind domain, finite and free over `ℂ[t]` of rank `[K : ℂ⟮t⟯]`. Over the prime
`(t)` all residue degrees are one, since `ℂ[t]/(t) ≅ ℂ` is algebraically closed, so the sum of the
orders of `t` in the local rings of `A` above `(t)` is `[K : ℂ⟮t⟯]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace HodgeLean.Foundations.Curves

variable {K : Type} [Field K] [Algebra ℂ K] (t : K)

/-- The element `t` of `ℂ[t]`. -/
def tGen : Algebra.adjoin ℂ {t} := ⟨t, Algebra.self_mem_adjoin_singleton ℂ t⟩

/-- The prime `(t)` of `ℂ[t]`. -/
def tIdeal : Ideal (Algebra.adjoin ℂ {t}) := Ideal.span {tGen t}

/-- Extending `(t)` along an algebra map gives the principal ideal of the image of `t`. -/
theorem map_tIdeal (S : Type*) [CommRing S] [Algebra (Algebra.adjoin ℂ {t}) S] :
    (tIdeal t).map (algebraMap (Algebra.adjoin ℂ {t}) S) =
      Ideal.span {algebraMap (Algebra.adjoin ℂ {t}) S (tGen t)} := by
  rw [tIdeal, Ideal.map_span, Set.image_singleton]

variable {t} (ht : Transcendental ℂ t)
include ht

/-- The polynomial presentation of `ℂ[t]` sends `X` to `t`. -/
theorem polyEquiv_X : Polynomial.algEquivOfTranscendental ℂ t ht X = tGen t := by
  ext; simp [tGen]

/-- `ℂ[t]` is a PID for transcendental `t`. -/
theorem isPrincipalIdealRing_adjoin : IsPrincipalIdealRing (Algebra.adjoin ℂ {t}) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental ℂ t ht).toRingHom
    (Polynomial.algEquivOfTranscendental ℂ t ht).surjective

/-- The ideal `(t)` is the image of `(X - 0)`. -/
theorem tIdeal_eq_map : tIdeal t =
    (Ideal.span {X - C (0 : ℂ)}).map (Polynomial.algEquivOfTranscendental ℂ t ht) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, C_0, map_zero, sub_zero, polyEquiv_X]
  rfl

/-- The ideal `(t)` is nonzero. -/
theorem tIdeal_ne_bot : tIdeal t ≠ ⊥ := by
  rw [tIdeal, Ne, Ideal.span_singleton_eq_bot]
  intro h
  have : t = 0 := congrArg Subtype.val h
  exact ht (this ▸ isAlgebraic_zero)

/-- `ℂ[t]/(t) ≅ ℂ`. -/
def quotientTIdealEquiv : ℂ ≃+* Algebra.adjoin ℂ {t} ⧸ tIdeal t :=
  ((Polynomial.quotientSpanXSubCAlgEquiv (0 : ℂ)).symm.trans
    (Ideal.quotientEquivAlg _ _ (Polynomial.algEquivOfTranscendental ℂ t ht)
      (tIdeal_eq_map ht))).toRingEquiv

/-- The ideal `(t)` is maximal. -/
theorem tIdeal_isMaximal : (tIdeal t).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField (Field.toIsField ℂ) (quotientTIdealEquiv ht).symm.toMulEquiv)

/-- The residue field `ℂ[t]/(t)` is algebraically closed. -/
theorem isAlgClosed_quotient [(tIdeal t).IsMaximal] :
    @IsAlgClosed (Algebra.adjoin ℂ {t} ⧸ tIdeal t) (Ideal.Quotient.field _) := by
  let := Ideal.Quotient.field (tIdeal t)
  exact IsAlgClosed.of_ringEquiv ℂ _ (quotientTIdealEquiv ht)

omit ht in
/-- An algebra whose structure map is bijective has rank one. -/
theorem finrank_eq_one_of_bijective {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) : Module.finrank R S = 1 := by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq,
    Module.finrank_self]

omit ht in
/-- The integral closure of `ℂ[t]` in `K`. -/
abbrev intClosure (t : K) := integralClosure (Algebra.adjoin ℂ {t}) K

omit ht in
/-- The element `t` of the integral closure of `ℂ[t]`. -/
def tA (t : K) : intClosure t := algebraMap _ _ (tGen t)

omit ht in
/-- The element `t` of the integral closure maps to `t`. -/
theorem algebraMap_tA (t : K) : algebraMap (intClosure t) K (tA t) = t := rfl

omit ht in
/-- The function field is the fraction field of the integral closure of `ℂ[t]`. -/
instance isFractionRing_intClosure [FiniteDimensional ℂ⟮t⟯ K] :
    IsFractionRing (intClosure t) K :=
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin ℂ {t}) ℂ⟮t⟯ K

/-- The integral closure of `ℂ[t]` is a Dedekind domain.
Source: Mathlib `IsIntegralClosure.isDedekindDomain`. -/
theorem isDedekindDomain_intClosure [FiniteDimensional ℂ⟮t⟯ K] :
    IsDedekindDomain (intClosure t) := by
  have := isPrincipalIdealRing_adjoin ht
  exact integralClosure.isDedekindDomain (Algebra.adjoin ℂ {t}) ℂ⟮t⟯ K

omit ht in
/-- The localization of the integral closure of `ℂ[t]` at a prime, inside `K`. -/
def locSub (t : K) [IsFractionRing (intClosure t) K] (q : Ideal (intClosure t)) [q.IsPrime] :
    Subalgebra (intClosure t) K :=
  Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors

section locSub

variable [IsFractionRing (intClosure t) K] (q : Ideal (intClosure t)) [q.IsPrime]

omit ht in
/-- The localization is an algebra over the integral closure (stated directly, because the
generic search through `Subalgebra.toAlgebra` times out here). -/
instance : Algebra (intClosure t) (locSub t q) := Subalgebra.algebra _

omit ht in
instance : IsLocalization q.primeCompl (locSub t q) :=
  Localization.subalgebra.isLocalization_ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors

omit ht in
/-- Elements of the localization are fractions with denominator outside the prime. -/
theorem mem_locSub {x : K} : x ∈ locSub t q ↔ ∃ (a s : intClosure t) (_ : s ∈ q.primeCompl),
    x = algebraMap _ K a * (algebraMap _ K s)⁻¹ := Iff.rfl

omit ht in
/-- The order of `t` is the same in both models of the localization. -/
theorem ord_localization_eq :
    Ring.ord (Localization.AtPrime q) (algebraMap _ _ (tA t)) =
      Ring.ord (locSub t q) (algebraMap _ _ (tA t)) := by
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (locSub t q)
  have := ord_ringEquiv (S := locSub t q) e.toRingEquiv
    (algebraMap _ (Localization.AtPrime q) (tA t))
  convert this using 2
  exact (e.commutes _).symm

end locSub

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
/-- The orders of `t` at the primes of the integral closure above `(t)` add up to
`[K : ℂ⟮t⟯]`.
Source: Mathlib `Ideal.sum_ramification_inertia_eq_finrank`; Serre, *Local Fields*, I.4. -/
theorem finsum_ord_primesOver [FiniteDimensional ℂ⟮t⟯ K] :
    ∑ᶠ q : (tIdeal t).primesOver (integralClosure (Algebra.adjoin ℂ {t}) K),
      (Ring.ord (Localization.AtPrime q.1)
        (algebraMap (intClosure t) (Localization.AtPrime q.1) (tA t))).toNat =
      Module.finrank ℂ⟮t⟯ K := by
  let R₀ := Algebra.adjoin ℂ {t}
  let A := integralClosure R₀ K
  have := isPrincipalIdealRing_adjoin ht
  have hmax := tIdeal_isMaximal ht
  have : IsDedekindDomain A := IsIntegralClosure.isDedekindDomain R₀ ℂ⟮t⟯ K A
  have : Module.Finite R₀ A := IsIntegralClosure.finite R₀ ℂ⟮t⟯ K A
  have : Module.Free R₀ A := IsIntegralClosure.module_free R₀ ℂ⟮t⟯ K A
  let : Fintype ((tIdeal t).primesOver A) :=
    (Algebra.QuasiFinite.finite_primesOver (tIdeal t)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (tIdeal t) A
  rw [IsIntegralClosure.rank R₀ ℂ⟮t⟯ K A] at hsum
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hf : q.1.inertiaDeg R₀ = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (tIdeal t) q.1]
    convert finrank_eq_one_of_bijective (R := R₀ ⧸ tIdeal t) (S := A ⧸ q.1) ?_
    have : Module.Finite (R₀ ⧸ tIdeal t) (A ⧸ q.1) :=
      Module.Finite.of_restrictScalars_finite R₀ _ _
    have : Algebra.IsIntegral (R₀ ⧸ tIdeal t) (A ⧸ q.1) := Algebra.IsIntegral.of_finite _ _
    let := Ideal.Quotient.field (tIdeal t)
    have := isAlgClosed_quotient ht
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hm := map_tIdeal t (Localization.AtPrime q.1)
  rw [IsScalarTower.algebraMap_apply R₀ A (Localization.AtPrime q.1)] at hm
  change _ = Ideal.span {algebraMap A (Localization.AtPrime q.1) (tA t)} at hm
  rw [hf, mul_one, Ideal.ramificationIdx_eq (tIdeal t) q.1, Ring.ord, ← hm]


section Valuations

variable [FiniteDimensional ℂ⟮t⟯ K]

/-- The localization at a prime above `(t)` is a DVR. -/
theorem isDVR_locSub (q : (tIdeal t).primesOver (intClosure t)) :
    IsDiscreteValuationRing (locSub t q.1) :=
  have := isDedekindDomain_intClosure ht
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _
    (Ideal.ne_bot_of_liesOver_of_ne_bot (tIdeal_ne_bot ht) q.1) _

/-- The valuation subring of `K` at a prime of the integral closure above `(t)`. -/
def valAt (q : (tIdeal t).primesOver (intClosure t)) : ValuationSubring K :=
  have := isDVR_locSub ht q
  valuationSubringOfFractionRing (locSub t q.1) K

/-- Membership in the valuation subring at a prime above `(t)`. -/
theorem mem_valAt (q : (tIdeal t).primesOver (intClosure t)) {x : K} :
    x ∈ valAt ht q ↔ ∃ r : locSub t q.1, algebraMap _ K r = x := Iff.rfl

/-- Constants lie in the valuation subring at every prime above `(t)`. -/
theorem algebraMap_mem_valAt (q : (tIdeal t).primesOver (intClosure t)) (c : ℂ) :
    algebraMap ℂ K c ∈ valAt ht q :=
  (mem_valAt ht q).mpr ⟨algebraMap (intClosure t) _ (algebraMap _ (intClosure t)
      (algebraMap ℂ (Algebra.adjoin ℂ {t}) c)), rfl⟩

/-- `t` lies in the valuation subring at every prime above `(t)`. -/
theorem t_mem_valAt (q : (tIdeal t).primesOver (intClosure t)) : t ∈ valAt ht q :=
  (mem_valAt ht q).mpr ⟨algebraMap (intClosure t) _ (tA t), rfl⟩

omit ht [FiniteDimensional ℂ⟮t⟯ K] in
/-- `t` lies in every prime above `(t)`. -/
theorem tA_mem (q : (tIdeal t).primesOver (intClosure t)) : tA t ∈ q.1 := by
  have h1 : tGen t ∈ (q.1).under (Algebra.adjoin ℂ {t}) := by
    rw [← Ideal.LiesOver.over (P := q.1) (p := tIdeal t)]
    exact Ideal.subset_span rfl
  exact h1

/-- `t⁻¹` does not lie in the valuation subring at a prime above `(t)`. -/
theorem inv_t_not_mem_valAt (q : (tIdeal t).primesOver (intClosure t)) : t⁻¹ ∉ valAt ht q := by
  intro h
  obtain ⟨r, hr⟩ := (mem_valAt ht q).mp h
  have ht0 : t ≠ 0 := fun h0 ↦ ht (h0 ▸ isAlgebraic_zero)
  have hu : IsUnit (algebraMap (intClosure t) (locSub t q.1) (tA t)) := by
    refine IsUnit.of_mul_eq_one r (Subtype.ext ?_)
    change t * algebraMap _ K r = 1
    rw [hr, mul_inv_cancel₀ ht0]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (locSub t q.1) q.1 _).mp hu (tA_mem q)

/-- The valuation subring at a prime above `(t)` is proper. -/
theorem valAt_ne_top (q : (tIdeal t).primesOver (intClosure t)) : valAt ht q ≠ ⊤ := fun h ↦
  inv_t_not_mem_valAt ht q (h ▸ trivial)

/-- The prime is recovered from its valuation subring. -/
theorem mem_iff_inv_not_mem_valAt (q : (tIdeal t).primesOver (intClosure t))
    {a : intClosure t} (ha : a ≠ 0) :
    a ∈ q.1 ↔ (algebraMap _ K a)⁻¹ ∉ valAt ht q := by
  have ha' : algebraMap (intClosure t) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr ha
  constructor
  · intro haq h
    obtain ⟨r, hr⟩ := (mem_valAt ht q).mp h
    have hu : IsUnit (algebraMap (intClosure t) (locSub t q.1) a) := by
      refine IsUnit.of_mul_eq_one r (Subtype.ext ?_)
      change algebraMap _ K a * algebraMap _ K r = 1
      rw [hr, mul_inv_cancel₀ ha']
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locSub t q.1) q.1 _).mp hu haq
  · intro h
    by_contra haq
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (locSub t q.1) q.1 a).mpr haq
    apply h
    refine (mem_valAt ht q).mpr ⟨↑(hu.unit⁻¹), ?_⟩
    have h1 : algebraMap _ K (algebraMap (intClosure t) (locSub t q.1) a) *
        algebraMap _ K (↑hu.unit⁻¹ : locSub t q.1) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    exact eq_inv_of_mul_eq_one_right h1

/-- Distinct primes above `(t)` give distinct valuation subrings. -/
theorem valAt_injective {q q' : (tIdeal t).primesOver (intClosure t)}
    (h : valAt ht q = valAt ht q') : q = q' := by
  apply Subtype.ext
  ext a
  by_cases ha : a = 0
  · simp [ha]
  rw [mem_iff_inv_not_mem_valAt ht q ha, mem_iff_inv_not_mem_valAt ht q' ha, h]

/-- A valuation subring containing `ℂ` in which `t` is a nonunit contains the localization
at some prime above `(t)`.
Source: Atiyah–Macdonald, Proposition 5.18 and Corollary 5.22. -/
theorem exists_locSub_le (W : ValuationSubring K) (hC : ∀ c, algebraMap ℂ K c ∈ W)
    (htW : t ∈ W) (hinv : t⁻¹ ∉ W) :
    ∃ q : (tIdeal t).primesOver (intClosure t), ∀ r : locSub t q.1, algebraMap _ K r ∈ W := by
  have hR₀ : ∀ x : Algebra.adjoin ℂ {t}, (x : K) ∈ W := by
    rintro ⟨x, hx⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx => change x ∈ W; rw [Set.mem_singleton_iff.mp hx]; exact htW
    | algebraMap c => exact hC c
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let j : Algebra.adjoin ℂ {t} →+* W := (algebraMap (Algebra.adjoin ℂ {t}) K).codRestrict W hR₀
  let := j.toAlgebra
  have : IsScalarTower (Algebra.adjoin ℂ {t}) W K := .of_algebraMap_eq fun _ ↦ rfl
  have hA : ∀ a : intClosure t, algebraMap _ K a ∈ W := by
    intro a
    obtain ⟨w, hw⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp
      (a.2.tower_top (A := W))
    change (a : K) ∈ W
    rw [← hw]
    exact w.2
  let ι : intClosure t →+* W := (algebraMap (intClosure t) K).codRestrict W hA
  let q := (IsLocalRing.maximalIdeal W).comap ι
  have htq : tA t ∈ q := by
    change ι (tA t) ∈ IsLocalRing.maximalIdeal W
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hinv
    have h1 : (ι (tA t) : K) * ((hu.unit⁻¹ : Wˣ) : W) = 1 := by
      rw [← W.coe_mul, IsUnit.mul_val_inv, W.coe_one]
    change (↑(ι (tA t)) : K)⁻¹ ∈ W
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact (hu.unit⁻¹ : Wˣ).1.2
  have hmax := tIdeal_isMaximal ht
  have hlies : q.LiesOver (tIdeal t) := by
    constructor
    refine hmax.eq_of_le ?_ ?_
    · intro h1
      have : (1 : intClosure t) ∈ q := by
        have := (Ideal.eq_top_iff_one _).mp h1
        simpa using this
      exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).mpr this)
    · rw [tIdeal, Ideal.span_le, Set.singleton_subset_iff]
      exact htq
  refine ⟨⟨q, inferInstance, hlies⟩, ?_⟩
  intro r
  obtain ⟨a, s, hs, hr⟩ := (mem_locSub q).mp r.2
  rw [show algebraMap (locSub t q) K r = r.1 from rfl, hr]
  refine mul_mem (hA a) ?_
  have hsu : IsUnit (ι s) := by
    by_contra hn
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hn)
  have h1 : (ι s : K) * ((hsu.unit⁻¹ : Wˣ) : W) = 1 := by
    rw [← W.coe_mul, IsUnit.mul_val_inv, W.coe_one]
  change (ι s : K)⁻¹ ∈ W
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact (hsu.unit⁻¹ : Wˣ).1.2

end Valuations

end HodgeLean.Foundations.Curves
