import HodgeLean.Adapters.NormalConeB4aGysinNilpotentFibre
import Mathlib.RingTheory.Localization.Algebra

/-! # Localizing split nilpotent thickenings along their reduced base -/

noncomputable section
namespace HodgeLean.Adapters

/-- A source element divides a power of its image under a nilpotent retraction,
viewed back in the source through the section. -/
theorem a3b4a_gysin_nilpotent_retraction_dvd_power
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε)) (a : A) :
    ∃ n : ℕ, a ∣ algebraMap B A ((ε a) ^ n) := by
  obtain ⟨n, hn⟩ := hnil
  have hk : algebraMap B A (ε a) - a ∈ RingHom.ker ε := by
    simp [RingHom.mem_ker]
  have hz : (algebraMap B A (ε a) - a) ^ n = 0 := by
    simpa [hn] using Ideal.pow_mem_pow hk n
  let I : Ideal A := Ideal.span {a}
  have ha : Ideal.Quotient.mk I a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he := congrArg (Ideal.Quotient.mk I) hz
  simp only [map_pow, map_sub, ha, sub_zero, map_zero] at he
  refine ⟨n, Ideal.mem_span_singleton.mp ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_pow] using he

/-- Localization at a source prime of a split nilpotent thickening inverts
exactly what is needed from its reduced base. -/
theorem a3b4a_gysin_nilpotent_localization_over_base
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε))
    (p : Ideal B) [p.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl)
      (Localization.AtPrime (p.comap ε.toRingHom)) := by
  let M := Algebra.algebraMapSubmonoid A p.primeCompl
  let q := p.comap ε.toRingHom
  have hle : M ≤ q.primeCompl := by
    rintro a ⟨b, hb, rfl⟩
    change ε (algebraMap B A b) ∉ p
    simpa using hb
  have hdiv : ∀ a ∈ q.primeCompl, ∃ b ∈ M, a ∣ b := by
    intro a ha
    obtain ⟨n, hn⟩ := a3b4a_gysin_nilpotent_retraction_dvd_power ε hnil a
    refine ⟨algebraMap B A ((ε a) ^ n), ?_, hn⟩
    exact ⟨(ε a) ^ n, p.primeCompl.pow_mem ha n, rfl⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd
    (S := Localization.AtPrime q) M q.primeCompl hle hdiv).mpr inferInstance

/-- Finite flat split nilpotent thickenings remain finite flat on corresponding
source and base local rings. -/
theorem a3b4a_gysin_nilpotent_localization_finite_flat
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Finite B A] [Module.Flat B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε))
    (p : Ideal B) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) ∧
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
  have hq := a3b4a_gysin_nilpotent_retraction_prime ε hnil p q
  subst q
  letI := Localization.AtPrime.algebraOfLiesOver p (p.comap ε.toRingHom)
  have := a3b4a_gysin_nilpotent_localization_over_base ε hnil p
  refine ⟨Module.Finite.of_isLocalization B A p.primeCompl, ?_⟩
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime (p.comap ε.toRingHom))).mpr
    inferInstance

/-- The retraction and its nilpotent kernel pass to corresponding source
and base local rings, compatibly with the original ring maps. -/
theorem a3b4a_gysin_exists_localized_nilpotent_retraction
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε))
    (p : Ideal B) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∃ εp : Localization.AtPrime q →ₐ[Localization.AtPrime p] Localization.AtPrime p,
      IsNilpotent (RingHom.ker εp) ∧
      ∀ a : A, εp (algebraMap A (Localization.AtPrime q) a) =
        algebraMap B (Localization.AtPrime p) (ε a) := by
  have hq := a3b4a_gysin_nilpotent_retraction_prime ε hnil p q
  subst q
  let q := p.comap ε.toRingHom
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have := a3b4a_gysin_nilpotent_localization_over_base ε hnil p
  letI : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization.AtPrime p) := by
    simpa only [Algebra.algebraMapSubmonoid_self] using
      (inferInstance : IsLocalization p.primeCompl (Localization.AtPrime p))
  let εp := IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime p) ε
  refine ⟨εp, ?_, ?_⟩
  swap
  · intro a
    exact IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap p.primeCompl ε) a
  have hmap : (Algebra.algebraMapSubmonoid A p.primeCompl).map ε.toRingHom =
      Algebra.algebraMapSubmonoid B p.primeCompl :=
    Algebra.algebraMapSubmonoid_map_eq p.primeCompl ε
  have hker : RingHom.ker εp =
      (RingHom.ker ε).map (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.ker_map (Localization.AtPrime p) ε.toRingHom hmap
  rw [hker]
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
  rfl

end HodgeLean.Adapters
