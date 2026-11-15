import HodgeLean.Adapters.NormalConeB4aGysinFiniteLocalBase

noncomputable section
namespace HodgeLean.Adapters

/-- With a local fibre in a finite algebra, localization at the source
prime only inverts elements already inverted by localization on the base. -/
theorem a3b4a_gysin_finite_source_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (p.Fiber S)]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q) := by
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  let Rp := Localization.AtPrime p
  let C := Localization M
  letI : IsLocalRing C := a3b4a_gysin_finite_base_localization_isLocalRing p
  let m := IsLocalRing.maximalIdeal C
  have hmRp : m.under Rp = IsLocalRing.maximalIdeal Rp :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rp) m)
  have hmR : m.under R = p := by
    rw [← Ideal.under_under (A := R) (B := Rp), hmRp]
    exact Localization.AtPrime.under_maximalIdeal
  let q' := m.under S
  letI : q'.LiesOver p := ⟨by
    change p = (m.under S).under R
    rw [Ideal.under_under, hmR]⟩
  have hq : q' = q := a3b4a_gysin_unique_prime_over_local_fibre p q' q
  have hle : M ≤ q.primeCompl := by
    rintro s ⟨r, hr, rfl⟩
    exact fun hs => hr ((q.mem_of_liesOver p r).mpr hs)
  have hu : ∀ s ∈ q.primeCompl, IsUnit (algebraMap S C s) := by
    intro s hs
    by_contra hn
    apply hs
    rw [← hq]
    change algebraMap S C s ∈ m
    exact (IsLocalRing.mem_maximalIdeal _).mpr hn
  letI : IsLocalization q.primeCompl C := IsLocalization.of_le M q.primeCompl hle hu
  exact IsLocalization.isLocalization_of_algEquiv M
    (IsLocalization.algEquiv q.primeCompl C (Localization.AtPrime q))

end HodgeLean.Adapters
