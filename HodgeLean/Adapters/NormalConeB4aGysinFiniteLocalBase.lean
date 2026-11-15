import HodgeLean.Adapters.NormalConeB4aGysinFiniteLocal
import Mathlib.RingTheory.Localization.Finiteness

noncomputable section
namespace HodgeLean.Adapters

/-- A finite model with local fibre remains local after localization on
the base at that fibre. -/
theorem a3b4a_gysin_finite_base_localization_isLocalRing
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (p.Fiber S)] :
    IsLocalRing (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI : IsLocalRing (Sp ⧸ (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Sp)) :=
    (Ideal.Fiber.algEquivQuotient (S := S) p).toRingEquiv.isLocalRing
  exact a3b4a_gysin_finite_local_of_local_parameter_quotient (R := Rp)

/-- A local fibre of a finite algebra has a unique source prime above its base prime. -/
theorem a3b4a_gysin_unique_prime_over_local_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] [IsLocalRing (p.Fiber S)]
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] : q = q' := by
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  have heq : e (Ideal.primesOver.mk p q) = e (Ideal.primesOver.mk p q') := by
    apply PrimeSpectrum.ext
    exact (IsLocalRing.eq_maximalIdeal
      (IsArtinianRing.isMaximal_of_isPrime (e (Ideal.primesOver.mk p q)).asIdeal)).trans
      (IsLocalRing.eq_maximalIdeal
        (IsArtinianRing.isMaximal_of_isPrime (e (Ideal.primesOver.mk p q')).asIdeal)).symm
  exact congrArg Subtype.val (e.injective heq)

end HodgeLean.Adapters
