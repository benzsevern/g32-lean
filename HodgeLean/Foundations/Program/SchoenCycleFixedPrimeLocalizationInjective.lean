import HodgeLean.Foundations.Program.SchoenCycleFixedPrimeLocalizationMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual fixed-prime localization map is injective whenever the original localization map is injective.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_prime_localization_map_injective
    (k C B G : Type*) [CommRing k] [CommRing C] [CommRing B] [Algebra k C] [Algebra C B]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C]
    (P : Ideal C) [P.IsPrime] [IsLocalization.AtPrime B P]
    (hinj : Function.Injective (algebraMap C B)) :
    Function.Injective (s2e_fixed_prime_localization_map k C B G P) := by
  let S := FixedPoints.subalgebra k C G
  let Q := P.comap S.val.toRingHom
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Q.primeCompl)
  intro a ha
  rw [s2e_fixed_prime_localization_map_of] at ha
  have hz : a.val = 0 := hinj (ha.trans (map_zero (algebraMap C B)).symm)
  have ha0 : a = 0 := Subtype.ext hz
  rw [ha0, map_zero]

#print axioms s2e_fixed_prime_localization_map_injective
end HodgeLean.Foundations.Program
