import HodgeLean.Foundations.Program.SchoenCycleLocalizedAdicMapEquivalence
import HodgeLean.Foundations.Program.SchoenCycleLocalFormalUnramified
import HodgeLean.Foundations.Program.SchoenCycleAdicLocalizationFlatness
import HodgeLean.Foundations.Program.SchoenCycleFlatUnramifiedAtEtale

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A retained canonical adic bijection gives etaleness at the augmented target prime without prescribed source cotangent coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1 and 17.11.1; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_isEtaleAt_of_localized_adic_bijective
    (k A S : Type*) [Field k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra k S] [Algebra A S] [IsScalarTower k A S]
    [IsNoetherianRing A] [IsNoetherianRing S] [Algebra.FinitePresentation A S]
    (I : Ideal A) [I.IsMaximal] (Q : Ideal S) [Q.IsMaximal] [Q.LiesOver I]
    (h : ∀ n a, a ∈ I ^ n → algebraMap A S a ∈ Q ^ n)
    (hbij : Function.Bijective (s2e_adic_algebra_map I Q (Algebra.ofId A S) h))
    (ε : Localization.AtPrime Q →ₐ[k] k) : Algebra.IsEtaleAt A Q := by
  let R := Localization.AtPrime I
  let T := Localization.AtPrime Q
  letI := Localization.AtPrime.algebraOfLiesOver I Q
  letI : Algebra.EssFiniteType S T := Algebra.EssFiniteType.of_isLocalization T Q.primeCompl
  letI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.comp A S T
  letI : Module.Finite T Ω[T⁄R] := Module.Finite.of_surjective
    (KaehlerDifferential.map A R T T) (KaehlerDifferential.map_surjective A R T)
  obtain ⟨E, hE⟩ := s2e_localized_adic_equivalence_with_values A S I Q h hbij
  letI : IsLocalHom (algebraMap R T) := by
    change IsLocalHom (Localization.localRingHom I Q (algebraMap A S) Ideal.LiesOver.over)
    infer_instance
  letI : Algebra.FormallyUnramified R T :=
    s2e_formallyUnramified_of_local_formal_equivalence k R T ε (E.restrictScalars k) hE
  letI : Algebra.FormallyUnramified A R := Algebra.FormallyUnramified.of_isLocalization I.primeCompl
  letI : Algebra.FormallyUnramified A T := Algebra.FormallyUnramified.comp A R T
  letI : Module.Flat A T := s2e_flat_prime_localization_of_adic_bijective A S I Q h hbij
  exact s2e_isEtaleAt_of_flat_unramified_localization A S Q

#print axioms s2e_isEtaleAt_of_localized_adic_bijective
end HodgeLean.Foundations.Program
