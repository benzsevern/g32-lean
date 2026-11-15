import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped Pointwise
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_prime_fibre_orbit
    {A B G : Type*} [CommRing A] [CommRing B] [Group G] [Finite G]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (P Q : PrimeSpectrum B)
    (h : PrimeSpectrum.comap (algebraMap A B) P =
      PrimeSpectrum.comap (algebraMap A B) Q) :
    ∃ g : G, Q = g • P := by
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G P.asIdeal Q.asIdeal
    (congrArg PrimeSpectrum.asIdeal h)
  exact ⟨g, PrimeSpectrum.ext hg⟩

lemma s2v_i1ahi_invariant_open_saturation
    {A B G : Type*} [CommRing A] [CommRing B] [Group G] [Finite G]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (N : Set (PrimeSpectrum B))
    (hN : ∀ (g : G) (P : PrimeSpectrum B), P ∈ N → g • P ∈ N) :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹'
      (PrimeSpectrum.comap (algebraMap A B) '' N) = N := by
  apply Set.Subset.antisymm
  · rintro Q ⟨P, hP, he⟩
    obtain ⟨g, rfl⟩ := s2v_i1ahi_prime_fibre_orbit (G := G) P Q he
    exact hN g P hP
  · intro P hP
    exact ⟨P, hP, rfl⟩

lemma s2v_i1ahi_invariant_open_image
    {A B G : Type*} [CommRing A] [CommRing B] [Group G] [Finite G]
    [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (N : Set (PrimeSpectrum B)) (hN : IsOpen N)
    (hstable : ∀ (g : G) (P : PrimeSpectrum B), P ∈ N → g • P ∈ N) :
    IsOpen (PrimeSpectrum.comap (algebraMap A B) '' N) := by
  letI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hq := (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap A B)
    (show (algebraMap A B).IsIntegral from Algebra.IsIntegral.isIntegral)).isQuotientMap
      (PrimeSpectrum.continuous_comap _) (Algebra.IsIntegral.comap_surjective A B)
  rw [← hq.isOpen_preimage, s2v_i1ahi_invariant_open_saturation (G := G) N hstable]
  exact hN

end HodgeLean.Foundations.Program
