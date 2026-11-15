import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Operations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_finite_spectrum_principal
    {R : Type*} [CommRing R] (N : TopologicalSpace.Opens (PrimeSpectrum R))
    (s : Finset (PrimeSpectrum R)) (hs : ∀ p ∈ s, p ∈ N) :
    ∃ r : R, (∀ p ∈ s, p ∈ PrimeSpectrum.basicOpen r) ∧
      PrimeSpectrum.basicOpen r ≤ N := by
  classical
  let I := PrimeSpectrum.vanishingIdeal (N : Set (PrimeSpectrum R))ᶜ
  have hn (p : PrimeSpectrum R) (hp : p ∈ s) : ¬ I ≤ p.asIdeal := by
    intro h
    have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := h
    change p ∈ PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal (N : Set (PrimeSpectrum R))ᶜ : Set R) at hz
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, N.isOpen.isClosed_compl.closure_eq] at hz
    exact hz (hs p hp)
  have hnot : ¬ (I : Set R) ⊆ ⋃ J ∈ (s.image PrimeSpectrum.asIdeal : Finset (Ideal R)), (J : Set R) := by
    intro h
    obtain ⟨J, hJ, hIJ⟩ := (Ideal.subset_union_prime (⊤ : Ideal R) ⊤
      (fun J hJ _ _ => by
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hJ
        exact p.isPrime)).mp h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hn p hp hIJ
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  refine ⟨r, ?_, ?_⟩
  · intro p hp
    intro hmem
    exact hr (Set.mem_iUnion.mpr ⟨p.asIdeal,
      Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hmem⟩⟩)
  · intro p hp
    by_contra hpn
    exact hp ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hrI p hpn)

lemma s2v_i1ahi_finite_affine_shrink
    (X : Scheme) [IsAffine X] (N : X.Opens)
    (s : Finset X) (hs : ∀ x ∈ s, x ∈ N) :
    ∃ V : X.Opens, IsAffineOpen V ∧ V ≤ N ∧ ∀ x ∈ s, x ∈ V := by
  classical
  let f := X.toSpecΓ
  let W := f ''ᵁ N
  let t := s.image f
  have ht : ∀ p ∈ t, p ∈ W := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨x, hs x hx, rfl⟩
  obtain ⟨r, hr, hrW⟩ := s2v_i1ahi_finite_spectrum_principal W t ht
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen r,
    (IsAffineOpen.Spec_basicOpen r).preimage_of_isIso f, ?_, ?_⟩
  · have he : f ⁻¹ᵁ W = N := f.preimage_image_eq N
    exact (show f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ f ⁻¹ᵁ W from
      fun _ hx => hrW hx).trans he.le
  · intro x hx
    exact hr (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

end HodgeLean.Foundations.Program
