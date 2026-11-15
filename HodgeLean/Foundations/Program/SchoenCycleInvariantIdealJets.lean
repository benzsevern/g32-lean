import HodgeLean.Foundations.Program.SchoenCycleStabilizerJets

/-! # Invariant finite jets retaining a specified ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Averaging a finite jet in a stable ideal retains membership in that ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_ideal_jet_representative
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (I J : Ideal A) (x : A)
    (hJ : ∀ g, ∀ r ∈ J, a g r ∈ J) (hxJ : x ∈ J)
    (hx : ∀ g, a g x - x ∈ I) :
    ∃ y ∈ J, (∀ g, a g y = y) ∧ y - x ∈ I := by
  obtain ⟨y, hy, he⟩ := s2e_invariant_jet_representative G A a (I ⊓ J) x
    (fun g => ⟨hx g, J.sub_mem (hJ g x hxJ) hxJ⟩)
  exact ⟨y, sub_add_cancel y x ▸ J.add_mem he.2 hxJ, hy, he.1⟩

/-- An orbit-supported jet in a stable ideal has an invariant representative in that same ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_orbit_supported_ideal_jet_average
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I J : Ideal A) (x z : A)
    (hJ : ∀ g, ∀ r ∈ J, a g r ∈ J) (hxJ : x ∈ J) (hzJ : z ∈ J)
    (hin : ∀ g ∈ H, a g z - x ∈ I)
    (hout : ∀ g ∉ H, a g z ∈ I) :
    ∃ y ∈ J, (∀ g, a g y = y) ∧ y - x ∈ I := by
  obtain ⟨y, hy, he⟩ := s2e_orbit_supported_jet_average G A a H (I ⊓ J) x z
    (fun g hg => ⟨hin g hg, J.sub_mem (hJ g z hzJ) hxJ⟩)
    (fun g hg => ⟨hout g hg, hJ g z hzJ⟩)
  exact ⟨y, sub_add_cancel y x ▸ J.add_mem he.2 hxJ, hy, he.1⟩

/-- Stabilizer-invariant jets extend within a prescribed stable ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_stabilizer_ideal_jet_extension
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I J : Ideal A) (x : A)
    (hJ : ∀ g, ∀ r ∈ J, a g r ∈ J) (hxJ : x ∈ J)
    (hstable : ∀ g ∈ H, ∀ r ∈ I, a g r ∈ I)
    (hx : ∀ g ∈ H, a g x - x ∈ I)
    (hcoprime : ∀ g ∉ H, I ⊔ I.comap (a g).toRingHom = ⊤) :
    ∃ y ∈ J, (∀ g, a g y = y) ∧ y - x ∈ I := by
  obtain ⟨e, he, he0⟩ := s2e_orbit_ideal_separator G A a H I hcoprime
  apply s2e_orbit_supported_ideal_jet_average G A a H I J x (e * x) hJ hxJ
    (J.mul_mem_left e hxJ)
  · intro g hg
    have he1 : a g e - 1 ∈ I := by
      simpa only [map_sub, map_one] using hstable g hg (e - 1) he
    have hmul : a g (e * x) - x =
        a g e * (a g x - x) + (a g e - 1) * x := by
      rw [map_mul]
      ring
    rw [hmul]
    exact I.add_mem (I.mul_mem_left _ (hx g hg)) (I.mul_mem_right _ he1)
  · intro g hg
    rw [map_mul]
    exact I.mul_mem_right _ (he0 g hg)

/-- A jet in a stable ideal at a maximal ideal extends to an invariant element of that same stable ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants; Atiyah–Macdonald, Proposition 1.10. -/
theorem s2e_maximal_stabilizer_ideal_jet_extension
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I : Ideal A) [I.IsMaximal]
    (hstab : ∀ g, I.comap (a g).toRingHom = I ↔ g ∈ H)
    (J : Ideal A) (hJ : ∀ g, ∀ r ∈ J, a g r ∈ J)
    (N : ℕ) (x : A) (hxJ : x ∈ J) (hx : ∀ g ∈ H, a g x - x ∈ I ^ N) :
    ∃ y ∈ J, (∀ g, a g y = y) ∧ y - x ∈ I ^ N := by
  have hpow (g : G) : (I ^ N).comap (a g).toRingHom =
      (I.comap (a g).toRingHom) ^ N := by
    apply (Ideal.relIsoOfBijective (a g).toRingHom (a g).bijective).symm.injective
    change ((I ^ N).comap (a g).toRingHom).map (a g).toRingHom =
      ((I.comap (a g).toRingHom) ^ N).map (a g).toRingHom
    rw [Ideal.map_comap_of_surjective (f := (a g).toRingHom) (a g).surjective,
      Ideal.map_pow,
      Ideal.map_comap_of_surjective (f := (a g).toRingHom) (a g).surjective]
  apply s2e_stabilizer_ideal_jet_extension G A a H (I ^ N) J x hJ hxJ ?_ hx ?_
  · intro g hg r hr
    change r ∈ (I ^ N).comap (a g).toRingHom
    rwa [hpow, (hstab g).mpr hg]
  · intro g hg
    rw [hpow]
    apply Ideal.pow_sup_pow_eq_top
    have hm : (I.comap (a g).toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (a g).toRingHom (a g).surjective
    apply Ideal.IsMaximal.coprime_of_ne (inferInstance) hm
    intro he
    exact hg ((hstab g).mp he.symm)

end HodgeLean.Foundations.Program
