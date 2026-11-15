import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-! # Representing localized finite jets by affine sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every finite jet at a maximal ideal is represented before localization.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
localization and quotients; Chapter 10, finite infinitesimal neighbourhoods. -/
theorem s2e_localization_power_jet_representative
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m]
    (N : ℕ) (z : S) :
    ∃ r : R, z - algebraMap R S r ∈ (m ^ N).map (algebraMap R S) := by
  classical
  obtain ⟨r, ⟨b, hb⟩, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl z
  have hb' : b ∉ m := hb
  have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem (n := N) m hb'
  obtain ⟨cbar, hcbar⟩ := hu.exists_right_inv
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective cbar
  have hbc : b * c - 1 ∈ m ^ N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, map_mul, hc, hcbar, sub_self]
  have hm : algebraMap R S (b * c) - 1 ∈ (m ^ N).map (algebraMap R S) := by
    simpa only [map_sub, map_one] using Ideal.mem_map_of_mem (algebraMap R S) hbc
  refine ⟨r * c, ?_⟩
  have he : IsLocalization.mk' S r ⟨b, hb⟩ - algebraMap R S (r * c) =
      -IsLocalization.mk' S r ⟨b, hb⟩ * (algebraMap R S (b * c) - 1) := by
    rw [map_mul, map_mul, ← IsLocalization.mk'_spec S r ⟨b, hb⟩]
    ring
  rw [he]
  exact ((m ^ N).map (algebraMap R S)).mul_mem_left _ hm

/-- Localization at a maximal ideal reflects membership in every power of that ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
localization and quotients; Chapter 10, finite infinitesimal neighbourhoods. -/
theorem s2e_localization_power_jet_mem_iff
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m]
    (N : ℕ) (r : R) :
    algebraMap R S r ∈ (m ^ N).map (algebraMap R S) ↔ r ∈ m ^ N := by
  constructor
  · intro h
    obtain ⟨b, hb, hbr⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff m.primeCompl S (m ^ N) r).mp h
    have hb' : b ∉ m := hb
    have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem (n := N) m hb'
    have hz : Ideal.Quotient.mk (m ^ N) b * Ideal.Quotient.mk (m ^ N) r = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hbr
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hu.mul_right_eq_zero.mp hz)
  · exact Ideal.mem_map_of_mem (algebraMap R S)

/-- Localization at a maximal ideal preserves its finite neighbourhood algebra.
The equivalence is induced by the specified localization map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3,
localization and quotients; Chapter 10, finite infinitesimal neighbourhoods. -/
noncomputable def s2e_localization_power_jet_algEquiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (m : Ideal R) [m.IsMaximal] [IsLocalization.AtPrime S m] (N : ℕ) :
    (R ⧸ m ^ N) ≃ₐ[R] (S ⧸ (m ^ N).map (algebraMap R S)) := by
  let J := (m ^ N).map (algebraMap R S)
  let f : R ⧸ m ^ N →ₐ[R] S ⧸ J := Ideal.quotientMapₐ J (Algebra.ofId R S)
    (by
      change m ^ N ≤ J.comap (algebraMap R S)
      exact Ideal.le_comap_map)
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk J (algebraMap R S r) =
      Ideal.Quotient.mk J (algebraMap R S s) at h
    apply Ideal.Quotient.eq.mpr
    apply (s2e_localization_power_jet_mem_iff R S m N (r - s)).mp
    rw [map_sub]
    exact Ideal.Quotient.eq.mp h
  · intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, hr⟩ := s2e_localization_power_jet_representative R S m N s
    refine ⟨Ideal.Quotient.mk (m ^ N) r, ?_⟩
    change Ideal.Quotient.mk J (algebraMap R S r) = Ideal.Quotient.mk J s
    exact (Ideal.Quotient.eq.mpr hr).symm

end HodgeLean.Foundations.Program
