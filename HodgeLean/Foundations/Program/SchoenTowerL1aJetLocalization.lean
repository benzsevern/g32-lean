import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Nonzero first-order classes under principal localization

Clearing a denominator transports a nonzero local first-order class back to
the original affine coordinate ring. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A nonzero first-order class in a principal localization has a numerator with nonzero first-order class in the original point kernel.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, principal localization and tangent vectors. -/
theorem s2v_l1a_localized_first_jet_numerator
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K] [Algebra R A]
    (d : R) [IsLocalization.Away d A]
    (ev : R →+* K) (evA : A →+* K)
    (heval : evA.comp (algebraMap R A) = ev)
    (u : A) (hu : u ∈ RingHom.ker evA) (hnu : u ∉ RingHom.ker evA ^ 2) :
    ∃ r : R, r ∈ RingHom.ker ev ∧ r ∉ RingHom.ker ev ^ 2 := by
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj d u
  have hmap : Ideal.map (algebraMap R A) (RingHom.ker ev) ≤ RingHom.ker evA := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (DFunLike.congr_fun heval x).trans hx
  refine ⟨r, ?_, ?_⟩
  · change ev r = 0
    rw [← DFunLike.congr_fun heval r, RingHom.comp_apply, ← hr, map_mul]
    change evA u * _ = 0
    rw [hu, zero_mul]
  · intro hbad
    apply hnu
    have hm := Ideal.mem_map_of_mem (algebraMap R A) hbad
    rw [Ideal.map_pow] at hm
    have hm' : algebraMap R A r ∈ RingHom.ker evA ^ 2 :=
      (pow_le_pow_left' hmap 2) hm
    rw [← hr, mul_comm] at hm'
    apply (Ideal.unit_mul_mem_iff_mem (RingHom.ker evA ^ 2) ?_).mp hm'
    exact (IsLocalization.map_units A ⟨d, Submonoid.mem_powers d⟩).pow n

end HodgeLean.Foundations.Program
