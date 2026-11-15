import HodgeLean.Foundations.Program.SchoenCycleCartierLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A coefficient-ring isomorphism transports a free rank-one actual image ideal.
Source: Mathlib, `Ideal.map_span`; Hartshorne, Algebraic Geometry, II.6,
regular local equations of effective Cartier divisors. -/
theorem s2v_i2a_cartier_ideal_ring_equiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) (hI : Nonempty (I ≃ₗ[R] R)) :
    Nonempty ((I.map e.toRingHom) ≃ₗ[S] S) := by
  obtain ⟨f⟩ := hI
  obtain ⟨z, hz, hregular⟩ := s2e_free_ideal_regular_generator I f
  rw [hz, Ideal.map_span, Set.image_singleton]
  apply s2e_regular_principal_ideal_free
  intro a b hab
  apply e.symm.injective
  apply hregular
  have H := congrArg e.symm hab
  change e.symm (a * e z) = e.symm (b * e z) at H
  rwa [map_mul, map_mul, e.symm_apply_apply] at H

end HodgeLean.Foundations.Program
