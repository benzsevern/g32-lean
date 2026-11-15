import HodgeLean.Foundations.Program.SchoenTowerI2aCartierCoefficientTransport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Injective transport into an integral coefficient ring preserves a free
rank-one ideal, retaining the actual extended ideal.
Source: Hartshorne, Algebraic Geometry, II.6, regular equations of effective
Cartier divisors; Mathlib, `Ideal.map_span`. -/
theorem s2v_i2a_cartier_ideal_injective_transport
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (hφ : Function.Injective φ) (I : Ideal R)
    (hI : Nonempty (I ≃ₗ[R] R)) : Nonempty ((I.map φ) ≃ₗ[S] S) := by
  obtain ⟨e⟩ := hI
  obtain ⟨z, hz, hregular⟩ := s2e_free_ideal_regular_generator I e
  have hz0 : z ≠ 0 := by
    intro h
    have H : (1 : R) * z = 0 * z := by simp [h]
    exact one_ne_zero (hregular H)
  have hφz : φ z ≠ 0 := fun h => hz0 (hφ (h.trans φ.map_zero.symm))
  rw [hz, Ideal.map_span, Set.image_singleton]
  exact s2e_regular_principal_ideal_free _ (fun _ _ h => mul_right_cancel₀ hφz h)

end HodgeLean.Foundations.Program
