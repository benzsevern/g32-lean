import HodgeLean.Foundations.Program.SchoenTowerI2aFieldRescaling
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchUnits

/-! Exact rational rescaling through a weighted ideal transform.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A weighted principal ideal identity removes the entire exceptional power and rational correction while retaining generation of the original field. -/
theorem s2v_i2a_weighted_equation_rescaling
    {R K J : Type*} [CommRing R] [IsDomain R] [Field K] [Fintype J]
    (ρ : R →+* K) (F G : J → R) (n : J → ℕ)
    (e A B : R) (m : ℕ) (he : ρ e ≠ 0) (hA : ρ A ≠ 0) (hB : ρ B ≠ 0)
    (hI : (∏ j, Ideal.span {F j} ^ n j) =
      (∏ j, Ideal.span {G j} ^ n j) * Ideal.span {e} ^ m)
    (ε : Rˣ) (t : K)
    (heq : t ^ m * ρ B ^ m = ρ (ε : R) * (∏ j, ρ (F j) ^ n j) * ρ A ^ m)
    (hgen : Subfield.closure (Set.range ρ ∪ {t}) = ⊤) :
    ∃ (w : K) (δ : Rˣ),
      Subfield.closure (Set.range ρ ∪ {w}) = ⊤ ∧
      w ^ m = ρ (δ : R) * ∏ j, ρ (G j) ^ n j := by
  have hI' : Ideal.span {∏ j, F j ^ n j} =
      Ideal.span {(∏ j, G j ^ n j) * e ^ m} := by
    simpa only [Ideal.span_singleton_pow, Ideal.prod_span_singleton,
      Ideal.span_singleton_mul_span_singleton] using hI
  obtain ⟨δ, hδ⟩ := (Ideal.span_singleton_eq_span_singleton.mp hI').symm
  have hprod : (∏ j, F j ^ n j) = (δ : R) * (∏ j, G j ^ n j) * e ^ m := by
    rw [← hδ]
    ring
  have hprodK := congrArg ρ hprod
  simp only [map_prod, map_pow, map_mul] at hprodK
  have H : (t * ρ B) ^ m =
      ρ ((ε * δ : Rˣ) : R) * (∏ j, ρ (G j) ^ n j) * (ρ e * ρ A) ^ m := by
    rw [mul_pow, heq, hprodK, Units.val_mul, map_mul, mul_pow]
    ring
  refine ⟨t * ρ B / (ρ e * ρ A), ε * δ, ?_, ?_⟩
  · have hmul := s2v_i2a_rescaled_generator_field ρ (t * ρ B) B hB
    rw [mul_div_cancel_right₀ t hB] at hmul
    have hdiv := s2v_i2a_rescaled_generator_field ρ (t * ρ B) (e * A)
      (by rw [map_mul]; exact mul_ne_zero he hA)
    rw [map_mul] at hdiv
    exact hdiv.trans (hmul.symm.trans hgen)
  · rw [div_pow, H, mul_div_cancel_right₀ _ (pow_ne_zero m (mul_ne_zero he hA))]

end HodgeLean.Foundations.Program
