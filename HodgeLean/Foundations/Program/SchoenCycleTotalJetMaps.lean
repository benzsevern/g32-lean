import HodgeLean.Foundations.Program.SchoenCycleTotalJets
import HodgeLean.Foundations.Program.SchoenCycleLocalPowerMaps

/-! # Evaluation maps from total-order coordinate algebras -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Parameters in a local ring's maximal ideal evaluate total-order polynomial
coordinates in the corresponding actual finite neighbourhood.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_totalJet_eval
    (σ R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (t : σ → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) (N : ℕ) :
    (MvPolynomial σ ℂ ⧸ idealOfVars σ ℂ ^ N) →ₐ[ℂ]
      (R ⧸ IsLocalRing.maximalIdeal R ^ N) := by
  let e : MvPolynomial σ ℂ →ₐ[ℂ] R := aeval t
  have he : (idealOfVars σ ℂ).map e.toRingHom ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change e (X i) ∈ IsLocalRing.maximalIdeal R
    simpa only [e, aeval_X] using ht i
  have hm : (idealOfVars σ ℂ ^ N).map e.toRingHom ≤ IsLocalRing.maximalIdeal R ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' he N
  apply Ideal.Quotient.liftₐ (idealOfVars σ ℂ ^ N)
    ((Ideal.Quotient.mkₐ ℂ (IsLocalRing.maximalIdeal R ^ N)).comp e)
  intro p hp
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (e p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hm (Ideal.mem_map_of_mem e.toRingHom hp)

/-- Evaluation on represented polynomial classes is actual parameter evaluation.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_totalJet_eval_mk
    (σ R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (t : σ → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) (N : ℕ)
    (p : MvPolynomial σ ℂ) :
    s2e_totalJet_eval σ R t ht N (Ideal.Quotient.mk (idealOfVars σ ℂ ^ N) p) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (aeval t p) := rfl

/-- A local parameter map taking the parameters back to the polynomial
coordinates gives a left inverse to finite-neighbourhood evaluation.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_totalJet_eval_left_inverse
    (σ R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (t : σ → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) (N : ℕ) (hN : 0 < N)
    (φ : R →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ idealOfVars σ ℂ ^ N))
    [IsLocalHom φ.toRingHom]
    (hφ : ∀ i, φ (t i) = Ideal.Quotient.mk (idealOfVars σ ℂ ^ N) (X i)) :
    letI := s2e_totalJet_isLocalRing σ N hN
    (s2e_local_power_quotient_lift ℂ R _ φ N (s2e_totalJet_maximalIdeal_pow σ N hN)).comp
      (s2e_totalJet_eval σ R t ht N) = AlgHom.id ℂ _ := by
  letI := s2e_totalJet_isLocalRing σ N hN
  apply Ideal.Quotient.algHom_ext
  ext i
  change s2e_local_power_quotient_lift ℂ R _ φ N (s2e_totalJet_maximalIdeal_pow σ N hN)
    (s2e_totalJet_eval σ R t ht N (Ideal.Quotient.mk (idealOfVars σ ℂ ^ N) (X i))) =
      Ideal.Quotient.mk (idealOfVars σ ℂ ^ N) (X i)
  rw [s2e_totalJet_eval_mk, aeval_X, s2e_local_power_quotient_lift_mk]
  exact hφ i

end HodgeLean.Foundations.Program
