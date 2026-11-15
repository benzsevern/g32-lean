import HodgeLean.Foundations.Program.SchoenCycleC1PowerSeriesAdicCoordinates
import HodgeLean.Foundations.Program.SchoenCycleC1PowerSeriesAdicAction

/-! # Polynomial-adic coordinates retaining all scalar actions -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- One power series comparison preserves all polynomial values and every
specified scalar action on the polynomial coordinate. -/
theorem s2e_c1_equivariant_power_series_coordinates
    (k : Type*) [CommRing k] :
    let I : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
    ∃ E : PowerSeries k ≃ₐ[k] AdicCompletion I (Polynomial k),
      (∀ p : Polynomial k, E (p : PowerSeries k) = AdicCompletion.of _ _ p) ∧
      ∀ (ζ : k) (hα : ∀ n : ℕ, ∀ p ∈ I ^ n,
        Polynomial.aeval (Polynomial.C ζ * Polynomial.X) p ∈ I ^ n),
        (s2e_adic_algebra_map I I (Polynomial.aeval (Polynomial.C ζ * Polynomial.X)) hα).comp
          E.toAlgHom = E.toAlgHom.comp (PowerSeries.rescaleAlgHom ζ) := by
  obtain ⟨E, hE⟩ := s2e_c1_power_series_polynomial_adic_coordinates k
  have hv (p : Polynomial k) : E (p : PowerSeries k) = AdicCompletion.of _ _ p := by
    rw [Polynomial.pUnitAlgEquiv_symm_toPowerSeries]
    rw [hE, AlgEquiv.apply_symm_apply]
  exact ⟨E, hv, fun ζ hα => s2e_c1_power_series_adic_scalar_action k E hv ζ hα⟩

end HodgeLean.Foundations.Program
