import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeConjugacy
import HodgeLean.Foundations.Program.SchoenTowerL1bActionHalfPlaneLift

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The supplied homeomorphism has a continuous logarithmic representative
on a half-plane, with a single integral deck coefficient. -/
theorem s2v_l1b_action_nativeConjugacy_log_lift
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    (E : M ≃ₜ ComplexPoint Y) (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆
      (s2v_l1b_action_nativeConjugacy Y E x).source ∧
      ∃ (L : ℂ → ℂ) (k : ℤ),
        ContinuousOn L {z : ℂ | z.re < Real.log r} ∧
        (∀ z, z.re < Real.log r → Complex.exp (L z) =
          s2v_l1b_action_nativeConjugacy Y E x (Complex.exp z)) ∧
        (∀ z, z.re < Real.log r →
          L (z + 2 * Real.pi * Complex.I) = L z + (k : ℂ) * (2 * Real.pi * Complex.I)) := by
  obtain ⟨r, hr, hb, hc, hn⟩ := s2v_l1b_action_nativeConjugacy_disk Y E x
  obtain ⟨L, hL, he⟩ := s2v_l1b_action_halfplane_log_lift
    (s2v_l1b_action_nativeConjugacy Y E x) r hr hc hn
  obtain ⟨k, hk⟩ := s2v_l1b_action_halfplane_deck_coefficient
    (s2v_l1b_action_nativeConjugacy Y E x) L (Real.log r) hL he
  exact ⟨r, hr, hb, L, k, hL, he, hk⟩

end HodgeLean.Foundations.Program
