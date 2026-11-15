import HodgeLean.Foundations.Curves.AbelTheorem.CurveBilinear
import HodgeLean.Foundations.Curves.AbelTheorem.FrameMeromorphicPeriods
import HodgeLean.Foundations.Curves.AbelTheorem.ComplementLoopPeriod

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Module Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem integral_periods_from_frame (h : finrank ℂ E = 1)
    (D : C →₀ ℤ) (F : PeriodFrame (E := E) D) (v : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) v x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h v x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h v x) 0)
    (hpa : ∀ i, ∃ n : ℤ, loopIntegral (F.a i) v = (2 * Real.pi * Complex.I) * (n : ℂ))
    (hpb : ∀ i, ∃ n : ℤ, loopIntegral (F.b i) v = (2 * Real.pi * Complex.I) * (n : ℂ)) :
    ∀ γ : b3_SmoothLoop E (divisorComplement D),
      Complex.exp (b3_period E (divisorComplement D) γ
        (divisorDifferentialRestriction h D v ha)) = 1 := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  intro γ
  rw [divisor_complement_loop_period_eq h D v ha γ]
  obtain ⟨n, hn⟩ := integral_meromorphic_loop_period_of_frame h D F v hr ha hpa hpb
    (ambient_divisor_complement_loop D γ) (fun t => (γ.val t).property)
  rw [hn]
  exact Complex.exp_eq_one_iff.mpr ⟨n, by ring⟩

end HodgeLean.Foundations.Curves.AbelTheorem
