import HodgeLean.Foundations.Program.G32Native.PairedResidualGivenPreparationOrders
import HodgeLean.Foundations.AnalyticDivisorAlgebraic5

/-! # Adjusted divisor orders of a supplied preparation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
/-- Every supplied full-system root tuple retains its exact nearby multiplicities. -/
theorem residual_system_given_preparation_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n m : ℕ}
    (y : Fin n → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (b : Fin m → W) (p : C)
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    {d : ℕ} (g u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ)
    (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', (if p ∈ Set.range y then z else 1) *
      HurwitzPrymRR_loc hE ((∑ i, a' i • b i : W).val) p z = g (a', z))
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hprep : (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
      fun tz => u tz * monicInLast c tz)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r < ε ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈ (extChartAt 𝓘(ℂ, E) p).target) ∧
      ∀ᶠ t in 𝓝 (0 : Fin m → ℂ), (∑ i, (a + t) i • b i) ≠ 0 ∧
        ∀ z : Fin d → ℂ, monicPoly c t = ∏ j, (Polynomial.X - Polynomial.C (z j)) →
          (∀ j, z j ∈ Metric.ball (0 : ℂ) r) ∧
          ∀ ζ ∈ Metric.ball (0 : ℂ) r,
            (Fintype.card {j : Fin d // z j = ζ} : ℤ) =
              (b4c_divForm (hE := hE) (∑ i, (a + t) i • b i : W).val + s2e_markedPoleDivisor y)
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE ζ)) := by
  obtain ⟨r, hr, hrε, ht, ho⟩ := residual_system_given_preparation_orders
    hE y hy W hW b p a ha g u c he hu hu0 hprep hε
  refine ⟨r, hr, hrε, ht, ?_⟩
  filter_upwards [ho, s2e_monic_rootTuples_eventually_small c hc hc0 hr] with t ht hs
  refine ⟨ht.1, fun z hz => ⟨?_, ?_⟩⟩
  · have hn := hs z hz
    rw [dist_zero_right, pi_norm_lt_iff hr] at hn
    intro j
    simpa only [Metric.mem_ball, dist_zero_right] using hn j
  · intro ζ hζ
    obtain ⟨e, heP, heD⟩ := ht.2 ζ hζ
    have heval : (fun v => (monicPoly c t).eval v) =
        (fun v => monicInLast c (t, v)) := funext (spec_monicPoly c t).2.2
    have hcount := s2e_rootTuple_analytic_order (monicPoly c t) z hz ζ
    rw [heval, heP] at hcount
    have hnat : e = Fintype.card {j : Fin d // z j = ζ} := by exact_mod_cast hcount
    rw [← hnat]
    exact heD

#print axioms residual_system_given_preparation_root_multiplicities
end HodgeLean.Foundations.Program.G32Native
