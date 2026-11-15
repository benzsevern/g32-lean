import HodgeLean.Foundations.Program.SchoenCycleGivenPreparationOrders
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
namespace HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
/-- Every root tuple of the supplied preparation retains the nearby adjusted multiplicities.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_given_preparation_root_multiplicities
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (p : C)
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    {d : ℕ} (g u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ)
    (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', (if p ∈ Set.range y then z else 1) *
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) p z = g (a', z))
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
              s2e_adjustedDifferentialDivisor hE w y (∑ i, (a + t) i • b i)
                ((extChartAt 𝓘(ℂ, E) p).symm
                  (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE ζ)) := by
  obtain ⟨r, hr, hrε, ht, ho⟩ := s2e_given_preparation_adjusted_orders
    hE w x hres y hy horder hout b p a ha g u c he hu hu0 hprep hε
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

#print axioms s2e_given_preparation_root_multiplicities
end HodgeLean.Foundations.Program
