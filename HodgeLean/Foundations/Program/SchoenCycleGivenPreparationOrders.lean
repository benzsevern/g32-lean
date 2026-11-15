import HodgeLean.Foundations.Program.SchoenCyclePreparationLocalOrders

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

/-- The supplied prepared polynomial has exactly the nearby adjusted differential orders.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_given_preparation_adjusted_orders
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
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r < ε ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈ (extChartAt 𝓘(ℂ, E) p).target) ∧
      ∀ᶠ t in 𝓝 (0 : Fin m → ℂ), (∑ i, (a + t) i • b i) ≠ 0 ∧
        ∀ z ∈ Metric.ball (0 : ℂ) r, ∃ e : ℕ,
          analyticOrderAt (fun z => monicInLast c (t, z)) z = e ∧
          (e : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, (a + t) i • b i)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  classical
  obtain ⟨ρ, hρ, hord⟩ := s2e_preparation_uniform_vertical_orders
    (fun tz => g (a + tz.1, tz.2)) u c hu hu0 hprep
  obtain ⟨σ, hσ, hchart⟩ := s2e_curve_chart_disc_avoids_marked hE y p
  obtain ⟨τ, hτ, heτ⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp he)
  obtain ⟨r, hr, hrlim⟩ := exists_between (lt_min hρ (lt_min hσ (lt_min hτ hε)))
  have hrρ := hrlim.trans_le (min_le_left ρ (min σ (min τ ε)))
  have hrσ := hrlim.trans_le ((min_le_right ρ (min σ (min τ ε))).trans
    (min_le_left σ (min τ ε)))
  have hrτ := hrlim.trans_le ((min_le_right ρ (min σ (min τ ε))).trans
    ((min_le_right σ (min τ ε)).trans (min_le_left τ ε)))
  have hrε := hrlim.trans_le ((min_le_right ρ (min σ (min τ ε))).trans
    ((min_le_right σ (min τ ε)).trans (min_le_right τ ε)))
  have htend : Tendsto (fun t : Fin m → ℂ => a + t) (𝓝 0) (𝓝 a) := by
    simpa only [add_zero] using (show Continuous (fun t : Fin m → ℂ => a + t) from continuous_const.add continuous_id).tendsto (0 : Fin m → ℂ)
  refine ⟨r, hr, hrε, fun z hz => (hchart z (Metric.ball_subset_ball hrσ.le hz)).1, ?_⟩
  filter_upwards [hord, htend.eventually (s2e_linear_family_eventually_ne_zero b a ha)]
    with t ht hne
  refine ⟨hne, fun z hz => ?_⟩
  obtain ⟨hg, hgo⟩ := ht z (Metric.ball_subset_ball hrρ.le hz)
  have he' : (fun ζ => (if p ∈ Set.range y then ζ else 1) *
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, (a + t) i • b i)) p ζ)
      =ᶠ[𝓝[≠] z] fun ζ => g (a + t, ζ) := by
    by_cases hz0 : z = 0
    · subst z
      exact he.mono (fun ζ hζ => hζ (a + t))
    · have hn : ∀ᶠ ζ in 𝓝 z, (if p ∈ Set.range y then ζ else 1) *
          HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, (a + t) i • b i)) p ζ =
          g (a + t, ζ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hrτ.le hz),
          eventually_ne_nhds hz0] with ζ hζ hζ0
        exact heτ ζ hζ hζ0 (a + t)
      exact hn.filter_mono nhdsWithin_le_nhds
  obtain ⟨e, heG, heD⟩ := s2e_pole_corrected_chart_order hE w x hres y hy _ hne p z
    (hchart z (Metric.ball_subset_ball hrσ.le hz)).1
    (hchart z (Metric.ball_subset_ball hrσ.le hz)).2 _ hg he'
  exact ⟨e, hgo.symm.trans heG, heD⟩

#print axioms s2e_given_preparation_adjusted_orders
end HodgeLean.Foundations.Program
