import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemChartOrder
import HodgeLean.Foundations.Program.SchoenCyclePairedLocalPolynomial

/-! # Local polynomial presentations of the full pole system -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Local full-system polynomials retain all nearby adjusted divisor orders. -/
theorem residual_system_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n m : ℕ}
    (y : Fin n → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (b : Fin m → W)
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0) (p : C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (R δ : ℝ) (c : Fin d → (Fin m → ℂ) → ℂ),
      (d : ℤ) = (b4c_divForm (hE := hE) (∑ i, a i • b i : W).val + s2e_markedPoleDivisor y) p ∧
      0 < R ∧ R < ε ∧ 0 < δ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R,
        extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
          (extChartAt 𝓘(ℂ, E) p).target) ∧
      (∀ j, AnalyticOnNhd ℂ (c j) (Metric.ball a δ)) ∧
      ∀ a' ∈ Metric.ball a δ, (∑ i, a' i • b i) ≠ 0 →
        (∀ z, HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', z) = 0 →
          z ∈ Metric.ball (0 : ℂ) R) ∧
        ∀ z ∈ Metric.ball (0 : ℂ) R, ∃ e : ℕ,
          analyticOrderAt (fun ζ =>
            HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c (a', ζ)) z = e ∧
          (e : ℤ) = (b4c_divForm (hE := hE) (∑ i, a' i • b i : W).val + s2e_markedPoleDivisor y)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  classical
  obtain ⟨g, hg, heRaw⟩ := residual_system_pole_correction hE (Set.range y) W
    (fun q => ⟨(hW q).1, (hW q).2.1, (hW q).2.2.1⟩) b p
  have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
      HurwitzPrymRR_loc hE (∑ i, a i • b i : W).val p z = g (a, z) := by
    filter_upwards [heRaw] with z hz
    intro a
    by_cases hp : p ∈ Set.range y
    · simpa only [ite_eq_left hp] using hz a
    · simpa only [ite_eq_right hp] using hz a
  let v : W := ∑ i, a i • b i
  have hg0 : AnalyticAt ℂ (fun z => g (a, z)) 0 :=
    (hg a).comp (f := fun z : ℂ => (a, z)) (analyticAt_const.prod analyticAt_id)
  obtain ⟨d, hd, hD⟩ := residual_normalized_pole_corrected_order hE y hy
    ⟨v.val, (hW v).1⟩ (fun h => ha (Subtype.ext h)) (hW v).2.2.1 (hW v).2.2.2 p
    (fun z => g (a, z)) hg0 (he.mono (fun z hz => hz a))
  obtain ⟨ρ, hρ, hchart⟩ := s2e_curve_chart_disc_avoids_marked hE y p
  obtain ⟨σ, hσ, hσeq⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp he)
  obtain ⟨R, hR, hRlim, δ, hδ, hf, hb, hcount⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_zeroCount_eq_order
      (hg a) hd (lt_min hε (lt_min hρ hσ))
  have hRε := hRlim.trans_le (min_le_left ε (min ρ σ))
  have hRρ := hRlim.trans_le ((min_le_right ε (min ρ σ)).trans (min_le_left ρ σ))
  have hRσ := hRlim.trans_le ((min_le_right ε (min ρ σ)).trans (min_le_right ρ σ))
  obtain ⟨c, hc, hpoly⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_exists_monicInLast_orders hf hb
      (hcount a (Metric.mem_ball_self hδ))
  refine ⟨d, R, δ, c, hD, hR, hRε, hδ, ?_, hc, ?_⟩
  · intro z hz
    exact (hchart z ((Metric.mem_closedBall.mp hz).trans_lt hRρ)).1
  · intro a' ha' hne
    obtain ⟨hroot, hpolord⟩ := hpoly a' ha'
    refine ⟨hroot, ?_⟩
    intro z hz
    have hzρ : z ∈ Metric.ball (0 : ℂ) ρ :=
      (Metric.mem_ball.mp hz).trans hRρ
    have hzσ : z ∈ Metric.ball (0 : ℂ) σ :=
      (Metric.mem_ball.mp hz).trans hRσ
    have hg' : AnalyticAt ℂ (fun ζ => g (a', ζ)) z :=
      (hf (a', z) ⟨Metric.ball_subset_closedBall ha', Metric.ball_subset_closedBall hz⟩).comp
        (f := fun ζ : ℂ => (a', ζ)) (analyticAt_const.prod analyticAt_id)
    have he' : (fun ζ => (if p ∈ Set.range y then ζ else 1) *
        HurwitzPrymRR_loc hE ((∑ i, a' i • b i : W).val) p ζ)
        =ᶠ[𝓝[≠] z] fun ζ => g (a', ζ) := by
      by_cases hz0 : z = 0
      · subst z
        exact he.mono (fun ζ hζ => hζ a')
      · have heN : ∀ᶠ ζ in 𝓝 z, (if p ∈ Set.range y then ζ else 1) *
            HurwitzPrymRR_loc hE ((∑ i, a' i • b i : W).val) p ζ =
            g (a', ζ) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hzσ, eventually_ne_nhds hz0] with ζ hζ hζ0
          exact hσeq ζ hζ hζ0 a'
        exact heN.filter_mono nhdsWithin_le_nhds
    obtain ⟨e, heord, heD⟩ := residual_normalized_pole_corrected_chart_order hE y hy
      ⟨(∑ i, a' i • b i : W).val, (hW _).1⟩ (fun h => hne (Subtype.ext h))
      (hW _).2.2.1 (hW _).2.2.2 p z (hchart z hzρ).1 (hchart z hzρ).2
      (fun ζ => g (a', ζ)) hg' he'
    exact ⟨e, (hpolord z hz).trans heord, heD⟩

#print axioms residual_system_local_polynomial
end HodgeLean.Foundations.Program.G32Native
