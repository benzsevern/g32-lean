import HodgeLean.Foundations.TubularEuler.MetricNormalLiftAnalyticHelpers

/-! # Analytic variation of uniquely metric-orthogonal vectors

A vector family specified by the original metric and quotient equations
agrees locally with the analytic inverse-metric Gram formula.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.TubularEuler

/-- An orthogonal representative family is analytic when its actual metric,
quotient, and value coefficients are analytic and retain positivity and
surjectivity near the reference point. Analyticity of the representatives
themselves is a conclusion, not an input.
Source: `metricNormalLift_unique` and `metricNormalLift_analyticAt`.
HC no distance; AV milestone no distance. -/
theorem metric_normal_vector_family_analytic
    {B E N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]
    [FiniteDimensional ℝ N]
    (P : B → E →L[ℝ] E) (T : B → E →L[ℝ] N) (n : B → N)
    (v : B → E) (b : B)
    (hP : AnalyticAt ℝ P b) (hT : AnalyticAt ℝ T b) (hn : AnalyticAt ℝ n b)
    (hpos : ∀ᶠ c in 𝓝 b, ∀ u : E, u ≠ 0 → 0 < inner ℝ (P c u) u)
    (hsurj : ∀ᶠ c in 𝓝 b, Function.Surjective (T c))
    (hv : ∀ᶠ c in 𝓝 b, T c (v c) = n c ∧
      ∀ w : E, T c w = 0 → inner ℝ (P c (v c)) w = 0) :
    AnalyticAt ℝ v b := by
  have hL := metricNormalLift_analyticAt P T b hP hT
    hpos.self_of_nhds hsurj.self_of_nhds
  have hformula : AnalyticAt ℝ (fun c => metricNormalLift (P c) (T c) (n c)) b :=
    (hL.contDiffAt.clm_apply hn.contDiffAt).analyticAt
  have heq : v =ᶠ[𝓝 b] (fun c => metricNormalLift (P c) (T c) (n c)) := by
    filter_upwards [hpos, hsurj, hv] with c hp hs hc
    exact metricNormalLift_unique (P c) hp (T c) hs (n c) (v c) hc.1 hc.2
  exact (hformula.contDiffAt.congr_of_eventuallyEq heq).analyticAt

#print axioms metric_normal_vector_family_analytic

end HodgeLean.Foundations.TubularEuler
