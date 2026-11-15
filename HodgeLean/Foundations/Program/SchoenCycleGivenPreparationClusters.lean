import HodgeLean.Foundations.Program.SchoenCycleGivenPreparationRoots
import HodgeLean.Foundations.Program.SchoenCyclePairedClusters

/-! # Nearby adjusted divisors of supplied simultaneous preparations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The supplied preparations recover the entire nearby adjusted divisor from their root multisets.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_given_preparations_cluster_divisors
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n k s : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (b : Fin n → b3_HolForm E C × (Fin r → ℂ))
    (a : Fin n → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (m : Fin s → ℕ) (hm : ∑ l, m l = 2 * k)
    (p : Fin s → C) (hp : Function.Injective p)
    (g u : Fin s → (Fin n → ℂ) × ℂ → ℂ)
    (c : (l : Fin s) → Fin (m l) → (Fin n → ℂ) → ℂ)
    (he : ∀ l, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', (if p l ∈ Set.range y then z else 1) *
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) (p l) z = g l (a', z))
    (hu : ∀ l, AnalyticAt ℂ (u l) 0) (hu0 : ∀ l, u l 0 ≠ 0)
    (hprep : ∀ l, (fun tz => g l (a + tz.1, tz.2)) =ᶠ[𝓝 0]
      fun tz => u l tz * monicInLast (c l) tz)
    (hc : ∀ l j, ContinuousAt (c l j) 0) (hc0 : ∀ l j, c l j 0 = 0) :
    ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∑ i, (a + t) i • b i) ≠ 0 ∧
      ∀ z : (l : Fin s) → Fin (m l) → ℂ,
        (∀ l, monicPoly (c l) t = ∏ j, (Polynomial.X - Polynomial.C (z l j))) →
        s2e_adjustedDifferentialDivisor hE w y (∑ i, (a + t) i • b i) =
          ∑ l, ∑ j, Finsupp.single
            ((extChartAt 𝓘(ℂ, E) (p l)).symm
              (extChartAt 𝓘(ℂ, E) (p l) (p l) + b4cov_lineEquiv hE (z l j))) (1 : ℤ) := by
  obtain ⟨ε, hε, _, hsep⟩ := s2e_curve_chart_discs_disjoint hE p hp
  choose ρ hρ hρε ht hevent using fun l =>
    s2e_given_preparation_root_multiplicities hE w x hres y hy horder hout b (p l) a ha
      (g l) (u l) (c l) (he l) (hu l) (hu0 l) (hprep l) (hc l) (hc0 l) (hε l)
  have htend : Tendsto (fun t : Fin n → ℂ => a + t) (𝓝 0) (𝓝 a) := by
    simpa only [add_zero] using
      (show Continuous (fun t : Fin n → ℂ => a + t) from continuous_const.add continuous_id).tendsto 0
  filter_upwards [eventually_all.mpr hevent,
    htend.eventually (s2e_linear_family_eventually_ne_zero b a ha)] with t he' hne
  refine ⟨hne, fun z hz => ?_⟩
  have hzi : ∀ l j, z l j ∈ Metric.ball (0 : ℂ) (ρ l) :=
    fun l => ((he' l).2 (z l) (hz l)).1
  apply s2e_paired_divisor_eq_disjoint_local_tuples hE w x hres y hy horder hout hgenus
    _ hne p ρ m z ht hzi
    (fun l => ((he' l).2 (z l) (hz l)).2)
  · rw [s2e_adjustedDifferentialDivisor_degree hE w x hres y hgenus _ hne, hm]
  · intro l l' hll'
    exact (hsep hll').mono (Set.image_mono (Metric.ball_subset_ball (hρε l).le))
      (Set.image_mono (Metric.ball_subset_ball (hρε l').le))

#print axioms s2e_given_preparations_cluster_divisors
end HodgeLean.Foundations.Program
