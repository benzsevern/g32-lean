import HodgeLean.Foundations.Program.SchoenCyclePoleClearing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Local polynomial preparation of the paired family -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
/-- A nonzero finite linear combination remains nonzero for nearby scalar parameters. -/
theorem s2e_linear_family_eventually_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (b : Fin n → V)
    (a : Fin n → ℂ) (ha : (∑ i, a i • b i) ≠ 0) :
    ∀ᶠ a' in 𝓝 a, (∑ i, a' i • b i) ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ ha
  let f : (Fin n → ℂ) → ℂ := fun a' => ∑ i, a' i * φ (b i)
  have hf : Continuous f := by
    exact continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)
  have he (a' : Fin n → ℂ) : f a' = φ (∑ i, a' i • b i) := by
    simp only [f, map_sum, map_smul, smul_eq_mul]
  have hfa : f a ≠ 0 := by rwa [he]
  filter_upwards [hf.continuousAt.eventually_ne hfa] with a' ha'
  intro hz
  apply ha'
  rw [he, hz, map_zero]

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Pole correction yields a Weierstrass polynomial of the exact adjusted
divisor multiplicity at every nonzero parameter and every curve point.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems;
Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Theorem 2. -/
theorem s2e_paired_family_local_preparation
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (p : C) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, (if p ∈ Set.range y then z else 1) *
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z =
          g (a, z)) ∧
      ∀ a, (∑ i, a i • b i) ≠ 0 →
        ∃ d : ℕ, (d : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, a i • b i) p ∧
          analyticOrderAt (fun z => g (a, z)) 0 = d ∧
          ∃ u : (Fin m → ℂ) × ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
            ∃ c : Fin d → (Fin m → ℂ) → ℂ,
              (∀ j, AnalyticAt ℂ (c j) 0 ∧ c j 0 = 0) ∧
              (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
                fun tz => u tz * HodgeLean.Foundations.AnalyticDivisorAlgebraic4.monicInLast c tz := by
  obtain ⟨g, hg, he⟩ := s2e_paired_family_pole_correction hE w y horder hout b p
  refine ⟨g, hg, he, ?_⟩
  intro a ha
  let v := ∑ i, a i • b i
  have hg' : AnalyticAt ℂ (fun z => g (a, z)) 0 :=
    (hg a).comp (f := fun z : ℂ => (a, z)) (analyticAt_const.prod analyticAt_id)
  obtain ⟨d, hd, hD⟩ := s2e_pole_corrected_order hE w x hres y hy v.1 v.2 ha p
    (fun z => g (a, z)) hg' (he.mono (fun z hz => hz a))
  refine ⟨d, hD, hd, ?_⟩
  have hf : AnalyticAt ℂ (fun tz : (Fin m → ℂ) × ℂ => g (a + tz.1, tz.2)) 0 :=
    (hg a).comp_of_eq ((analyticAt_const.add analyticAt_fst).prod analyticAt_snd)
      (by simp only [Prod.fst_zero, Prod.snd_zero, add_zero])
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic4.spec_weierstrass_preparation hf
  simpa only [Prod.fst_zero, add_zero] using hd

/-- A small coordinate disc avoids all marked points other than its centre.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local divisor coordinates. -/
theorem s2e_curve_chart_disc_avoids_marked
    [T2Space C] (hE : Module.finrank ℂ E = 1) {n : ℕ}
    (y : Fin n → C) (p : C) :
    ∃ R > 0, ∀ z ∈ Metric.ball (0 : ℂ) R,
      extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z ∈
        (extChartAt 𝓘(ℂ, E) p).target ∧
      (z ≠ 0 → (extChartAt 𝓘(ℂ, E) p).symm
        (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z) ∉ Set.range y) := by
  classical
  let K := Set.range y \ {p}
  have hK : IsClosed K := ((Set.finite_range y).subset Set.sdiff_subset).isClosed
  have hpK : p ∉ K := fun hp => hp.2 rfl
  obtain ⟨R, hR, hh⟩ := s2e_curve_chart_disc_inside hE p Kᶜ
    (hK.isOpen_compl.mem_nhds hpK)
  refine ⟨R, hR, ?_⟩
  intro z hz
  obtain ⟨ht, hk⟩ := hh z hz
  refine ⟨ht, ?_⟩
  intro hzne hmark
  apply hk
  refine ⟨hmark, ?_⟩
  intro hqp
  have hc : extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z =
      extChartAt 𝓘(ℂ, E) p p :=
    ((extChartAt 𝓘(ℂ, E) p).right_inv ht).symm.trans (congrArg _ hqp)
  have hz0 : b4cov_lineEquiv hE z = 0 := by
    exact add_left_cancel (hc.trans (add_zero _).symm)
  exact hzne ((b4cov_lineEquiv hE).injective (hz0.trans (map_zero _).symm))

/-- Local polynomial roots have exactly the adjusted divisor multiplicities
throughout a disc, also at parameters with zero residues and at repeated roots.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14;
Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B, Theorem 2. -/
theorem s2e_paired_family_local_polynomial
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ))
    (a : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0) (p : C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (R δ : ℝ) (c : Fin d → (Fin m → ℂ) → ℂ),
      (d : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, a i • b i) p ∧
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
          (e : ℤ) = s2e_adjustedDifferentialDivisor hE w y (∑ i, a' i • b i)
            ((extChartAt 𝓘(ℂ, E) p).symm
              (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)) := by
  classical
  obtain ⟨g, hg, he⟩ := s2e_paired_family_pole_correction hE w y horder hout b p
  let v := ∑ i, a i • b i
  have hg0 : AnalyticAt ℂ (fun z => g (a, z)) 0 :=
    (hg a).comp (f := fun z : ℂ => (a, z)) (analyticAt_const.prod analyticAt_id)
  obtain ⟨d, hd, hD⟩ := s2e_pole_corrected_order hE w x hres y hy v.1 v.2 ha p
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
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) p ζ)
        =ᶠ[𝓝[≠] z] fun ζ => g (a', ζ) := by
      by_cases hz0 : z = 0
      · subst z
        exact he.mono (fun ζ hζ => hζ a')
      · have heN : ∀ᶠ ζ in 𝓝 z, (if p ∈ Set.range y then ζ else 1) *
            HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) p ζ =
            g (a', ζ) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hzσ, eventually_ne_nhds hz0] with ζ hζ hζ0
          exact hσeq ζ hζ hζ0 a'
        exact heN.filter_mono nhdsWithin_le_nhds
    obtain ⟨e, heord, heD⟩ := s2e_pole_corrected_chart_order hE w x hres y hy
      (∑ i, a' i • b i) hne p z (hchart z hzρ).1 (hchart z hzρ).2
      (fun ζ => g (a', ζ)) hg' he'
    exact ⟨e, (hpolord z hz).trans heord, heD⟩

end HodgeLean.Foundations.Program
