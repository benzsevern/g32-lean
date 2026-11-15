import HodgeLean.Foundations.Program.SchoenCycleLinearPreparedVariation
import HodgeLean.Foundations.Program.SchoenCycleRegularRatio

/-! # Divisibility of paired differential variations from prepared coefficients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
local instance : Module ℂ ℂ := Semiring.toModule
local instance : NormedSpace ℂ ℂ := NormedField.toNormedSpace
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Stationarity of the prepared coefficients forces local analytic divisibility
of the actual paired differential variation at the specified curve point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres. -/
theorem s2e_paired_prepared_local_divisibility
    (hE : Module.finrank ℂ E = 1) {r n m d : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (a δ : Fin m → ℂ) (p : C)
    (g u : (Fin m → ℂ) × ℂ → ℂ) (c : Fin d → (Fin m → ℂ) → ℂ)
    (hg : AnalyticAt ℂ g (a, 0))
    (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t,
      (if p ∈ Set.range y then z else 1) * HurwitzPrymRR_loc hE
        (s2e_pairedDifferentialLinear hE w (∑ i, t i • b i)) p z = g (t, z))
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0)
    (hδ : ∀ j, fderiv ℂ (c j) 0 δ = 0)
    (hprep : (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
      fun tz => u tz * monicInLast c tz) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        HurwitzPrymRR_loc hE
          (s2e_pairedDifferentialLinear hE w (∑ i, δ i • b i)) p z =
        q z * HurwitzPrymRR_loc hE
          (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) p z := by
  classical
  let F := fun i => HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (b i)) p
  let L : ℂ → ((Fin m → ℂ) →L[ℂ] ℂ) := fun z =>
    ∑ i, (ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).smulRight (F i z)
  have hL (t : Fin m → ℂ) (z : ℂ) : L z t = HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w (∑ i, t i • b i)) p z := by
    simp only [L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    symm
    simp only [map_sum, map_smul, HurwitzPrymRR_loc, b4cov_coef,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F]
  have hf : AnalyticAt ℂ (fun tz : (Fin m → ℂ) × ℂ => g (a + tz.1, tz.2)) 0 :=
    hg.comp_of_eq ((analyticAt_const.add analyticAt_fst).prod analyticAt_snd)
      (by simp only [Prod.fst_zero, Prod.snd_zero, add_zero])
  have hl : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t,
      g (a + t, z) = (if p ∈ Set.range y then z else 1) * L z (a + t) := by
    filter_upwards [he] with z hz t
    rw [hL]
    exact (hz (a + t)).symm
  have hκ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (if p ∈ Set.range y then z else 1) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    split_ifs
    · exact hz0
    · exact one_ne_zero
  obtain ⟨q, hq, hdiv⟩ := s2e_corrected_linear_prepared_variation_divisible L a δ
    (fun z => if p ∈ Set.range y then z else 1)
    (fun tz => g (a + tz.1, tz.2)) u c hf hu hu0 hc hδ hprep hl hκ
  refine ⟨q, hq, ?_⟩
  simpa only [hL] using hdiv

/-- A paired parameter variation preserving every local prepared coefficient is scalar.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_paired_prepared_variation_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (b : Fin m → b3_HolForm E C × (Fin r → ℂ))
    (a δ : Fin m → ℂ) (ha : (∑ i, a i • b i) ≠ 0)
    (hcoeff : ∀ p : C, ∃ (d : ℕ) (g u : (Fin m → ℂ) × ℂ → ℂ)
        (c : Fin d → (Fin m → ℂ) → ℂ),
      AnalyticAt ℂ g (a, 0) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ t,
        (if p ∈ Set.range y then z else 1) * HurwitzPrymRR_loc hE
          (s2e_pairedDifferentialLinear hE w (∑ i, t i • b i)) p z = g (t, z)) ∧
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ j, AnalyticAt ℂ (c j) 0) ∧
      (∀ j, fderiv ℂ (c j) 0 δ = 0) ∧
      ((fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
        fun tz => u tz * monicInLast c tz)) :
    ∃ α : ℂ, (∑ i, δ i • b i) = α • (∑ i, a i • b i) := by
  apply s2e_divisible_paired_parameters_proportional hE w x hres _ _ ha
  intro p
  obtain ⟨d, g, u, c, hg, he, hu, hu0, hc, hδ, hprep⟩ := hcoeff p
  exact s2e_paired_prepared_local_divisibility hE w y b a δ p g u c
    hg he hu hu0 hc hδ hprep

end HodgeLean.Foundations.Program
