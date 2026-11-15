import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Finsupp.Weight

/-! # Recovery of summable monomial coefficients -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators NNReal ENNReal
namespace HodgeLean.Foundations.Program

private def monomialTerm (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ) (a : Fin m →₀ ℕ) : ℂ :=
  MvPowerSeries.coeff a F * ∏ i, z i ^ a i

private def lineCoeff (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ) (n : ℕ) : ℂ :=
  ∑' a : {a : Fin m →₀ ℕ // a.degree = n}, monomialTerm m F z a

private lemma monomialTerm_smul (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ) (a : Fin m →₀ ℕ) (t : ℂ) :
    monomialTerm m F (t • z) a = monomialTerm m F z a * t ^ a.degree := by
  simp only [monomialTerm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
  ring

private lemma lineCoeff_summable (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ) (h : Summable (fun a => ‖monomialTerm m F z a‖)) :
    Summable (fun n => ‖lineCoeff m F z n‖) := by
  have hg := (h.hasSum.tsum_fiberwise (fun a : Fin m →₀ ℕ => a.degree)).summable
  apply hg.of_nonneg_of_le (fun n => norm_nonneg _) 
  intro n
  exact norm_tsum_le_tsum_norm (h.subtype _)

private lemma line_hasFPowerSeries (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ) (h : Summable (fun a => ‖monomialTerm m F z a‖)) :
    HasFPowerSeriesAt (fun t : ℂ => s2e_divSeries m F (t • z))
      (FormalMultilinearSeries.ofScalars ℂ (lineCoeff m F z)) 0 := by
  let p := FormalMultilinearSeries.ofScalars ℂ (lineCoeff m F z)
  have hp : (1 : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable_norm (r := (1 : ℝ≥0))
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
      using lineCoeff_summable m F z h
  refine ⟨1, ⟨hp, by norm_num, ?_⟩⟩
  intro t ht
  have ht' : ‖t‖ ≤ 1 := by
    have := (mem_eball_zero_iff.mp ht)
    exact le_of_lt (by simpa only [← ofReal_norm, ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)] using this)
  have hs : Summable (fun a => monomialTerm m F (t • z) a) := by
    apply h.of_norm_bounded
    intro a
    rw [monomialTerm_smul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht')
  have hh := hs.hasSum.tsum_fiberwise (fun a : Fin m →₀ ℕ => a.degree)
  convert hh using 1
  · funext n
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      monomialTerm_smul]
    change lineCoeff m F z n * t ^ n = _
    rw [lineCoeff, ← tsum_mul_right]
    apply tsum_congr
    intro a
    rw [a.property]
  · simp only [zero_add]
    rfl

private lemma monomialTerm_summable (d : ℕ) (r : Fin (d + 1) → ℝ)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a))
    (z : Fin (d + 1) → ℂ) (hz : ∀ i, ‖z i‖ ≤ r i) :
    Summable (fun a => ‖monomialTerm (d + 1) F z a‖) := by
  apply hF.of_nonneg_of_le (fun a => norm_nonneg _)
  intro a
  simp only [monomialTerm, norm_mul, norm_prod, norm_pow, s2e_divWeight]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) _)

private def homogeneousPoly (m : ℕ) (F : MvPowerSeries (Fin m) ℂ) (n : ℕ) :
    MvPolynomial (Fin m) ℂ :=
  ∑ a ∈ (Finsupp.finite_of_degree_eq (σ := Fin m) n).toFinset,
    MvPolynomial.monomial a (MvPowerSeries.coeff a F)

private lemma eval_homogeneousPoly (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (n : ℕ) (z : Fin m → ℂ) :
    MvPolynomial.eval z (homogeneousPoly m F n) = lineCoeff m F z n := by
  let : Fintype {a : Fin m →₀ ℕ // a.degree = n} :=
    (Finsupp.finite_of_degree_eq n).fintype
  simp only [homogeneousPoly, map_sum, MvPolynomial.eval_monomial, Finsupp.prod_pow,
    lineCoeff, tsum_fintype, monomialTerm]
  apply Finset.sum_subtype
  intro a
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

private lemma coeff_homogeneousPoly (m : ℕ) (F : MvPowerSeries (Fin m) ℂ)
    (a : Fin m →₀ ℕ) :
    (homogeneousPoly m F a.degree).coeff a = MvPowerSeries.coeff a F := by
  simp only [homogeneousPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp

/-- Positive polydisc summability and equality of monomial germs determine the series.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B. -/
theorem s2e_monomial_germ_injective
    (d : ℕ) (r s : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (F G : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a))
    (hG : Summable (fun a => ‖MvPowerSeries.coeff a G‖ * s2e_divWeight d s a))
    (hFG : s2e_divSeries (d + 1) F =ᶠ[nhds 0] s2e_divSeries (d + 1) G) : F = G := by
  have heval (z : Fin (d + 1) → ℂ)
      (hz : ∀ i, ‖z i‖ < min (r i) (s i)) :
      lineCoeff (d + 1) F z = lineCoeff (d + 1) G z := by
    have hf := line_hasFPowerSeries (d + 1) F z
      (monomialTerm_summable d r F hF z (fun i => (lt_min_iff.mp (hz i)).1.le))
    have hg := line_hasFPowerSeries (d + 1) G z
      (monomialTerm_summable d s G hG z (fun i => (lt_min_iff.mp (hz i)).2.le))
    have hline : (fun t : ℂ => s2e_divSeries (d + 1) F (t • z)) =ᶠ[nhds 0]
        (fun t : ℂ => s2e_divSeries (d + 1) G (t • z)) := by
      have hc : ContinuousAt (fun t : ℂ => t • z) 0 := by fun_prop
      have ht : Tendsto (fun t : ℂ => t • z) (nhds 0) (nhds 0) := by
        simpa only [zero_smul] using hc.tendsto
      exact ht.eventually hFG
    exact (FormalMultilinearSeries.ofScalars_series_eq_iff ℂ _ _).mp
      (hf.eq_formalMultilinearSeries_of_eventually hg hline)
  have hpoly (n : ℕ) : homogeneousPoly (d + 1) F n = homogeneousPoly (d + 1) G n := by
    apply MvPolynomial.funext_set (fun i => {w : ℂ | ‖w‖ < min (r i) (s i)})
    · intro i
      apply infinite_of_mem_nhds (0 : ℂ)
      have hp : 0 < min (r i) (s i) := lt_min (hr i) (hs i)
      simpa only [Metric.ball, dist_zero_right] using Metric.ball_mem_nhds (0 : ℂ) hp
    · intro z hz
      rw [eval_homogeneousPoly, eval_homogeneousPoly]
      exact congrFun (heval z (fun i => hz i (Set.mem_univ i))) n
  apply MvPowerSeries.ext
  intro a
  have h := congrArg (fun p : MvPolynomial (Fin (d + 1)) ℂ => p.coeff a) (hpoly a.degree)
  simpa only [coeff_homogeneousPoly] using h

end HodgeLean.Foundations.Program
