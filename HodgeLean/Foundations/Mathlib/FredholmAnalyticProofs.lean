module

public import HodgeLean.Foundations.Mathlib.FredholmAnalyticDefs
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticKato
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticFrame
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticEval
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticMatrix
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticSchur
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticSeries

/-! # Proof obligations for the Fredholm and bounded holomorphic layer -/

@[expose] public noncomputable section

open Set Filter Topology Module
open scoped BoundedContinuousFunction

namespace HodgeLean.Foundations

theorem b63r_isFredholm_of_finite_aux {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hker : FiniteDimensional ℂ T.ker)
    (hcoker : T.range.CoFG) :
    T.IsFredholm :=
  b63r_kato_isFredholm T hker hcoker

theorem b63r_fredholm_schur_aux {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm) :
    ∃ 𝒰 : Set (E →L[ℂ] F), IsOpen 𝒰 ∧ T₀ ∈ 𝒰 ∧
      ∃ (M : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ]
          (Fin (finrank ℂ (F ⧸ T₀.range)) → ℂ))
        (L : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ] E),
        AnalyticOnNhd ℂ M 𝒰 ∧ AnalyticOnNhd ℂ L 𝒰 ∧ M T₀ = 0 ∧
        ∀ S ∈ 𝒰, Function.Injective (L S) ∧
          (M S).ker.map (L S).toLinearMap = S.ker :=
  b63r_schur_core T₀ hT₀

theorem b63r_analytic_kernel_frame_aux {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {k d : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W) (T : (Fin k → ℂ) → E →L[ℂ] F)
    (hT : AnalyticOnNhd ℂ T W) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) (hF : (T t₀).IsFredholm)
    (hd : ∀ t ∈ W, finrank ℂ ((T t).ker) = d) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ e : Fin d → (Fin k → ℂ) → E, (∀ i, AnalyticOnNhd ℂ (e i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ e i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ e i t) = (T t).ker :=
  b63r_frame_core W hW T hT t₀ ht₀ hF hd

theorem b63r_matrix_kernel_frame_aux {k p q ρ : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin p) (Fin q) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ M t i j) W)
    (hρ : ∀ t ∈ W, (M t).rank = ρ) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ v : Fin (q - ρ) → (Fin k → ℂ) → (Fin q → ℂ), (∀ i, AnalyticOnNhd ℂ (v i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ v i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ v i t) = LinearMap.ker (M t).mulVecLin :=
  b63r_matrix_frame_core W hW M hM hρ t₀ ht₀

open Classical in
theorem b63r_mem_bddHol_iff_aux {U : Set ℂ} (hU : IsOpen U) (f : U →ᵇ ℂ) :
    f ∈ b63r_bddHol U ↔
      DifferentiableOn ℂ (fun z ↦ if h : z ∈ U then f ⟨z, h⟩ else 0) U := by
  refine (fun _ : IsOpen U => ?_) hU
  constructor
  · rintro ⟨g, hg, hf⟩
    exact hg.congr fun z hz => by simp [hz, hf]
  · intro h
    exact ⟨_, h, fun z => by simp [z.2]⟩

theorem b63r_bddHol_limit_aux {U : Set ℂ} (hU : IsOpen U) (F : ℕ → U →ᵇ ℂ)
    (hF : ∀ n, F n ∈ b63r_bddHol U) (f : U →ᵇ ℂ) (hlim : Tendsto F atTop (𝓝 f)) :
    f ∈ b63r_bddHol U := by
  classical
  rw [b63r_mem_bddHol_iff_aux hU]
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop) (F := fun n z ↦
    if h : z ∈ U then F n ⟨z, h⟩ else 0) ?_
    (Eventually.of_forall fun n => (b63r_mem_bddHol_iff_aux hU _).mp (hF n)) hU
  refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with n hn z hz
  simpa [hz] using hn ⟨z, hz⟩

theorem b63r_bddHol_completeSpace_aux {U : Set ℂ} (hU : IsOpen U) :
    CompleteSpace (b63r_bddHol U) := by
  have : IsClosed (b63r_bddHol U : Set (U →ᵇ ℂ)) := by
    refine IsSeqClosed.isClosed fun F f hF hlim => b63r_bddHol_limit_aux hU F hF f hlim
  exact this.completeSpace_coe

theorem b63r_bddHol_restrict_spec_aux {U U' : Set ℂ} (h : U' ⊆ U) :
    ‖b63r_bddHol_restrict h‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_restrict h f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) (inclusion h z) := by
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_, fun _ _ => rfl⟩
  rw [one_mul]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun z =>
    BoundedContinuousFunction.norm_coe_le_norm (f : U →ᵇ ℂ) _

theorem b63r_bddHol_comp_spec_aux {U U' : Set ℂ} (ψ : ℂ → ℂ) (hψ : DifferentiableOn ℂ ψ U')
    (hmaps : MapsTo ψ U' U) :
    ‖b63r_bddHol_comp ψ hψ hmaps‖ ≤ 1 ∧
      ∀ (f : b63r_bddHol U) (z : U'),
        ((b63r_bddHol_comp ψ hψ hmaps f : b63r_bddHol U') : U' →ᵇ ℂ) z =
          (f : U →ᵇ ℂ) ⟨ψ z, hmaps z.2⟩ := by
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_, fun _ _ => rfl⟩
  rw [one_mul]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun z =>
    BoundedContinuousFunction.norm_coe_le_norm (f : U →ᵇ ℂ) _

theorem b63r_bddHol_mul_spec_aux {U : Set ℂ} (m : b63r_bddHol U) :
    ‖b63r_bddHol_mul m‖ ≤ ‖m‖ ∧
      ∀ (f : b63r_bddHol U) (z : U),
        ((b63r_bddHol_mul m f : b63r_bddHol U) : U →ᵇ ℂ) z =
          (m : U →ᵇ ℂ) z * (f : U →ᵇ ℂ) z :=
  ⟨ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f =>
    norm_mul_le (m : U →ᵇ ℂ) (f : U →ᵇ ℂ), fun _ _ => rfl⟩

theorem b63r_mulSeries_analytic_aux {U : Set ℂ} (hU : IsOpen U) (c : ℕ → b63r_bddHol U)
    (ρ : ℝ) (hρ : 0 < ρ) (hc : Summable fun k ↦ ρ ^ k * ‖c k‖) :
    (∀ ε ∈ Metric.ball (0 : ℂ) ρ, Summable fun k ↦ ε ^ k • b63r_bddHol_mul (c k)) ∧
      AnalyticOnNhd ℂ (fun ε : ℂ ↦ ∑' k, ε ^ k • b63r_bddHol_mul (c k))
        (Metric.ball (0 : ℂ) ρ) := by
  have := b63r_bddHol_completeSpace_aux hU
  refine b63r_powSeries_analytic (fun k => b63r_bddHol_mul (c k)) ρ hρ ?_
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hc
  exact mul_le_mul_of_nonneg_left (b63r_bddHol_mul_spec_aux (c k)).1 (by positivity)

theorem b63r_binomial_multiplier_aux (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    (∀ (s ε : ℂ), ‖ε‖ < r → ∀ u ∈ b63r_annulus n r,
      HasSum (fun k : ℕ ↦ Ring.choose s k * (-ε) ^ k * u ^ (-((n * k : ℕ) : ℤ)))
        ((1 - ε * u ^ (-(n : ℤ))) ^ s)) ∧
      ∀ k : ℕ, IsLUB ((fun u : ℂ ↦ ‖u ^ (-((n * k : ℕ) : ℤ))‖) '' b63r_annulus n r)
        (r ^ (-(k : ℤ))) := by
  have hzp : ∀ (u : ℂ) (k : ℕ), u ^ (-((n * k : ℕ) : ℤ)) = (u ^ (-(n : ℤ))) ^ k := by
    intro u k
    rw [← zpow_natCast, ← zpow_mul]
    push_cast
    ring_nf
  have hnorm : ∀ (u : ℂ) (k : ℕ), ‖u ^ (-((n * k : ℕ) : ℤ))‖ = ((‖u‖ ^ n)⁻¹) ^ k := by
    intro u k
    rw [hzp, norm_pow, norm_zpow, zpow_neg, zpow_natCast]
  refine ⟨fun s ε hε u hu => ?_, fun k => ?_⟩
  · have hun : 0 < ‖u‖ ^ n := hr.trans hu.1
    have hx : ‖-ε * u ^ (-(n : ℤ))‖ < 1 := by
      rw [norm_mul, norm_neg, norm_zpow, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
        div_lt_one hun]
      exact hε.trans hu.1
    have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum
      (y := -ε * u ^ (-(n : ℤ))) (by
        rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
        exact ENNReal.ofReal_lt_one.mpr hx)
    have heq : (1 - ε * u ^ (-(n : ℤ))) = 1 + -ε * u ^ (-(n : ℤ)) := by ring
    rw [heq]
    convert h using 1
    · funext k
      simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul, hzp]
      rw [mul_pow]
      ring
    · simp
  · have hupper : ∀ u ∈ b63r_annulus n r, ‖u ^ (-((n * k : ℕ) : ℤ))‖ ≤ r ^ (-(k : ℤ)) := by
      intro u hu
      have := pow_le_pow_left₀ (by positivity) (inv_anti₀ hr hu.1.le) k
      rw [hnorm, zpow_neg, zpow_natCast, ← inv_pow r k]
      exact this
    refine ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact hupper u hu
    · -- points `u = s^(1/n)` with `s ∈ (r, 2r)`
      have hpt : ∀ s ∈ Ioo r (2 * r), (s⁻¹) ^ k ≤ b := by
        intro s hs
        have hs0 : 0 ≤ s := hr.le.trans hs.1.le
        set u : ℂ := ((s ^ (n : ℝ)⁻¹ : ℝ) : ℂ)
        have hu : ‖u‖ ^ n = s := by
          simp only [u, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg (by positivity), Real.rpow_inv_natCast_pow hs0 (by omega)]
        have hmem : u ∈ b63r_annulus n r := by
          simp only [b63r_annulus, mem_ofPred_eq, hu]
          exact hs
        have := hb ⟨u, hmem, rfl⟩
        simp only at this
        rwa [hnorm, hu] at this
      have hlim : Tendsto (fun s : ℝ => (s⁻¹) ^ k) (𝓝[>] r) (𝓝 ((r⁻¹) ^ k)) := by
        have : ContinuousAt (fun s : ℝ => (s⁻¹) ^ k) r :=
          (continuousAt_inv₀ hr.ne').pow k
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[>] r, (s⁻¹) ^ k ≤ b := by
        filter_upwards [Ioo_mem_nhdsGT (by linarith : r < 2 * r)] with s hs
        exact hpt s hs
      have := le_of_tendsto hlim hev
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact this

open Classical in
theorem b63r_eval_analytic_aux {k : ℕ} {U : Set ℂ} (hU : IsOpen U) (W : Set (Fin k → ℂ))
    (hW : IsOpen W) (e : (Fin k → ℂ) → b63r_bddHol U) (he : AnalyticOnNhd ℂ e W) :
    AnalyticOnNhd ℂ
      (fun p : (Fin k → ℂ) × ℂ ↦ if h : p.2 ∈ U then ((e p.1 : b63r_bddHol U) : U →ᵇ ℂ) ⟨p.2, h⟩
        else 0) (W ×ˢ U) :=
  b63r_eval_core hU W hW e he

end HodgeLean.Foundations
