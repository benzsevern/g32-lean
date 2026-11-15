import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_seriesCoeff (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (j k : ℕ) (s : ℂ) : b63r_bddHol (b63r_annulus n r) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact hn r) (rf4_annulus_subset_closed n r)
    (fun u : ℂ ↦ Ring.choose s k * (-1 : ℂ) ^ k * u ^ j * u ^ (-((n * k : ℕ) : ℤ)))
    (fun u hu ↦ by
      have h := rf4_closedAnnulus_ne_zero hn hr hu
      exact (((differentiableAt_const _).mul (differentiableAt_pow j)).mul
        (differentiableAt_zpow.mpr (Or.inl h))).continuousAt.continuousWithinAt)
    (fun u hu ↦ by
      have h := rf4_closedAnnulus_ne_zero hn hr (rf4_annulus_subset_closed n r hu)
      exact (((differentiableAt_const _).mul (differentiableAt_pow j)).mul
        (differentiableAt_zpow.mpr (Or.inl h))).differentiableWithinAt)

theorem rf4_seriesCoeff_norm (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (j k : ℕ) (s : ℂ) :
    ‖rf4_seriesCoeff n hn r hr j k s‖ ≤
      ‖Ring.choose s k‖ * (max 1 (2 * r)) ^ j * r ^ (-(k : ℤ)) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro u
  change ‖Ring.choose s k * (-1 : ℂ) ^ k * (u : ℂ) ^ j *
    (u : ℂ) ^ (-((n * k : ℕ) : ℤ))‖ ≤ _
  have hu : ‖(u : ℂ)‖ ≤ max 1 (2 * r) := by
    by_cases h : ‖(u : ℂ)‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · have h' : 1 ≤ ‖(u : ℂ)‖ := le_of_not_ge h
      have hp : ‖(u : ℂ)‖ ≤ ‖(u : ℂ)‖ ^ n := by
        simpa using pow_le_pow_right₀ h' hn
      exact (hp.trans u.property.2.le).trans (le_max_right _ _)
  have hk : ‖(u : ℂ) ^ (-((n * k : ℕ) : ℤ))‖ ≤ r ^ (-(k : ℤ)) :=
    (b63r_binomial_multiplier n hn r hr).2 k |>.1 ⟨u, u.property, rfl⟩
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu j)
    (norm_nonneg _)) hk (norm_nonneg _) (by positivity)

theorem rf4_choose_summable (s : ℂ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun k : ℕ ↦ ‖Ring.choose s k‖ * t ^ k) := by
  have hrad : (Real.toNNReal t : ENNReal) < (binomialSeries ℂ s).radius := by
    apply lt_of_lt_of_le _ (binomialSeries_radius_ge_one (𝔸 := ℂ) (a := s))
    exact_mod_cast (show Real.toNNReal t < 1 by simpa using ht1)
  have h := (binomialSeries ℂ s).summable_norm_mul_pow hrad
  simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_norm,
    Real.coe_toNNReal _ ht] using h

theorem rf4_seriesCoeff_summable (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (j : ℕ) (s : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    Summable (fun k : ℕ ↦ ρ ^ k * ‖rf4_seriesCoeff n hn r hr j k s‖) := by
  have h := (rf4_choose_summable s (ρ / r) (by positivity)
    ((div_lt_one hr).mpr hρr)).mul_right ((max 1 (2 * r)) ^ j)
  apply Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) h
  calc
    _ ≤ ρ ^ k * (‖Ring.choose s k‖ * (max 1 (2 * r)) ^ j * r ^ (-(k : ℤ))) :=
      mul_le_mul_of_nonneg_left (rf4_seriesCoeff_norm n hn r hr j k s) (by positivity)
    _ = _ := by rw [zpow_neg, zpow_natCast, div_pow]; ring

theorem rf4_series_sum_eq_multiplier (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (j : Fin n) (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) (ε : ℂ) (hε : ‖ε‖ < ρ) :
    (∑' k, ε ^ k • rf4_seriesCoeff n hn r hr j k (rf4_sectorExp n j)) =
      rf4_multiplier n hn r hr ε (hε.trans hρr) j := by
  have hs := (b63r_powSeries_analytic
    (fun k ↦ rf4_seriesCoeff n hn r hr j k (rf4_sectorExp n j)) ρ hρ
    (rf4_seriesCoeff_summable n hn r hr j (rf4_sectorExp n j) ρ hρ hρr)).1
      ε (by simpa using hε)
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro u
  let ev : b63r_bddHol (b63r_annulus n r) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ u).comp (b63r_bddHol (b63r_annulus n r)).subtypeL
  have hev := ev.hasSum hs.hasSum
  have hb := ((b63r_binomial_multiplier n hn r hr).1
    (rf4_sectorExp n j) ε (hε.trans hρr) u u.property).mul_left ((u : ℂ) ^ (j : ℕ))
  have heq : (fun k ↦ ev (ε ^ k • rf4_seriesCoeff n hn r hr j k (rf4_sectorExp n j))) =
      (fun k ↦ (u : ℂ) ^ (j : ℕ) * (Ring.choose (rf4_sectorExp n j) k * (-ε) ^ k *
        (u : ℂ) ^ (-((n * k : ℕ) : ℤ)))) := by
    funext k
    change ε ^ k * (Ring.choose (rf4_sectorExp n j) k * (-1 : ℂ) ^ k *
      (u : ℂ) ^ (j : ℕ) * (u : ℂ) ^ (-((n * k : ℕ) : ℤ))) = _
    rw [show -ε = (-1 : ℂ) * ε by ring, mul_pow]
    ring
  rw [heq] at hev
  exact hev.unique hb

def rf4_mulOperator {U : Set ℂ} : b63r_bddHol U →L[ℂ]
    (b63r_bddHol U →L[ℂ] b63r_bddHol U) :=
  LinearMap.mkContinuous
    { toFun := b63r_bddHol_mul
      map_add' := by
        intro f g
        ext h u
        change ((f : U →ᵇ ℂ) u + (g : U →ᵇ ℂ) u) * (h : U →ᵇ ℂ) u =
          (f : U →ᵇ ℂ) u * (h : U →ᵇ ℂ) u + (g : U →ᵇ ℂ) u * (h : U →ᵇ ℂ) u
        ring
      map_smul' := by
        intro a f
        ext h u
        change (a * (f : U →ᵇ ℂ) u) * (h : U →ᵇ ℂ) u =
          a * ((f : U →ᵇ ℂ) u * (h : U →ᵇ ℂ) u)
        ring }
    1 (fun f ↦ by
      change ‖b63r_bddHol_mul f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact (b63r_bddHol_mul_spec f).1)

theorem rf4_sectorOp_analytic (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c : ℂ) :
    AnalyticOnNhd ℂ (rf4_sectorOp n hn r hr c) (Metric.ball (0 : ℂ) r) := by
  classical
  intro ε hε
  have hεr : ‖ε‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hε
  obtain ⟨ρ, hερ, hρr⟩ := exists_between hεr
  have hρ : 0 < ρ := (norm_nonneg ε).trans_lt hερ
  let B : Type := b63r_bddHol (b63r_annulus n r)
  let G := Fin n → b63r_bddHol (Metric.ball c (2 * r))
  let L : Fin n → G →L[ℂ] B := fun j ↦
    (b63r_bddHol_comp (fun u : ℂ ↦ c + u ^ n)
      ((differentiable_const c).add (differentiable_pow n)).differentiableOn
      (rf4_powMap_mapsTo n r c)).comp (ContinuousLinearMap.proj j)
  let A : Fin n → B →L[ℂ] (G →L[ℂ] B) := fun j ↦
    (n : ℂ) • (((ContinuousLinearMap.compL ℂ G B B).flip (L j)).comp rf4_mulOperator)
  let T : Fin n → ℂ → B := fun j z ↦
    ∑' k, z ^ k • rf4_seriesCoeff n hn r hr j k (rf4_sectorExp n j)
  have hT : ∀ j, AnalyticAt ℂ (T j) ε := fun j ↦
    (b63r_powSeries_analytic
      (fun k ↦ rf4_seriesCoeff n hn r hr j k (rf4_sectorExp n j)) ρ hρ
      (rf4_seriesCoeff_summable n hn r hr j (rf4_sectorExp n j) ρ hρ hρr)).2
        ε (by simpa only [Metric.mem_ball, dist_zero_right] using hερ)
  have hA : AnalyticAt ℂ (fun z ↦ ∑ j : Fin n, A j (T j z)) ε :=
    Finset.univ.analyticAt_fun_sum (fun j _ ↦ ((A j).analyticAt _).comp (hT j))
  apply hA.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds
    (show ε ∈ Metric.ball (0 : ℂ) ρ by simpa only [Metric.mem_ball, dist_zero_right] using hερ)]
    with z hz
  have hzr : ‖z‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  rw [rf4_sectorOp, dite_eq_left (hzr.trans hρr)]
  apply Finset.sum_congr rfl
  intro j _
  have heq := rf4_series_sum_eq_multiplier n hn r hr j ρ hρ hρr z hzr
  change (n : ℂ) • (b63r_bddHol_mul (T j z)).comp (L j) = _
  rw [show T j z = rf4_multiplier n hn r hr z (hzr.trans hρr) j from heq]

theorem rf4_delta_analytic_core {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O) :
    AnalyticOnNhd ℂ (rf4_delta D) (rf4_polydisc D.m D.r) := by
  intro ε hε
  let F : Fin D.m → Type := fun x ↦ b63r_bddHol (b63r_annulus (D.deg x) D.r)
  let G := fun x : Fin D.m ↦ Fin (D.deg x) → b63r_bddHol (Metric.ball (D.c x) (2 * D.r))
  let P : ∀ x, rf4_Src D →L[ℂ] G x := fun x ↦
    (ContinuousLinearMap.proj x).comp (ContinuousLinearMap.snd ℂ _ _)
  have hx : ∀ x, AnalyticAt ℂ (fun z : Fin D.m → ℂ ↦
      (b63r_bddHol_restrict (D.hann x).ge).comp
          ((rf2_bddForm_coeff D.P (D.ann x)).comp (ContinuousLinearMap.fst ℂ _ _)) -
        (rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (z x)).comp (P x)) ε := by
    intro x
    have hs : AnalyticAt ℂ
        (fun z : Fin D.m → ℂ ↦ rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (z x)) ε :=
      ((rf4_sectorOp_analytic (D.deg x) (D.hdeg x) D.r D.hr (D.c x))
        (ε x) (by simpa only [Metric.mem_ball, dist_zero_right] using hε x)).comp
          (f := fun z : Fin D.m → ℂ ↦ z x)
        ((ContinuousLinearMap.proj x : (Fin D.m → ℂ) →L[ℂ] ℂ).analyticAt ε)
    have hp := (((ContinuousLinearMap.compL ℂ (rf4_Src D) (G x) (F x)).flip (P x)).analyticAt _).comp hs
    exact analyticAt_const.sub hp
  let Q : ((x : Fin D.m) → rf4_Src D →L[ℂ] F x) →L[ℂ]
      (rf4_Src D →L[ℂ] rf4_Tgt D) :=
    (ContinuousLinearMap.piEquivL ℂ (rf4_Src D) F).toContinuousLinearMap
  exact (Q.analyticAt _).comp (AnalyticAt.pi hx)

end HodgeLean.Foundations.Program
