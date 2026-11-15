import HodgeLean.Foundations.Program.PeriodMultiplicationTraceProofs
import HodgeLean.Foundations.Program.PrymVariationFramesParamIntegral
import Mathlib.Analysis.Complex.HasPrimitives

noncomputable section
open Set Filter Topology Manifold Metric
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

attribute [local instance] b3Forms_isManifold_real

theorem b66m_period_integral_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {Φ : W × ℂ → ℂ} {x₀ : W}
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ Φ (x₀, (t : ℂ))) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, Φ (x, (t : ℂ)))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℂ Φ (x₀, (t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ)) x₀ := by
  let c : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcI : ∀ t, c t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hc : ∀ t ∈ uIcc (0 : ℝ) 1, c t = t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simp only [c, min_eq_right ht.2, max_eq_right ht.1]
  let S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc 0 1
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hcS : ∀ t, (c t : ℂ) ∈ S := fun t => ⟨c t, hcI t, rfl⟩
  let O : Set (W × ℂ) := {p | AnalyticAt ℂ Φ p}
  have hO : IsOpen O := isOpen_analyticAt ℂ Φ
  have hKO : ({x₀} ×ˢ S : Set (W × ℂ)) ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, t, ht, rfl⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact hΦ t ht
  obtain ⟨η, hη, hηO⟩ := (isCompact_singleton.prod hS).exists_cthickening_subset_open hO hKO
  let K : Set (W × ℂ) := closedBall x₀ η ×ˢ S
  have hKc : IsCompact K := (isCompact_closedBall x₀ η).prod hS
  have hK : K ⊆ O := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    refine hηO (mem_cthickening_of_dist_le (x, w) (x₀, w) η _ ⟨rfl, hw⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hx
  have hFc : ContinuousOn Φ K := fun p hp => (hK hp).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn (fderiv ℂ Φ) K :=
    fun p hp => (hK hp).fderiv.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF'c
  have hmemK : ∀ x ∈ closedBall x₀ η, ∀ t : ℝ, (x, (c t : ℂ)) ∈ K :=
    fun x hx t => ⟨hx, hcS t⟩
  have hx₀ : x₀ ∈ closedBall x₀ η := mem_closedBall_self hη.le
  have hcont : ∀ x ∈ closedBall x₀ η, Continuous (fun t : ℝ => Φ (x, (c t : ℂ))) :=
    fun x hx => hFc.comp_continuous
      (continuous_const.prodMk (Complex.continuous_ofReal.comp hcc)) (hmemK x hx)
  have hderiv : HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, Φ (x, (c t : ℂ)))
      (∫ t in (0 : ℝ)..1,
        (fderiv ℂ Φ (x₀, (c t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ)) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := MeasureTheory.volume) (F := fun x t => Φ (x, (c t : ℂ)))
      (F' := fun x t => (fderiv ℂ Φ (x, (c t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ))
      (bound := fun _ => C * ‖ContinuousLinearMap.inl ℂ W ℂ‖) (ball_mem_nhds x₀ hη)
      ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₀ hη] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₀ hx₀).intervalIntegrable _ _
    · exact Continuous.aestronglyMeasurable
        ((ContinuousLinearMap.compL ℂ W (W × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ W ℂ)
          |>.continuous.comp (hF'c.comp_continuous
            (continuous_const.prodMk (Complex.continuous_ofReal.comp hcc)) (hmemK x₀ hx₀)))
    · refine Eventually.of_forall fun t _ x hx => ?_
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hC _ (hmemK x (ball_subset_closedBall hx) t)) (norm_nonneg _))
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t _ x hx => ?_
      exact ((hK (hmemK x (ball_subset_closedBall hx) t)).differentiableAt.hasFDerivAt).comp x
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) x (c t : ℂ))
  have hfun : (fun x => ∫ t in (0 : ℝ)..1, Φ (x, (t : ℂ))) =
      (fun x => ∫ t in (0 : ℝ)..1, Φ (x, (c t : ℂ))) := by
    funext x
    exact intervalIntegral.integral_congr (fun t ht => by rw [hc t ht])
  have hlin : (∫ t in (0 : ℝ)..1,
      (fderiv ℂ Φ (x₀, (t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ)) =
      ∫ t in (0 : ℝ)..1,
        (fderiv ℂ Φ (x₀, (c t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ) :=
    intervalIntegral.integral_congr (fun t ht => by rw [hc t ht])
  rw [hfun, hlin]
  exact hderiv

theorem b66m_period_integral_fderiv_apply {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {Φ : W × ℂ → ℂ} {x₀ : W}
    (hΦ : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ Φ (x₀, (t : ℂ))) (h : W) :
    fderiv ℂ (fun x => ∫ t in (0 : ℝ)..1, Φ (x, (t : ℂ))) x₀ h =
      ∫ t in (0 : ℝ)..1, fderiv ℂ Φ (x₀, (t : ℂ)) (h, 0) := by
  rw [(b66m_period_integral_fderiv hΦ).fderiv]
  have hc : ContinuousOn (fun t : ℝ =>
      (fderiv ℂ Φ (x₀, (t : ℂ))).comp (ContinuousLinearMap.inl ℂ W ℂ)) (Icc 0 1) := by
    intro t ht
    have hd : ContinuousAt (fun s : ℝ => fderiv ℂ Φ (x₀, (s : ℂ))) t :=
      (hΦ t ht).fderiv.continuousAt.comp
        (f := fun s : ℝ => (x₀, (s : ℂ)))
        ((continuous_const.prodMk Complex.continuous_ofReal).continuousAt)
    exact (((ContinuousLinearMap.compL ℂ W (W × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ W ℂ)).continuous.continuousAt.comp hd).continuousWithinAt
  exact ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable_of_Icc zero_le_one) h

theorem b66m_finite_period_fderiv {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} (s : Finset ι)
    (Φ : ι → W × ℂ → ℂ) (x₀ : W) (f : W → ℂ)
    (hΦ : ∀ i ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ (Φ i) (x₀, (t : ℂ)))
    (heq : (fun x => ∑ i ∈ s, ∫ t in (0 : ℝ)..1, Φ i (x, (t : ℂ))) =ᶠ[𝓝 x₀] f)
    (h : W) : fderiv ℂ f x₀ h =
      ∑ i ∈ s, ∫ t in (0 : ℝ)..1, fderiv ℂ (Φ i) (x₀, (t : ℂ)) (h, 0) := by
  rw [← heq.fderiv_eq (𝕜 := ℂ), fderiv_fun_sum
    (fun i hi => (b66m_period_integral_fderiv (hΦ i hi)).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => b66m_period_integral_fderiv_apply (hΦ i hi) h)

theorem b66m_retained_cover (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    ∃ (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
      (a : ℤ → b66k_Index R),
      (∀ k, K.φ k = R.atlas.A (a k)) ∧ ∀ k, a (k + K.N) = a k := by
  have hΓ : Continuous (fun τ => ((t, c τ) : b6t_polydisc mr_base × R.C)) :=
    continuous_const.prodMk hc
  have hΓp : Function.Periodic (fun τ => ((t, c τ) : b6t_polydisc mr_base × R.C)) 1 :=
    fun τ => by simp only [hcp τ]
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b63e_exists_chartCover R.atlas.A (fun q => (R.atlas.hA q).1) _ hΓ hΓp
  let K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)) := {
    N := N
    pos := hN
    φ := fun k => R.atlas.A (x k)
    mem_atlas := fun k => (R.atlas.hA _).2
    fp := fun k => R.atlas.hparam _
    ctr := fun k => R.atlas.A (x k) (x k)
    r := r
    φ_add := fun k => by simp only [hx]
    ctr_add := fun k => by simp only [hx]
    r_add := hr
    ball_sub := hball
    mem := hmem
    fib := fun _ => rfl
    per := hΓp
    cont := hΓ }
  exact ⟨K, x, (fun _ => rfl), hx⟩

open scoped ContDiff in
set_option maxHeartbeats 400000 in
theorem b66m_moving_period_integrals (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (u₀ : V)
    (hu₀ : u₀.val ∈ U) {c : ℝ → C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover b C u₀.val
      (fun τ ↦ ((⟨u₀.val, hV u₀.property⟩ : b6t_polydisc b), c τ))) :
    ∃ (A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ),
      (∀ k, AnalyticOn ℂ (A k) ((K.φ k).target ∩ Prod.fst ⁻¹' (V ∩ U)) ∧
        ∀ (t : V) (x : b63l_parameterFibre b C V hV t), t.val ∈ U →
          x.val ∈ (K.φ k).source → ∀ w : TangentSpace 𝓘(ℂ, ℂ) x,
          θ.val t ⟨x, w⟩ = A k (K.φ k x.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun y : b63l_parameterFibre b C V hV t ↦ (K.φ k y.val).2) x w)) ∧
      (∀ k, AnalyticAt ℂ (K.bb k) u₀.val) ∧
      (∀ k, ∀ s ∈ Icc (0 : ℝ) 1,
        AnalyticAt ℂ (fun p : (Fin 10 → ℂ) × ℂ ↦
          A k (p.1, K.a k + p.2 * (K.bb k p.1 - K.a k)) * (K.bb k p.1 - K.a k))
          (u₀.val, (s : ℂ))) ∧
      (fun u ↦ ∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
        A k (u, K.a k + (s : ℂ) * (K.bb k u - K.a k)) * (K.bb k u - K.a k))
        =ᶠ[𝓝 u₀.val] (fun u ↦ if h : u ∈ V then
          (P ⟨u, h⟩ (b63e_fibreLoopClass b C ⟨u, hV h⟩ hc hcp)).val
            (b63e_relFormAt b C V hV θ ⟨u, h⟩) else 0) := by
  classical
  choose A hAan hAid using fun k ↦ θ.property.2 (K.φ k) (K.mem_atlas k) (K.fp k)
  set I : ℤ → (Fin 10 → ℂ) → ℂ := fun k u ↦ ∫ s in (0 : ℝ)..1,
    A k (u, K.a k + (s : ℂ) * (K.bb k u - K.a k)) * (K.bb k u - K.a k)
  have hAat : ∀ k, ∀ p ∈ (K.φ k).target, p.1 ∈ V → p.1 ∈ U → AnalyticAt ℂ (A k) p :=
    fun k p hp hpV hpU ↦ (hAan k).analyticAt
      (((K.φ k).open_target.inter ((hVo.inter hU).preimage continuous_fst)).mem_nhds
        ⟨hp, hpV, hpU⟩)
  have hbb : ∀ k, AnalyticAt ℂ (K.bb k) u₀.val := by
    intro k
    have h1 := K.cond_u₀ (k + 1)
    have h0 := K.cond_u₀ k
    have hm1 : ContMDiffAt 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
        (fun u : Fin 10 → ℂ ↦ (u, K.a (k + 1))) u₀.val :=
      (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
    have hm2 : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
        (K.φ (k + 1)).symm (u₀.val, K.a (k + 1)) :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (K.mem_atlas (k + 1))) (K.ball_sub _ h1.1)
    have hm3 : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
        (K.φ k) (K.v (k + 1) u₀.val) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (K.mem_atlas k)) h0.2.1
    have hm := hm3.comp u₀.val (hm2.comp u₀.val hm1)
    have ha : AnalyticAt ℂ (fun u ↦ K.φ k (K.v (k + 1) u)) u₀.val :=
      (contMDiffAt_iff_contDiffAt.1 hm).analyticAt
    exact analyticAt_snd.comp ha
  refine ⟨A, (fun k => ⟨hAan k, hAid k⟩), hbb, ?_, ?_⟩
  · intro k s hs
    have hpt := K.ball_sub k (K.segment_mem K.cond_u₀ k hs)
    have hA' := hAat k _ hpt u₀.property hu₀
    have hb : AnalyticAt ℂ (fun p : (Fin 10 → ℂ) × ℂ ↦ K.bb k p.1 - K.a k)
        (u₀.val, (s : ℂ)) := by
      have hb0 : AnalyticAt ℂ (fun p : (Fin 10 → ℂ) × ℂ => K.bb k p.1)
          (u₀.val, (s : ℂ)) :=
        AnalyticAt.comp (g := K.bb k) (f := fun p : (Fin 10 → ℂ) × ℂ => p.1)
          (x := (u₀.val, (s : ℂ))) (hbb k) analyticAt_fst
      exact hb0.sub analyticAt_const
    have hg : AnalyticAt ℂ (fun p : (Fin 10 → ℂ) × ℂ ↦
        (p.1, K.a k + p.2 * (K.bb k p.1 - K.a k))) (u₀.val, (s : ℂ)) :=
      analyticAt_fst.prod (analyticAt_const.add (analyticAt_snd.mul hb))
    exact (AnalyticAt.comp (g := A k)
      (f := fun p : (Fin 10 → ℂ) × ℂ =>
        (p.1, K.a k + p.2 * (K.bb k p.1 - K.a k)))
      (x := (u₀.val, (s : ℂ))) hA' hg).mul hb
  · have hnhds : ∀ᶠ u in 𝓝 u₀.val, (∀ k, K.cond u k) ∧ u ∈ V ∧ u ∈ U :=
      K.cond_nhds.and (Filter.Eventually.and (hVo.mem_nhds u₀.property) (hU.mem_nhds hu₀))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnhds
    filter_upwards [Metric.ball_mem_nhds _ hε] with u hu
    obtain ⟨hcond, huV, huU⟩ := hball u hu
    have hS : ∀ l : unitInterval, ∀ k, K.cond (u₀.val + (l : ℝ) • (u - u₀.val)) k := fun l ↦
      (hball _ ((convex_ball u₀.val ε).add_smul_sub_mem (mem_ball_self hε) hu l.2)).1
    set t : V := ⟨u, huV⟩
    set δ := K.loopF V hV t (hincl t) hcond
    have hhom : Continuous fun p : unitInterval × ℝ ↦ (K.hom p).2 :=
      continuous_snd.comp K.continuous_hom
    have hhomp : ∀ l, Function.Periodic (fun τ ↦ (K.hom (l, τ)).2) 1 := fun l τ ↦ by
      simp only [K.hom_periodic l τ]
    have hpar : Continuous fun p : unitInterval × ℝ ↦
        (K.floorLoop (u₀.val + (p.1 : ℝ) • (u - u₀.val)) ((K.N : ℝ) * p.2)).2 :=
      continuous_snd.comp (K.continuous_param hS)
    have hparp : ∀ l : unitInterval, Function.Periodic (fun τ ↦
        (K.floorLoop (u₀.val + (l : ℝ) • (u - u₀.val)) ((K.N : ℝ) * τ)).2) 1 := fun l τ ↦ by
      simp only [K.floorLoop_periodic _ τ]
    have hd : Continuous fun τ ↦ (K.floorLoop u₀.val ((K.N : ℝ) * τ)).2 :=
      (hpar.comp ((continuous_const : Continuous fun _ : ℝ ↦ (0 : unitInterval)).prodMk
        continuous_id)).congr fun τ ↦ by
        simp only [Function.comp_apply, Set.Icc.coe_zero, zero_smul, add_zero, id]
    have hdp : Function.Periodic (fun τ ↦ (K.floorLoop u₀.val ((K.N : ℝ) * τ)).2) 1 := fun τ ↦ by
      simp only [K.floorLoop_periodic _ τ]
    have hclass : (b63e_fibreLoopClass b C ⟨u, hV huV⟩ hc hcp :
        b6m_H1 (b63l_parameterFibre b C V hV t)) = b6m_loopClass _ δ := by
      rw [b63e_loopClass_eq_fibreLoopClass_param b C V hV t δ]
      refine (b63e_fibreLoopClass_homotopy' b C _ _ hhom hhomp hc hcp hd hdp
        (fun τ ↦ by rw [K.hom_zero]) (fun τ ↦ by rw [K.hom_one])).trans ?_
      refine b63e_fibreLoopClass_homotopy' b C _ _ hpar hparp hd hdp _ _
        (fun τ ↦ by simp only [Set.Icc.coe_zero, zero_smul, add_zero]) (fun τ ↦ ?_)
      show (K.floorLoop (u₀.val + ((1 : unitInterval) : ℝ) • (u - u₀.val)) ((K.N : ℝ) * τ)).2 =
        ((δ.1 τ).val).2
      simp only [Set.Icc.coe_one, one_smul, add_sub_cancel]
      exact congrArg Prod.snd (K.loopF_val V hV t (hincl t) hcond τ).symm
    show (∑ k ∈ Finset.range K.N, I k u) = dite (u ∈ V) _ _
    rw [dite_eq_left_of_eq_true (eq_true huV)]
    change _ = (P t (b63e_fibreLoopClass b C ⟨u, hV huV⟩ hc hcp)).val
      (b63e_relFormAt b C V hV θ t)
    rw [hclass, hP t]
    change _ = b3_pathIntegral ℂ _ δ.1 (θ.val t)
    rw [K.loopF_pathIntegral V hV t (hincl t) hcond (θ.property.1 t) A
      (fun k x hx v ↦ hAid k t x huU hx v)]
    intro k s hs
    exact (hAat k _ (K.ball_sub k (K.segment_mem hcond k hs)) huV huU).continuousAt

theorem b66m_endpoint_cocycle (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {c : ℝ → R.C} (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (k : ℤ) (h : Fin 10 → ℂ) :
    fderiv ℂ (K.bb k) t.val h =
      b66k_cocycle R t h (a (k + 1)) (a k) (K.v (k + 1) t.val).2 := by
  let x := (K.v (k + 1) t.val).2
  have hp : (t, x) = K.v (k + 1) t.val := by
    dsimp only [x]
    rw [K.v_u₀]
  have ht := K.ball_sub (k + 1) (K.cond_u₀ (k + 1)).1
  have ha : (t, x) ∈ (R.atlas.A (a (k + 1))).source := by
    rw [hp, ← hφ (k + 1)]
    exact (K.φ (k + 1)).map_target ht
  have hb : (t, x) ∈ (R.atlas.A (a k)).source := by
    rw [hp, ← hφ k]
    exact (K.cond_u₀ k).2.1
  have hcoord : R.atlas.A (a (k + 1)) (t, x) = (t.val, K.a (k + 1)) := by
    rw [hp, ← hφ (k + 1)]
    exact (K.φ (k + 1)).right_inv ht
  have htrans : (t.val, K.a (k + 1)) ∈
      ((R.atlas.A (a (k + 1))).symm.trans (R.atlas.A (a k))).source := by
    rw [← hcoord]
    refine ⟨(R.atlas.A (a (k + 1))).map_source ha, ?_⟩
    change (R.atlas.A (a (k + 1))).symm
      (R.atlas.A (a (k + 1)) (t, x)) ∈ (R.atlas.A (a k)).source
    rwa [(R.atlas.A (a (k + 1))).left_inv ha]
  have hd := ((b66k_transition_analytic R _ _ _ htrans).differentiableAt.hasFDerivAt).comp
    t.val (hasFDerivAt_prodMk_left (𝕜 := ℂ) t.val (K.a (k + 1)))
  have hfun : K.bb k = (b66k_transition R (a (k + 1)) (a k)) ∘
      (fun u : Fin 10 → ℂ => (u, K.a (k + 1))) := by
    funext u
    simp only [b63e_Cover.bb, b63e_Cover.v, b66k_transition, Function.comp_apply, hφ]
  rw [hfun, hd.fderiv]
  change fderiv ℂ (b66k_transition R (a (k + 1)) (a k))
    (t.val, K.a (k + 1)) (h, 0) = b66k_cocycle R t h (a (k + 1)) (a k) x
  simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, x) ∈ (R.atlas.A (a (k + 1))).source ∩
      (R.atlas.A (a k)).source from ⟨ha, hb⟩), hcoord]

theorem b66m_segment_integrand_fderiv {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {A : W × ℂ → ℂ} {b : W → ℂ} {u : W} (a s : ℂ)
    (hA : DifferentiableAt ℂ A (u, a + s * (b u - a)))
    (hb : DifferentiableAt ℂ b u) (h : W) :
    fderiv ℂ (fun p : W × ℂ =>
      A (p.1, a + p.2 * (b p.1 - a)) * (b p.1 - a)) (u, s) (h, 0) =
      fderiv ℂ A (u, a + s * (b u - a)) (h, 0) * (b u - a) +
        (s * fderiv ℂ A (u, a + s * (b u - a)) (0, b u - a) +
          A (u, a + s * (b u - a))) * fderiv ℂ b u h := by
  have hfst : HasFDerivAt (Prod.fst : W × ℂ → W)
      (ContinuousLinearMap.fst ℂ W ℂ) (u, s) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : W × ℂ → ℂ)
      (ContinuousLinearMap.snd ℂ W ℂ) (u, s) := hasFDerivAt_snd
  have hg := (hb.hasFDerivAt.comp (u, s) hfst).sub_const a
  have hw := (hsnd.mul hg).const_add a
  have hp := hfst.prodMk hw
  have hf := (hA.hasFDerivAt.comp (u, s) hp).mul hg
  change HasFDerivAt (fun p : W × ℂ =>
    A (p.1, a + p.2 * (b p.1 - a)) * (b p.1 - a)) _ (u, s) at hf
  rw [hf.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
    Function.comp_apply, Pi.mul_apply, smul_eq_mul,
    mul_zero, add_zero]
  let L := fderiv ℂ A (u, a + s * (b u - a))
  have hs : (h, s * fderiv ℂ b u h) =
      (h, (0 : ℂ)) + (s * fderiv ℂ b u h) • ((0 : W), (1 : ℂ)) := by simp
  have hv : L (0, b u - a) = (b u - a) * L (0, 1) := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one] using
      L.map_smul (b u - a) ((0 : W), (1 : ℂ))
  change A (u, a + s * (b u - a)) * fderiv ℂ b u h +
    (b u - a) * L (h, s * fderiv ℂ b u h) =
      L (h, 0) * (b u - a) +
        (s * L (0, b u - a) + A (u, a + s * (b u - a))) * fderiv ℂ b u h
  rw [hs, map_add, map_smul, smul_eq_mul, hv]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem b66m_segment_endpoint_integral {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (A : W × ℂ → ℂ) (u : W) (a b : ℂ)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ A (u, a + (s : ℂ) * (b - a))) :
    (∫ s in (0 : ℝ)..1,
      (s : ℂ) * fderiv ℂ A (u, a + (s : ℂ) * (b - a)) (0, b - a) +
        A (u, a + (s : ℂ) * (b - a))) = A (u, b) := by
  have hp : Continuous (fun s : ℝ => (u, a + (s : ℂ) * (b - a))) := by fun_prop
  have hc : ContinuousOn (fun s : ℝ =>
      (s : ℂ) * fderiv ℂ A (u, a + (s : ℂ) * (b - a)) (0, b - a) +
        A (u, a + (s : ℂ) * (b - a))) (Icc 0 1) := by
    intro s hs
    have hd : ContinuousAt (fun t : ℝ =>
        fderiv ℂ A (u, a + (t : ℂ) * (b - a))) s :=
      (hA s hs).fderiv.continuousAt.comp (f := fun t : ℝ =>
        (u, a + (t : ℂ) * (b - a))) hp.continuousAt
    have hv : ContinuousAt (fun t : ℝ => A (u, a + (t : ℂ) * (b - a))) s :=
      (hA s hs).continuousAt.comp (f := fun t : ℝ =>
        (u, a + (t : ℂ) * (b - a))) hp.continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.mul
      (hd.clm_apply continuousAt_const)).add hv).continuousWithinAt
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (t : ℂ) * A (u, a + (t : ℂ) * (b - a)))
        ((s : ℂ) * fderiv ℂ A (u, a + (s : ℂ) * (b - a)) (0, b - a) +
          A (u, a + (s : ℂ) * (b - a))) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hl : HasDerivAt (fun z : ℂ => (u, a + z * (b - a))) (0, b - a) (s : ℂ) := by
      simpa using (hasDerivAt_const (s : ℂ) u).prodMk
        (((hasDerivAt_id (s : ℂ)).mul_const (b - a)).const_add a)
    have hh := ((hasDerivAt_id (s : ℂ)).mul
      ((hA s hs).differentiableAt.hasFDerivAt.comp_hasDerivAt (s : ℂ) hl)).comp_ofReal
    simpa only [Function.comp_apply, Pi.mul_apply, id_eq, one_mul, add_comm] using hh
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa using he

theorem b66m_segment_period_fderiv {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] (A : W × ℂ → ℂ) (b : W → ℂ)
    (u : W) (a : ℂ) (hb : AnalyticAt ℂ b u)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ A (u, a + (s : ℂ) * (b u - a)))
    (h : W) :
    fderiv ℂ (fun x => ∫ s in (0 : ℝ)..1,
      A (x, a + (s : ℂ) * (b x - a)) * (b x - a)) u h =
      (∫ s in (0 : ℝ)..1,
        fderiv ℂ A (u, a + (s : ℂ) * (b u - a)) (h, 0) * (b u - a)) +
          A (u, b u) * fderiv ℂ b u h := by
  let Φ : W × ℂ → ℂ := fun p => A (p.1, a + p.2 * (b p.1 - a)) * (b p.1 - a)
  have hΦ : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ Φ (u, (s : ℂ)) := by
    intro s hs
    have hl : AnalyticAt ℂ (fun p : W × ℂ => b p.1 - a) (u, (s : ℂ)) :=
      (AnalyticAt.comp (g := b) (f := fun p : W × ℂ => p.1)
        (x := (u, (s : ℂ))) hb analyticAt_fst).sub analyticAt_const
    have hg : AnalyticAt ℂ (fun p : W × ℂ => (p.1, a + p.2 * (b p.1 - a)))
        (u, (s : ℂ)) := analyticAt_fst.prod (analyticAt_const.add (analyticAt_snd.mul hl))
    exact (AnalyticAt.comp (g := A)
      (f := fun p : W × ℂ => (p.1, a + p.2 * (b p.1 - a)))
      (x := (u, (s : ℂ))) (hA s hs) hg).mul hl
  have he := b66m_period_integral_fderiv_apply hΦ h
  change _ = _ at he
  rw [he]
  have hp : Continuous (fun s : ℝ => (u, a + (s : ℂ) * (b u - a))) := by fun_prop
  have hD : ContinuousOn (fun s : ℝ => fderiv ℂ A (u, a + (s : ℂ) * (b u - a)))
      (Icc 0 1) := fun s hs => ((hA s hs).fderiv.continuousAt.comp
        (f := fun s : ℝ => (u, a + (s : ℂ) * (b u - a))) hp.continuousAt).continuousWithinAt
  have hF : ContinuousOn (fun s : ℝ => A (u, a + (s : ℂ) * (b u - a)))
      (Icc 0 1) := fun s hs => ((hA s hs).continuousAt.comp
        (f := fun s : ℝ => (u, a + (s : ℂ) * (b u - a))) hp.continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun s : ℝ =>
      fderiv ℂ A (u, a + (s : ℂ) * (b u - a)) (h, 0) * (b u - a))
      MeasureTheory.volume 0 1 := ((hD.clm_apply continuousOn_const).mul continuousOn_const).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hj : IntervalIntegrable (fun s : ℝ =>
      ((s : ℂ) * fderiv ℂ A (u, a + (s : ℂ) * (b u - a)) (0, b u - a) +
        A (u, a + (s : ℂ) * (b u - a))) * fderiv ℂ b u h)
      MeasureTheory.volume 0 1 := (((Complex.continuous_ofReal.continuousOn.mul
    (hD.clm_apply continuousOn_const)).add hF).mul continuousOn_const).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  rw [intervalIntegral.integral_congr (fun s hs =>
    b66m_segment_integrand_fderiv a (s : ℂ)
      (hA s (by rwa [uIcc_of_le zero_le_one] at hs)).differentiableAt hb.differentiableAt h)]
  rw [intervalIntegral.integral_add hi hj]
  simp_rw [intervalIntegral.integral_mul_const]
  rw [b66m_segment_endpoint_integral A u a (b u) hA]


theorem b66m_polygon_period_fderiv {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} (S : Finset ι)
    (A : ι → W × ℂ → ℂ) (b : ι → W → ℂ) (a : ι → ℂ)
    (u : W) (f : W → ℂ)
    (hb : ∀ k ∈ S, AnalyticAt ℂ (b k) u)
    (hA : ∀ k ∈ S, ∀ s ∈ Icc (0 : ℝ) 1,
      AnalyticAt ℂ (A k) (u, a k + (s : ℂ) * (b k u - a k)))
    (heq : (fun x => ∑ k ∈ S, ∫ s in (0 : ℝ)..1,
      A k (x, a k + (s : ℂ) * (b k x - a k)) * (b k x - a k)) =ᶠ[𝓝 u] f)
    (h : W) :
    fderiv ℂ f u h =
      (∑ k ∈ S, ∫ s in (0 : ℝ)..1,
        fderiv ℂ (A k) (u, a k + (s : ℂ) * (b k u - a k)) (h, 0) *
          (b k u - a k)) +
      ∑ k ∈ S, A k (u, b k u) * fderiv ℂ (b k) u h := by
  have hd : ∀ k ∈ S, DifferentiableAt ℂ (fun x => ∫ s in (0 : ℝ)..1,
      A k (x, a k + (s : ℂ) * (b k x - a k)) * (b k x - a k)) u := by
    intro k hk
    have hΦ : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ
        (fun p : W × ℂ => A k (p.1, a k + p.2 * (b k p.1 - a k)) *
          (b k p.1 - a k)) (u, (s : ℂ)) := by
      intro s hs
      have hl : AnalyticAt ℂ (fun p : W × ℂ => b k p.1 - a k) (u, (s : ℂ)) :=
        (AnalyticAt.comp (g := b k) (f := fun p : W × ℂ => p.1)
          (x := (u, (s : ℂ))) (hb k hk) analyticAt_fst).sub analyticAt_const
      exact (AnalyticAt.comp (g := A k)
        (f := fun p : W × ℂ => (p.1, a k + p.2 * (b k p.1 - a k)))
        (x := (u, (s : ℂ))) (hA k hk s hs)
        (analyticAt_fst.prod (analyticAt_const.add (analyticAt_snd.mul hl)))).mul hl
    exact (b66m_period_integral_fderiv hΦ).differentiableAt
  rw [← heq.fderiv_eq (𝕜 := ℂ), fderiv_fun_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k hk =>
    b66m_segment_period_fderiv (A k) (b k) u (a k) (hb k hk) (hA k hk) h)


theorem b66m_endpoint_contraction (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {c : ℝ → R.C} (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ)
    (θ : b3_HolForm ℂ (rf8_fibre R.C t)) (q : b66g_Coeff R)
    (hA : ∀ k (p : rf8_fibre R.C t), p.val ∈ (K.φ k).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = A k (K.φ k p.val) * b66m_sc_sliceD R t (a k) p w)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (k : ℤ) (h : Fin 10 → ℂ) :
    A k (t.val, K.bb k t.val) * fderiv ℂ (K.bb k) t.val h =
      b66g_contract R q (b66k_cocycle R t h) (a (k + 1)) (a k)
        (K.v (k + 1) t.val).2 := by
  let p := b66m_sc_pt R t (K.v (k + 1) t.val).2
  have hp : p.val = K.v (k + 1) t.val := by
    apply Prod.ext
    · rw [K.v_u₀]
      rfl
    · rfl
  have hpk : p.val ∈ (K.φ k).source := by
    rw [hp]
    exact (K.cond_u₀ k).2.1
  have hpa : p.val ∈ (R.atlas.A (a k)).source := by rwa [← hφ k]
  have hcoord : K.φ k p.val = (t.val, K.bb k t.val) := by
    apply Prod.ext
    · rw [K.fp k _ hpk]
      rfl
    · rw [hp]
      rfl
  have hn : b66m_sc_sliceD R t (a k) p 1 ≠ 0 := by
    intro hz
    apply (b66g_slice_coordinate R t (a k)).2 p hpa
    ext1
    exact hz
  have heq := (hA k p hpk 1).symm.trans (hq (a k) p hpa 1)
  rw [hcoord] at heq
  have heq' := mul_right_cancel₀ hn heq
  rw [heq', b66m_endpoint_cocycle R t K a hφ k h]
  rfl


theorem b66m_retained_period_derivative (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) :
    ∃ A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ,
      (∀ k, AnalyticOn ℂ (A k)
        ((K.φ k).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) ∧
        ∀ (u : b6t_polydisc mr_base) (p : rf8_fibre R.C u), u.val ∈ U →
          p.val ∈ (K.φ k).source → ∀ w : ℂ,
          θ.val u ⟨p, w⟩ = A k (K.φ k p.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun y : rf8_fibre R.C u => (K.φ k y.val).2) p w)) ∧
      ∀ h : Fin 10 → ℂ,
        fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc mr_base then
          (R.P ⟨u, hu⟩ (b63e_fibreLoopClass mr_base R.C ⟨u, hu⟩ hc hcp)).val
            (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
              θ ⟨u, hu⟩) else 0) t.val h =
        (∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
          fderiv ℂ (A k) (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k))
            (h, 0) * (K.bb k t.val - K.a k)) +
        ∑ k ∈ Finset.range K.N,
          b66g_contract R q (b66k_cocycle R t h) (a (k + 1)) (a k)
            (K.v (k + 1) t.val).2 := by
  obtain ⟨A, hA, hb, _, heq⟩ := b66m_moving_period_integrals mr_base R.C
    (b6t_polydisc mr_base) (Subset.refl _) (rf5_polydisc_isOpen mr_base)
    R.hincl R.P R.hP U hU θ t ht hc hcp K
  refine ⟨A, hA, fun h => ?_⟩
  have hd := b66m_polygon_period_fderiv (Finset.range K.N)
    (fun k : ℕ => A k) (fun k : ℕ => K.bb k) (fun k : ℕ => K.a k) t.val _
    (fun k _ => hb k) (fun k _ => ?_) heq h
  · rw [hd]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    apply b66m_endpoint_contraction R t K a hφ A (b63e_relFormAt mr_base R.C
      (b6t_polydisc mr_base) (Subset.refl _) θ t) q
    · intro j p hp w
      have he := (hA j).2 t p ht hp w
      have hf : (fun y : rf8_fibre R.C t => (K.φ j y.val).2) =
          b66m_sc_slice R t (a j) := by
        funext y
        rw [hφ j]
        rfl
      change θ.val t ⟨p, w⟩ = _
      rw [hf] at he
      exact he
    · exact hq
  · intro s hs
    have hp := K.ball_sub k (K.segment_mem K.cond_u₀ k hs)
    exact (hA k).1.analyticAt
      (((K.φ k).open_target.inter
        (((rf5_polydisc_isOpen mr_base).inter hU).preimage continuous_fst)).mem_nhds
        ⟨hp, t.property, ht⟩)


theorem b66m_flat_loop_period (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) R.P θ s
      (b63e_fibreLoopClass mr_base R.C s hc hcp) =
      fun u => if hu : u ∈ b6t_polydisc mr_base then
        (R.P ⟨u, hu⟩ (b63e_fibreLoopClass mr_base R.C ⟨u, hu⟩ hc hcp)).val
          (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
            θ ⟨u, hu⟩) else 0 := by
  funext u
  unfold b63e_periodFunction
  split_ifs with hu
  · rw [b63e_fibreLoopClass_transport]
  · rfl


theorem b66m_sc_tau_derivative_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t)
    (a b : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source)
    (w : ℂ) :
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66m_sc_tau R t ρ u a) p) w -
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66m_sc_tau R t ρ u b) p) w =
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (fun y : rf8_fibre R.C t => u a b y.val.2) p) w := by
  have heq : b66m_sc_tau R t ρ u a - b66m_sc_tau R t ρ u b =ᶠ[𝓝 p]
      (fun y : rf8_fibre R.C t => u a b y.val.2) := by
    filter_upwards [(b66m_sc_open_source R t a).mem_nhds ha,
      (b66m_sc_open_source R t b).mem_nhds hb] with y hya hyb
    exact b66m_sc_tau_sub R t ρ hρ hu a b y hya hyb
  have hda := (b66m_sc_tau_smooth R t ρ hρ hu a p ha).mdifferentiableAt (by simp)
  have hdb := (b66m_sc_tau_smooth R t ρ hρ hu b p hb).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
  rw [mfderiv_sub hda hdb] at hd
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L w) hd


def b66m_correctedLocalForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (u : b66k_Cochain R)
    (β : b66k_Index R → TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ :=
  fun p => β p.1.val p -
    (show ℂ →L[ℝ] ℂ from
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66m_sc_tau R t ρ u p.1.val) p.1) p.2


theorem b66m_correctedLocalForm_local (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t)
    (β : b66k_Index R → TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hβ : ∀ a b (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      β a ⟨p, w⟩ - β b ⟨p, w⟩ =
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          (fun y : rf8_fibre R.C t => u a b y.val.2) p) w)
    (a : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66m_correctedLocalForm R t ρ u β ⟨p, w⟩ = β a ⟨p, w⟩ -
      (show ℂ →L[ℝ] ℂ from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66m_sc_tau R t ρ u a) p) w := by
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hd := b66m_sc_tau_derivative_sub R t ρ hρ u hu a p.val p ha hb w
  have hl := hβ a p.val p ha hb w
  dsimp only [b66m_correctedLocalForm]
  linear_combination hd - hl


theorem b66m_correctedLocalForm_antilinear (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (u : b66k_Cochain R)
    (β : b66k_Index R → TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hβ : ∀ a (p : rf8_fibre R.C t) (w : ℂ),
      β a ⟨p, Complex.I • w⟩ = Complex.I * β a ⟨p, w⟩)
    (p : rf8_fibre R.C t) (w : ℂ) :
    (b66m_correctedLocalForm R t ρ u β ⟨p, w⟩ + Complex.I *
      b66m_correctedLocalForm R t ρ u β ⟨p, Complex.I • w⟩) / 2 =
      -b66m_sc_gamma R t ρ u ⟨p, w⟩ := by
  simp only [b66m_correctedLocalForm, b66m_sc_gamma, b4c_dbar, hβ]
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul, smul_eq_mul]
  ring_nf
  congr 3

section B66mRelCoef

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

/-- The coefficient of a relative form in a retained chart. -/
theorem b66m_relCoef_exists
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R) :
    ∃ α : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ α ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) ∧
      ∀ (u : b6t_polydisc mr_base) (x : rf8_fibre R.C u), u.val ∈ U →
        x.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
          θ.val u ⟨x, v⟩ = α (u.val, b66m_sc_slice R u a x) * b66m_sc_sliceD R u a x v := by
  obtain ⟨α, hα, hθ⟩ := θ.property.2 (R.atlas.A a) (R.atlas.hA a).2 (R.atlas.hparam a)
  refine ⟨α, hα, fun u x hu hx v => ?_⟩
  rw [hθ u x hu hx v, b66m_sc_slice_value R u a x hx]
  rfl

/-- The chosen coefficient of a relative form in a retained chart. -/
def b66m_relCoef (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (a : b66k_Index R) : (Fin 10 → ℂ) × ℂ → ℂ :=
  (b66m_relCoef_exists R θ a).choose

theorem b66m_relCoef_open (hU : IsOpen U) (a : b66k_Index R) :
    IsOpen ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) :=
  (R.atlas.A a).open_target.inter (((rf5_polydisc_isOpen mr_base).inter hU).preimage continuous_fst)

theorem b66m_relCoef_analytic (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R) :
    AnalyticOnNhd ℂ (b66m_relCoef R θ a)
      ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) :=
  ((b66m_relCoef_open R hU a).analyticOn_iff_analyticOnNhd).1
    (b66m_relCoef_exists R θ a).choose_spec.1

theorem b66m_relCoef_spec
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R)
    (u : b6t_polydisc mr_base) (x : rf8_fibre R.C u) (hu : u.val ∈ U)
    (hx : x.val ∈ (R.atlas.A a).source) (v : ℂ) :
    θ.val u ⟨x, v⟩ = b66m_relCoef R θ a (u.val, b66m_sc_slice R u a x) * b66m_sc_sliceD R u a x v :=
  (b66m_relCoef_exists R θ a).choose_spec.2 u x hu hx v

theorem b66m_sliceD_one_ne (t : b6t_polydisc mr_base) (a : b66k_Index R) (x : rf8_fibre R.C t)
    (hx : x.val ∈ (R.atlas.A a).source) : b66m_sc_sliceD R t a x 1 ≠ 0 := by
  intro h
  apply (b66g_slice_coordinate R t a).2 x hx
  ext1
  change b66m_sc_sliceD R t a x 1 = 0
  exact h

/-- At the base fibre the chart coefficient of `θ` is the coefficient of the given form. -/
theorem b66m_relCoef_base {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    (a : b66k_Index R) (x : rf8_fibre R.C t) (hx : x.val ∈ (R.atlas.A a).source) :
    b66m_relCoef R θ a (t.val, b66m_sc_slice R t a x) = q a x.val.2 := by
  have h1 := b66m_relCoef_spec R θ a t x ht hx 1
  have h2 := hq a x hx (1 : ℂ)
  rw [h1] at h2
  exact mul_right_cancel₀ (b66m_sliceD_one_ne R t a x hx) h2

end B66mRelCoef

section B66mCoefficientLaw
open scoped ContDiff

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

/-- Near a point of an overlap, the chart coefficients of a relative form obey the
transformation law of one-forms. -/
theorem b66m_relCoef_law (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a b : b66k_Index R)
    {p₀ : (Fin 10 → ℂ) × ℂ} (hp₀ : p₀ ∈ (R.atlas.A a).target)
    (hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source)
    (hp₀U : p₀.1 ∈ b6t_polydisc mr_base ∩ U) :
    ∀ᶠ p in 𝓝 p₀, b66m_relCoef R θ a p =
      b66m_relCoef R θ b (p.1, b66k_transition R a b p) *
        fderiv ℂ (b66k_transition R a b) p (0, 1) := by
  have e1 : ∀ᶠ p in 𝓝 p₀, p ∈ (R.atlas.A a).target :=
    (R.atlas.A a).open_target.mem_nhds hp₀
  have e2 : ∀ᶠ p in 𝓝 p₀, (R.atlas.A a).symm p ∈ (R.atlas.A b).source :=
    ((R.atlas.A a).continuousAt_symm hp₀).preimage_mem_nhds
      ((R.atlas.A b).open_source.mem_nhds hp₀b)
  have e3 : ∀ᶠ p in 𝓝 p₀, p.1 ∈ b6t_polydisc mr_base ∩ U :=
    continuous_fst.continuousAt.preimage_mem_nhds
      (((rf5_polydisc_isOpen mr_base).inter hU).mem_nhds hp₀U)
  filter_upwards [e1, e2, e3] with p hpa hpb hpU
  set u : b6t_polydisc mr_base := ⟨p.1, hpU.1⟩
  have hd : p.2 ∈ b66k_domain R u a := by
    change (p.1, p.2) ∈ (R.atlas.A a).target
    exact hpa
  set x := b66m_sc_pt R u ((R.atlas.A a).symm (u.val, p.2)).2
  have hxv : x.val = (R.atlas.A a).symm p := b66k_inverse_slice R u a p.2 hd
  have hxa : x.val ∈ (R.atlas.A a).source := by rw [hxv]; exact (R.atlas.A a).map_target hpa
  have hxb : x.val ∈ (R.atlas.A b).source := by rw [hxv]; exact hpb
  have h1 := b66m_relCoef_spec R θ a u x hpU.2 hxa 1
  have h2 := b66m_relCoef_spec R θ b u x hpU.2 hxb 1
  have h3 := b66m_rs_slice_change R u a b x hxa hxb 1
  have hsa : b66m_sc_slice R u a x = p.2 := by
    change (R.atlas.A a x.val).2 = p.2
    rw [hxv, (R.atlas.A a).right_inv hpa]
  have hsb : b66m_sc_slice R u b x = b66k_transition R a b p := by
    change (R.atlas.A b x.val).2 = _
    rw [hxv]
    rfl
  have hv : b66k_vertical R u a b x.val.2 = fderiv ℂ (b66k_transition R a b) p (0, 1) := by
    unfold b66k_vertical
    rw [← b66m_sc_fibre_val R u x, hxv, (R.atlas.A a).right_inv hpa]
  rw [h1, hsa, h3, hsb, hv] at h2
  have hne := b66m_sliceD_one_ne R u a x hxa
  have := mul_right_cancel₀ hne (h2.trans (mul_assoc _ _ _).symm)
  exact this

/-- The parameter derivative of the chart coefficients of `θ` is a lift of the contraction of
the Kodaira–Spencer cocycle with the form `q` that `θ` restricts to at `t`. -/
theorem b66m_relCoef_derivative_overlap (hU : IsOpen U) {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    (h : Fin 10 → ℂ) :
    (∀ a, AnalyticOnNhd ℂ (fun w =>
      fderiv ℂ (b66m_relCoef R θ a) (t.val, w) (h, 0)) (b66k_domain R t a)) ∧
    ∀ a b w, w ∈ b66k_refinementDomain R t 1 a b →
      HasDerivAt (fun z => b66g_contract R q (b66k_cocycle R t h) a b
        ((R.atlas.A a).symm (t.val, z)).2)
        (fderiv ℂ (b66m_relCoef R θ a) (t.val, w) (h, 0) -
          fderiv ℂ (b66m_relCoef R θ b)
            (t.val, b66k_transition R a b (t.val, w)) (h, 0) *
              fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) w := by
  have hW : ∀ a w, w ∈ b66k_domain R t a → (t.val, w) ∈ (R.atlas.A a).target ∩
      Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) := fun a w hw => ⟨hw, t.property, ht⟩
  refine ⟨fun a w hw => ?_, fun a b w hw => ?_⟩
  · have hfd := (b66m_relCoef_analytic R hU θ a).fderiv _ (hW a w hw)
    have hin : AnalyticAt ℂ (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) w :=
      analyticAt_const.prod analyticAt_id
    exact (ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).analyticAt _ |>.comp_of_eq
      (hfd.comp_of_eq hin rfl) rfl
  · set p₀ : (Fin 10 → ℂ) × ℂ := (t.val, w)
    set τ := b66k_transition R a b
    obtain ⟨hm, hτd, -, -⟩ := b66m_rs_transition_mem R t a b w hw
    have hτa : AnalyticAt ℂ τ p₀ := b66k_transition_analytic R a b p₀ hm
    have hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source := hm.2
    set αa := b66m_relCoef R θ a
    set αb := b66m_relCoef R θ b
    set e := τ p₀
    have hαa := b66m_relCoef_analytic R hU θ a
    have hαb := b66m_relCoef_analytic R hU θ b
    have hWb : (t.val, e) ∈ (R.atlas.A b).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) :=
      hW b e hτd
    -- the transformation law and its derivative in the parameter direction
    have hlaw := b66m_relCoef_law R hU θ a b hm.1 hp₀b ⟨t.property, ht⟩
    have hΦ : HasFDerivAt (fun p : (Fin 10 → ℂ) × ℂ => ((p.1, τ p) : (Fin 10 → ℂ) × ℂ))
        ((ContinuousLinearMap.fst ℂ _ _).prod (fderiv ℂ τ p₀)) p₀ :=
      hasFDerivAt_fst.prodMk hτa.differentiableAt.hasFDerivAt
    have hA := (hαb _ hWb).differentiableAt.hasFDerivAt.comp p₀ hΦ
    have hτ2 : AnalyticAt ℂ (fderiv ℂ τ) p₀ := hτa.fderiv
    have hΨ : HasFDerivAt (fun p => fderiv ℂ τ p (0, 1))
        ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : (Fin 10 → ℂ) × ℂ)).comp
          (fderiv ℂ (fderiv ℂ τ) p₀)) p₀ :=
      (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : (Fin 10 → ℂ) × ℂ)).hasFDerivAt.comp p₀
        hτ2.differentiableAt.hasFDerivAt
    have hprod := hA.mul hΨ
    have hβa : fderiv ℂ αa p₀ (h, 0) =
        αb (t.val, e) * fderiv ℂ (fderiv ℂ τ) p₀ (h, 0) (0, 1) +
          fderiv ℂ τ p₀ (0, 1) * fderiv ℂ αb (t.val, e) (h, fderiv ℂ τ p₀ (h, 0)) := by
      have hlaw' : αa =ᶠ[𝓝 p₀] (fun p => αb (p.1, τ p) * fderiv ℂ τ p (0, 1)) := hlaw
      rw [hlaw'.fderiv_eq, show (fun p => αb (p.1, τ p) * fderiv ℂ τ p (0, 1)) =
        ((αb ∘ fun p => (p.1, τ p)) * fun p => fderiv ℂ τ p (0, 1)) from rfl, hprod.fderiv]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.apply_apply, smul_eq_mul,
        Function.comp_apply]
      rfl
    have hsplit : fderiv ℂ αb (t.val, e) (h, fderiv ℂ τ p₀ (h, 0)) =
        fderiv ℂ αb (t.val, e) (h, 0) + fderiv ℂ τ p₀ (h, 0) * fderiv ℂ αb (t.val, e) (0, 1) := by
      have : ((h, fderiv ℂ τ p₀ (h, 0)) : (Fin 10 → ℂ) × ℂ) =
          (h, 0) + fderiv ℂ τ p₀ (h, 0) • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
    -- the contracted cocycle in the chart `a`
    have hS : (fun z => b66g_contract R q (b66k_cocycle R t h) a b
        ((R.atlas.A a).symm (t.val, z)).2) =ᶠ[𝓝 w]
        fun z => αb (t.val, τ (t.val, z)) * fderiv ℂ τ (t.val, z) (h, 0) := by
      filter_upwards [b66m_rs_overlap_eventually R t a b w hw] with z hz
      have hzb : (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A b).source :=
        hz.1.2
      have hqb := b66m_relCoef_base R ht θ q hq b _ hzb
      have hsl : b66m_sc_slice R t b (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2) =
          τ (t.val, z) := hz.2.2
      rw [hsl] at hqb
      have hqb' : αb (t.val, τ (t.val, z)) = q b ((R.atlas.A a).symm (t.val, z)).2 := hqb
      simp only [b66g_contract, b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk, hz.1, ↓reduceIte,
        hz.2.1]
      rw [hqb']
    have hl : HasDerivAt (fun z : ℂ => ((t.val, z) : (Fin 10 → ℂ) × ℂ)) (0, 1) w :=
      (hasDerivAt_const w t.val).prodMk (hasDerivAt_id w)
    have hτz : HasDerivAt (fun z => τ (t.val, z)) (fderiv ℂ τ p₀ (0, 1)) w :=
      hτa.differentiableAt.hasFDerivAt.comp_hasDerivAt w hl
    have hB : HasDerivAt (fun z => αb (t.val, τ (t.val, z)))
        (fderiv ℂ αb (t.val, e) (0, fderiv ℂ τ p₀ (0, 1))) w :=
      (hαb _ hWb).differentiableAt.hasFDerivAt.comp_hasDerivAt w
        ((hasDerivAt_const w t.val).prodMk hτz)
    have hC : HasDerivAt (fun z => fderiv ℂ τ (t.val, z) (h, 0))
        (fderiv ℂ (fderiv ℂ τ) p₀ (0, 1) (h, 0)) w :=
      ((ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).hasFDerivAt.comp p₀
        hτ2.differentiableAt.hasFDerivAt).comp_hasDerivAt w hl
    have hsymm := (hτa.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
    refine ((hB.mul hC).congr_of_eventuallyEq hS).congr_deriv ?_
    have hv1 : fderiv ℂ αb (t.val, e) (0, fderiv ℂ τ p₀ (0, 1)) =
        fderiv ℂ τ p₀ (0, 1) * fderiv ℂ αb (t.val, e) (0, 1) := by
      have : ((0, fderiv ℂ τ p₀ (0, 1)) : (Fin 10 → ℂ) × ℂ) =
          fderiv ℂ τ p₀ (0, 1) • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by ext <;> simp
      rw [this, map_smul, smul_eq_mul]
    change _ = fderiv ℂ αa p₀ (h, 0) - fderiv ℂ αb (t.val, e) (h, 0) * fderiv ℂ τ p₀ (0, 1)
    rw [hβa, hsplit, hv1, hsymm (h, 0) (0, 1)]
    ring


end B66mCoefficientLaw

/-- Pull a scalar coordinate derivative back to the real tangent space. -/
theorem b66m_cochain_real_derivative (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (u : b66k_Cochain R) (a b : b66k_Index R)
    (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source)
    (d : ℂ)
    (hd : HasDerivAt (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      d (b66m_sc_slice R t a p)) (w : ℂ) :
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun y : rf8_fibre R.C t => u a b y.val.2) p) w =
        d * b66m_sc_sliceD R t a p w := by
  let f : ℂ → ℂ := fun z => u a b ((R.atlas.A a).symm (t.val, z)).2
  have heq : (fun y : rf8_fibre R.C t => u a b y.val.2) =ᶠ[𝓝 p]
      f ∘ b66m_sc_slice R t a := by
    filter_upwards [(b66m_sc_open_source R t a).mem_nhds ha] with y hy
    exact congrArg (u a b) (b66m_sc_inv_slice R t a y hy).symm
  have hs := (b66m_sc_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hD := (HasMFDerivAt.comp (g := f) (f := b66m_sc_slice R t a) p
    hd.hasFDerivAt.hasMFDerivAt hs.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  refine ((b3A_mdifferentiableAt_real hD.mdifferentiableAt).2 w).trans ?_
  rw [hD.mfderiv]
  change b66m_sc_sliceD R t a p w • d = d * b66m_sc_sliceD R t a p w
  exact mul_comm (b66m_sc_sliceD R t a p w) d

/-- The derivative of a relative coefficient, read as a local tangent form. -/
def b66m_parameterLocalForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (h : Fin 10 → ℂ) (a : b66k_Index R) :
    TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ := fun p =>
  fderiv ℂ (b66m_relCoef R θ a) (t.val, b66m_sc_slice R t a p.1) (h, 0) *
    b66m_sc_sliceD R t a p.1 p.2

/-- The actual parameter local forms differ by the differential of contraction. -/
theorem b66m_parameterLocalForm_overlap (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ) (a b : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source)
    (w : ℂ) :
    b66m_parameterLocalForm R t θ h a ⟨p, w⟩ -
      b66m_parameterLocalForm R t θ h b ⟨p, w⟩ =
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun y : rf8_fibre R.C t =>
        b66g_contract R q (b66k_cocycle R t h) a b y.val.2) p) w := by
  have hz : b66m_sc_slice R t a p ∈ b66k_refinementDomain R t 1 a b := by
    refine ⟨b66m_sc_slice_domain R t a p ha, ?_⟩
    rw [b66m_sc_inv_slice R t a p ha, one_smul, ← b66m_sc_fibre_val R t p]
    exact hb
  have hd := (b66m_relCoef_derivative_overlap R hU ht θ q hq h).2 a b _ hz
  rw [b66m_cochain_real_derivative R t _ a b p ha _ hd w]
  have hsb : b66k_transition R a b (t.val, b66m_sc_slice R t a p) =
      b66m_sc_slice R t b p := by
    change (R.atlas.A b ((R.atlas.A a).symm
      (t.val, (R.atlas.A a p.val).2))).2 = _
    rw [← b66m_sc_slice_value R t a p ha, (R.atlas.A a).left_inv ha]
    rfl
  have hv : fderiv ℂ (b66k_transition R a b)
      (t.val, b66m_sc_slice R t a p) (0, 1) = b66k_vertical R t a b p.val.2 := by
    unfold b66k_vertical
    rw [← b66m_sc_fibre_val R t p, b66m_sc_slice_value R t a p ha]
    rfl
  simp only [b66m_parameterLocalForm]
  rw [hsb, hv, b66m_rs_slice_change R t a b p ha hb w]
  ring

/-- The corrected parameter form has its displayed expression in every retained chart. -/
theorem b66m_correctedParameterForm_local (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (a : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, w⟩ =
    b66m_parameterLocalForm R t θ h a ⟨p, w⟩ -
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) a) p) w := by
  apply b66m_correctedLocalForm_local R t ρ hρ _
    (b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h))
    (b66m_parameterLocalForm R t θ h)
    (b66m_parameterLocalForm_overlap R t hU ht θ q hq h) a p ha w


/-- The antilinear component of the actual corrected parameter form. -/
theorem b66m_correctedParameterForm_antilinear (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (p : rf8_fibre R.C t) (w : ℂ) :
    (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h) ⟨p, w⟩ + Complex.I *
      b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h) ⟨p, Complex.I • w⟩) / 2 =
      -b66m_sc_gamma R t ρ (b66g_contract R q (b66k_cocycle R t h)) ⟨p, w⟩ := by
  apply b66m_correctedLocalForm_antilinear
  intro a y v
  simp only [b66m_parameterLocalForm, smul_eq_mul]
  rw [b66m_rs_clm_apply (b66m_sc_sliceD R t a y) (Complex.I * v),
    b66m_rs_clm_apply (b66m_sc_sliceD R t a y) v]
  ring

/-- Potential endpoint differences along a retained polygon give its scalar cocycle terms. -/
theorem b66m_polygon_potential_endpoints (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t)
    {c : ℝ → R.C} (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    (∑ k ∈ Finset.range K.N,
      (b66m_sc_tau R t ρ u (a k)
        (b66m_sc_pt R t (K.v (k + 1) t.val).2) -
      b66m_sc_tau R t ρ u (a k)
        (b66m_sc_pt R t (K.v k t.val).2))) =
      -∑ k ∈ Finset.range K.N,
        u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 := by
  let p : ℤ → rf8_fibre R.C t := fun k => b66m_sc_pt R t (K.v k t.val).2
  have hp : ∀ k, (p k).val = K.v k t.val := by
    intro k
    apply Prod.ext
    · rw [K.v_u₀]
      rfl
    · rfl
  let F : ℕ → ℂ := fun k => b66m_sc_tau R t ρ u (a k) (p k)
  have hperiod : F K.N = F 0 := by
    have haN : a (K.N : ℤ) = a 0 := by simpa using ha 0
    have hpN : p (K.N : ℤ) = p 0 := by
      apply Subtype.ext
      rw [hp, hp]
      simpa using K.v_add 0 t.val
    simp only [F, haN, hpN, Nat.cast_zero]
  have hterm : ∀ k : ℕ,
      b66m_sc_tau R t ρ u (a k) (p (k + 1)) -
        b66m_sc_tau R t ρ u (a k) (p k) =
      -u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 + (F (k + 1) - F k) := by
    intro k
    have hpa : (p (k + 1)).val ∈ (R.atlas.A (a k)).source := by
      rw [hp, ← hφ k]
      exact (K.cond_u₀ k).2.1
    have hpb : (p (k + 1)).val ∈ (R.atlas.A (a (k + 1))).source := by
      rw [hp, ← hφ (k + 1)]
      exact (K.φ (k + 1)).map_target (K.ball_sub (k + 1) (K.cond_u₀ (k + 1)).1)
    have he := b66m_sc_tau_sub R t ρ hρ hu (a (k + 1)) (a k)
      (p (k + 1)) hpb hpa
    change _ - _ = u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 at he
    simp only [F, Nat.cast_add, Nat.cast_one]
    linear_combination -he
  change (∑ k ∈ Finset.range K.N,
    (b66m_sc_tau R t ρ u (a k) (p (k + 1)) -
      b66m_sc_tau R t ρ u (a k) (p k))) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_range_sub F, hperiod, sub_self, add_zero]

/-- The real differential of a smooth local function is smooth on the tangent bundle. -/
theorem b66m_realDifferential_smooth (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (f : rf8_fibre R.C t → ℂ)
    (S : Set (rf8_fibre R.C t)) (hS : IsOpen S)
    (hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f S)
    (p : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t)) (hp : p.1 ∈ S) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) =>
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f q.1) q.2) p := by
  have ho : IsOpen ((Bundle.TotalSpace.proj :
      TangentBundle 𝓘(ℝ, ℂ) (rf8_fibre R.C t) → rf8_fibre R.C t) ⁻¹' S) :=
    hS.preimage (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℝ, ℂ)))
  have hd := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hS.uniqueMDiffOn
  let pr : TangentBundle 𝓘(ℝ, ℂ) (rf8_fibre R.C t) := ⟨p.1, p.2⟩
  have hm := hd.contMDiffAt (x := pr) (ho.mem_nhds hp)
  have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ)
    (n := ∞)).contMDiffAt.comp pr hm
  have hr := RiemannRochAna_realTangent (E := ℂ) (C := rf8_fibre R.C t)
  apply (hs.comp p (hr p)).congr_of_eventuallyEq
  filter_upwards [((hr p).continuousAt).preimage_mem_nhds (ho.mem_nhds hp)] with q hq
  change (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f q.1) q.2 =
    (show ℂ →L[ℝ] ℂ from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f S q.1) q.2
  rw [mfderivWithin_of_mem_nhds (hS.mem_nhds hq)]

/-- Smoothness of a tangent form written in one retained coordinate. -/
theorem b66m_coordinateForm_smooth (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (a : b66k_Index R) (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (b66k_domain R t a))
    (p : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t))
    (hp : p.1.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) =>
        A (b66m_sc_slice R t a q.1) * b66m_sc_sliceD R t a q.1 q.2) p := by
  let S : Set (rf8_fibre R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  have hS : IsOpen S := b66m_sc_open_source R t a
  have hs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66m_sc_slice R t a) S := by
    intro y hy
    exact (b3A_contMDiffWithinAt_real
      (b66m_sc_slice_contMDiffAt R t a y hy).contMDiffWithinAt).of_le (by simp)
  have hD := b66m_realDifferential_smooth R t (b66m_sc_slice R t a) S hS hs p hp
  have hAc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (A ∘ b66m_sc_slice R t a) p.1 :=
    (b3A_contMDiffWithinAt_real
      (((hA _ (b66m_sc_slice_domain R t a p.1 hp)).contDiffAt.contMDiffAt).comp
        p.1 (b66m_sc_slice_contMDiffAt R t a p.1 hp)).contMDiffWithinAt).of_le (by simp)
  have hproj : ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) => q.1) p :=
    RiemannRochAna_projection_smooth (E := ℂ) (C := rf8_fibre R.C t) p
  apply ((hAc.comp p hproj).mul hD).congr_of_eventuallyEq
  have hpn := (FiberBundle.continuous_proj ℂ
    (TangentSpace 𝓘(ℂ, ℂ))).continuousAt (x := p)
  filter_upwards [hpn.preimage_mem_nhds (hS.mem_nhds hp)] with q hq
  have he := (b3A_mdifferentiableAt_real
    ((b66m_sc_slice_contMDiffAt R t a q.1 hq).mdifferentiableAt (by simp))).2 q.2
  exact congrArg (fun v : ℂ => A (b66m_sc_slice R t a q.1) * v) he.symm

/-- The actual parameter local form is smooth on its retained chart. -/
theorem b66m_parameterLocalForm_smooth (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (h : Fin 10 → ℂ) (a : b66k_Index R)
    (p : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t))
    (hp : p.1.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (b66m_parameterLocalForm R t θ h a) p := by
  apply b66m_coordinateForm_smooth R t a
    (fun w => fderiv ℂ (b66m_relCoef R θ a) (t.val, w) (h, 0)) _ p hp
  intro w hw
  have hfd := (b66m_relCoef_analytic R hU θ a).fderiv _
    (show (t.val, w) ∈ (R.atlas.A a).target ∩
      Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) from ⟨hw, t.property, ht⟩)
  have hin : AnalyticAt ℂ (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) w :=
    analyticAt_const.prod analyticAt_id
  exact (ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).analyticAt _
    |>.comp_of_eq (hfd.comp_of_eq hin rfl) rfl

/-- The corrected derivative of an actual relative form is globally real smooth. -/
theorem b66m_correctedParameterForm_smooth (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) :
    ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h)) := by
  intro p
  let a : b66k_Index R := p.1.val
  have hp : p.1.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  have hu := b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)
  let S : Set (rf8_fibre R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  have hS : IsOpen S := b66m_sc_open_source R t a
  have hτ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) a) S :=
    fun y hy => (b66m_sc_tau_smooth R t ρ hρ hu a y hy).contMDiffWithinAt
  have hD := b66m_realDifferential_smooth R t _ S hS hτ p hp
  have hβ := b66m_parameterLocalForm_smooth R t hU ht θ h a p hp
  apply (hβ.sub hD).congr_of_eventuallyEq
  have hproj := (FiberBundle.continuous_proj ℂ
    (TangentSpace 𝓘(ℂ, ℂ))).continuousAt (x := p)
  filter_upwards [hproj.preimage_mem_nhds (hS.mem_nhds hp)] with y hy
  exact (b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ
    a y.1 hy y.2)

/-- Integrating a local complex-valued differential along a smooth path gives endpoints. -/
theorem b66m_pathIntegral_differential (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (f : rf8_fibre R.C t → ℂ)
    (γ : ℝ → rf8_fibre R.C t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (hf : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 f (γ s)) :
    b3_pathIntegral ℂ (rf8_fibre R.C t) γ
      (fun p => (show ℂ →L[ℝ] ℂ from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f p.1) p.2) = f (γ 1) - f (γ 0) := by
  have hd : ∀ s : ℝ, HasDerivAt (f ∘ γ)
      ((show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s))
        (b3_velocity ℂ (rf8_fibre R.C t) γ s)) s := by
    intro s
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (f ∘ γ) s
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s)) :=
      HasMFDerivAt.comp s ((hf s).mdifferentiableAt one_ne_zero).hasMFDerivAt
        (hγ.mdifferentiableAt one_ne_zero).hasMFDerivAt
    have hh : HasFDerivAt (f ∘ γ)
        ((show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s)).comp
          (show ℝ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s)) s :=
      hcomp.hasFDerivAt
    exact hh.hasDerivAt
  have hc : ContDiff ℝ 1 (f ∘ γ) := by
    apply contDiff_iff_contDiffAt.2
    intro s
    exact contMDiffAt_iff_contDiffAt.1 ((hf s).comp s (hγ s))
  have hi : IntervalIntegrable (fun s =>
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s))
        (b3_velocity ℂ (rf8_fibre R.C t) γ s)) MeasureTheory.volume 0 1 := by
    have heq : (fun s =>
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s))
          (b3_velocity ℂ (rf8_fibre R.C t) γ s)) = deriv (f ∘ γ) :=
      funext fun s => (hd s).deriv.symm
    rw [heq]
    exact (hc.continuous_deriv (by simp)).intervalIntegrable _ _
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

/-- Any chart coefficient representing the relative form agrees locally with its chosen coefficient. -/
theorem b66m_relCoef_unique (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}
    (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (a : b66k_Index R) (A : (Fin 10 → ℂ) × ℂ → ℂ)
    (hA : ∀ (u : b6t_polydisc mr_base) (p : rf8_fibre R.C u), u.val ∈ U →
      p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
        θ.val u ⟨p, w⟩ = A (R.atlas.A a p.val) * b66m_sc_sliceD R u a p w)
    (z : (Fin 10 → ℂ) × ℂ)
    (hz : z ∈ (R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) :
    A =ᶠ[𝓝 z] b66m_relCoef R θ a := by
  filter_upwards [(b66m_relCoef_open R hU a).mem_nhds hz] with y hy
  let u : b6t_polydisc mr_base := ⟨y.1, hy.2.1⟩
  let p := b66m_sc_pt R u ((R.atlas.A a).symm (u.val, y.2)).2
  have hp : p.val = (R.atlas.A a).symm y :=
    b66k_inverse_slice R u a y.2 hy.1
  have hpa : p.val ∈ (R.atlas.A a).source := by
    rw [hp]
    exact (R.atlas.A a).map_target hy.1
  have hcoord : R.atlas.A a p.val = y := by
    rw [hp, (R.atlas.A a).right_inv hy.1]
  have he := (hA u p hy.2.2 hpa 1).symm.trans
    (b66m_relCoef_spec R θ a u p hy.2.2 hpa 1)
  have hs : (u.val, b66m_sc_slice R u a p) = y := by
    change (u.val, (R.atlas.A a p.val).2) = y
    rw [← b66m_sc_slice_value R u a p hpa]
    exact hcoord
  rw [hcoord, hs] at he
  exact mul_right_cancel₀ (b66m_sliceD_one_ne R u a p hpa) he

/-- The polygon derivative uses the actual retained relative coefficients. -/
theorem b66m_retained_coefficient_derivative (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) :
    ∀ h : Fin 10 → ℂ,
        fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc mr_base then
          (R.P ⟨u, hu⟩ (b63e_fibreLoopClass mr_base R.C ⟨u, hu⟩ hc hcp)).val
            (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
              θ ⟨u, hu⟩) else 0) t.val h =
        (∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
          fderiv ℂ (b66m_relCoef R θ (a k)) (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k))
            (h, 0) * (K.bb k t.val - K.a k)) +
        ∑ k ∈ Finset.range K.N,
          b66g_contract R q (b66k_cocycle R t h) (a (k + 1)) (a k)
            (K.v (k + 1) t.val).2 := by
  obtain ⟨A, hA, hd⟩ := b66m_retained_period_derivative R t U hU ht θ q hq hc hcp K a hφ
  intro h
  rw [hd h]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le zero_le_one] at hr
  have heq := b66m_relCoef_unique R hU θ (a k) (A k) ?_
    (t.val, K.a k + (r : ℂ) * (K.bb k t.val - K.a k)) ?_
  · exact congrArg (fun L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ =>
      L (h, 0) * (K.bb k t.val - K.a k)) (heq.fderiv_eq (𝕜 := ℂ))
  · intro u p hu hp w
    have hp' : p.val ∈ (K.φ k).source := by rwa [hφ k]
    have he := (hA k).2 u p hu hp' w
    have hf : (fun y : rf8_fibre R.C u => (K.φ k y.val).2) =
        b66m_sc_slice R u (a k) := by
      funext y
      rw [hφ k]
      rfl
    rw [hf, hφ k] at he
    exact he
  · refine ⟨?_, t.property, ht⟩
    rw [← hφ k]
    exact K.ball_sub k (K.segment_mem K.cond_u₀ k hr)

/-- The corrected parameter form differs from a local coefficient integral by potential endpoints. -/
theorem b66m_correctedParameterForm_pathIntegral (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (a : b66k_Index R) (γ : ℝ → rf8_fibre R.C t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (hsrc : ∀ s : ℝ, (γ s).val ∈ (R.atlas.A a).source) :
    b3_pathIntegral ℂ (rf8_fibre R.C t) γ
      (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h)) =
      b3_pathIntegral ℂ (rf8_fibre R.C t) γ (b66m_parameterLocalForm R t θ h a) -
        (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) a (γ 1) -
          b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) a (γ 0)) := by
  let u := b66g_contract R q (b66k_cocycle R t h)
  let F := b66m_sc_tau R t ρ u a
  let D : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ := fun p =>
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F p.1) p.2
  have hu := b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)
  have hF : ∀ s, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F (γ s) :=
    fun s => b66m_sc_tau_smooth R t ρ hρ hu a (γ s) (hsrc s)
  have hd := b66m_pathIntegral_differential R t F γ hγ
    (fun s => (hF s).of_le (by simp))
  have hvel := b3A_continuous_velocity γ hγ
  have hβ : Continuous (fun s => b66m_parameterLocalForm R t θ h a
      ⟨γ s, b3_velocity ℂ (rf8_fibre R.C t) γ s⟩) :=
    continuous_iff_continuousAt.2 fun s =>
      (b66m_parameterLocalForm_smooth R t hU ht θ h a _ (hsrc s)).continuousAt.comp
        hvel.continuousAt
  have hD : Continuous (fun s => D ⟨γ s, b3_velocity ℂ (rf8_fibre R.C t) γ s⟩) := by
    apply continuous_iff_continuousAt.2
    intro s
    have hFs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F
        {y | y.val ∈ (R.atlas.A a).source} :=
      fun y hy => (b66m_sc_tau_smooth R t ρ hρ hu a y hy).contMDiffWithinAt
    have hc : ContinuousAt D ⟨γ s, b3_velocity ℂ (rf8_fibre R.C t) γ s⟩ :=
      (b66m_realDifferential_smooth R t F _ (b66m_sc_open_source R t a)
        hFs ⟨γ s, b3_velocity ℂ (rf8_fibre R.C t) γ s⟩ (hsrc s)).continuousAt
    exact hc.comp (f := fun r =>
      (⟨γ r, b3_velocity ℂ (rf8_fibre R.C t) γ r⟩ :
        TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t))) hvel.continuousAt
  change _ = _ - (F (γ 1) - F (γ 0))
  rw [← hd]
  unfold b3_pathIntegral
  rw [← intervalIntegral.integral_sub (hβ.intervalIntegrable _ _) (hD.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _
  exact b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ a
    (γ s) (hsrc s) _

/-- A retained-coordinate form has a holomorphic primitive near each point. -/
theorem b66m_coordinateForm_local_primitive (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (a : b66k_Index R) (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (b66k_domain R t a))
    (p : rf8_fibre R.C t) (hp : p.val ∈ (R.atlas.A a).source) :
    ∃ (V : Set (rf8_fibre R.C t)) (F : rf8_fibre R.C t → ℂ),
      IsOpen V ∧ p ∈ V ∧
      (∀ y ∈ V, y.val ∈ (R.atlas.A a).source ∧
        ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F y) ∧
      ∀ y ∈ V, ∀ w : ℂ,
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y) w =
          A (b66m_sc_slice R t a y) * b66m_sc_sliceD R t a y w := by
  let z := b66m_sc_slice R t a p
  have hdom : IsOpen (b66k_domain R t a) :=
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hdom z
    (b66m_sc_slice_domain R t a p hp)
  obtain ⟨G, hG⟩ := (show DifferentiableOn ℂ A (Metric.ball z r) from
    fun w hw => (hA w (hball hw)).differentiableAt.differentiableWithinAt).isExactOn_ball
  let S : Set (rf8_fibre R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  let V : Set (rf8_fibre R.C t) := S ∩ (b66m_sc_slice R t a) ⁻¹' Metric.ball z r
  have hS : IsOpen S := b66m_sc_open_source R t a
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact inter_mem (hS.mem_nhds hy.1)
      ((b66m_sc_slice_contMDiffAt R t a y hy.1).continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds hy.2))
  have hGc : ∀ w ∈ Metric.ball z r, ContDiffAt ℂ ω G w := by
    intro w hw
    have hd : DifferentiableOn ℂ G (Metric.ball z r) :=
      fun v hv => (hG v hv).differentiableAt.differentiableWithinAt
    exact (hd.analyticOnNhd Metric.isOpen_ball w hw).contDiffAt
  refine ⟨V, G ∘ b66m_sc_slice R t a, hV, ⟨hp, Metric.mem_ball_self hr⟩,
    fun y hy => ⟨hy.1, (hGc _ hy.2).contMDiffAt.comp y
      (b66m_sc_slice_contMDiffAt R t a y hy.1)⟩, ?_⟩
  intro y hy w
  have hs := (b66m_sc_slice_contMDiffAt R t a y hy.1).mdifferentiableAt (by simp)
  have hd := HasMFDerivAt.comp y (hG _ hy.2).hasFDerivAt.hasMFDerivAt hs.hasMFDerivAt
  refine ((b3A_mdifferentiableAt_real hd.mdifferentiableAt).2 w).trans ?_
  rw [hd.mfderiv]
  change b66m_sc_sliceD R t a y w • A (b66m_sc_slice R t a y) = _
  exact mul_comm _ _

/-- The actual smooth corrected parameter form has a smooth primitive near each point. -/
theorem b66m_correctedParameterForm_local_primitive (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (p : rf8_fibre R.C t) :
    ∃ (V : Set (rf8_fibre R.C t)) (G : rf8_fibre R.C t → ℂ),
      IsOpen V ∧ p ∈ V ∧
      (∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G y) ∧
      ∀ y ∈ V, ∀ w : ℂ,
        b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
          (b66m_parameterLocalForm R t θ h) ⟨y, w⟩ =
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G y) w := by
  let a : b66k_Index R := p.val
  have hp : p.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  obtain ⟨V, F, hV, hpV, hF, hdF⟩ := b66m_coordinateForm_local_primitive R t a
    (fun w => fderiv ℂ (b66m_relCoef R θ a) (t.val, w) (h, 0))
    ((b66m_relCoef_derivative_overlap R hU ht θ q hq h).1 a) p hp
  let T := b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) a
  have hu := b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)
  have hT : ∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ T y :=
    fun y hy => b66m_sc_tau_smooth R t ρ hρ hu a y (hF y hy).1
  have hFr : ∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F y :=
    fun y hy => (b3A_contMDiffWithinAt_real (hF y hy).2.contMDiffWithinAt).of_le (by simp)
  refine ⟨V, F - T, hV, hpV, fun y hy => (hFr y hy).sub (hT y hy), ?_⟩
  intro y hy w
  rw [b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ a y (hF y hy).1 w]
  have hd := mfderiv_sub ((hFr y hy).mdifferentiableAt (by simp))
    ((hT y hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) hd
  calc
    _ = (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y) w -
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) T y) w := by
      rw [hdF y hy w]
      rfl
    _ = _ := he.symm

/-- Reparametrization for a smooth tangent form homogeneous under real scalars. -/
theorem b66m_real_integral_reparam (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hθ : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ θ)
    (hlin : ∀ (p : rf8_fibre R.C t) (c : ℝ) (v : ℂ),
      θ ⟨p, c • v⟩ = c • θ ⟨p, v⟩)
    (γ : ℝ → rf8_fibre R.C t) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 1 σ) (a b : ℝ) :
    (∫ s in a..b, b3A_integrand θ (γ ∘ σ) s) =
      ∫ s in σ a..σ b, b3A_integrand θ γ s := by
  have hd : Differentiable ℝ σ := hσ.differentiable one_ne_zero
  have hpt : ∀ s, b3A_integrand θ (γ ∘ σ) s =
      deriv σ s • b3A_integrand θ γ (σ s) := by
    intro s
    have hv := b3A_velocity_reparam γ hγ σ hd s
    show θ ⟨γ (σ s), b3A_vel (E := ℂ) (γ ∘ σ) s⟩ = _
    rw [hv]
    exact hlin _ _ _
  have hc : Continuous (b3A_integrand θ γ) :=
    hθ.continuous.comp (b3A_continuous_velocity γ hγ)
  rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
  exact intervalIntegral.integral_deriv_smul_comp (fun s _ => (hd s).hasDerivAt)
    (hσ.continuous_deriv le_rfl).continuousOn hc

/-- Integration of a smooth real tangent form over a floor-glued polygon. -/
theorem b66m_real_floorLoop_pathIntegral (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hθ : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ θ)
    (hlin : ∀ (p : rf8_fibre R.C t) (c : ℝ) (v : ℂ),
      θ ⟨p, c • v⟩ = c • θ ⟨p, v⟩) (N : ℕ) (γ : ℤ → ℝ → rf8_fibre R.C t) (z : ℤ → rf8_fibre R.C t)
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) :
    b3_pathIntegral ℂ (rf8_fibre R.C t) (fun t ↦ γ ⌊(N : ℝ) * t⌋ (Int.fract ((N : ℝ) * t))) θ =
      ∑ k ∈ Finset.range N, b3_pathIntegral ℂ (rf8_fibre R.C t) (γ k) θ := by
  set L : ℝ → rf8_fibre R.C t := fun u ↦ γ ⌊u⌋ (Int.fract u)
  have hL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 L := b3Rest_floorPath_contMDiff γ z hγ
  have hσ : ContDiff ℝ 1 (fun t : ℝ ↦ (N : ℝ) * t) := contDiff_const.mul contDiff_id
  have h1 := b66m_real_integral_reparam R t θ hθ hlin L hL (fun t : ℝ ↦ (N : ℝ) * t) hσ 0 1
  simp only [mul_zero, mul_one] at h1
  unfold b3_pathIntegral
  change ∫ t in (0 : ℝ)..1, b3A_integrand θ (L ∘ fun t ↦ (N : ℝ) * t) t = _
  rw [h1]
  have hint : ∀ k : ℕ, IntervalIntegrable (b3A_integrand θ L) MeasureTheory.volume k (k + 1) :=
    fun k ↦ (hθ.continuous.comp (b3A_continuous_velocity L hL)).intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (k : ℝ)) (f := b3A_integrand θ L) (μ := MeasureTheory.volume) (n := N)
    (fun k _ ↦ by push_cast; exact hint k)
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : ∀ t ∈ uIcc (k : ℝ) (k + 1), b3A_integrand θ L t =
      b3A_integrand θ (γ k ∘ fun t ↦ t - k) t := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    refine b3A_integrand_congr θ ?_
    rcases ht.1.lt_or_eq with h0 | h0
    · rcases ht.2.lt_or_eq with h1 | h1
      · filter_upwards [Ioo_mem_nhds h0 h1] with v hv
        have hfl : ⌊v⌋ = (k : ℤ) := by
          rw [Int.floor_eq_iff]; push_cast; exact ⟨hv.1.le, hv.2⟩
        simp only [L, Function.comp_apply, Int.fract, hfl]
        push_cast
        rfl
      · subst h1
        have he := b63e_floorPath_eventually_const γ z hγ ((k : ℤ) + 1)
        have ht : Tendsto (fun v : ℝ ↦ v - k) (𝓝 ((k : ℝ) + 1)) (𝓝 1) :=
          (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
        push_cast at he
        filter_upwards [he, ht.eventually (hγ k).2.2] with v h1 h2
        exact h1.trans h2.symm
    · subst h0
      have he := b63e_floorPath_eventually_const γ z hγ (k : ℤ)
      have ht : Tendsto (fun v : ℝ ↦ v - k) (𝓝 (k : ℝ)) (𝓝 0) :=
        (continuous_id.sub continuous_const).tendsto' _ _ (by simp)
      push_cast at he
      filter_upwards [he, ht.eventually (hγ k).2.1] with v h1 h2
      exact h1.trans h2.symm
  push_cast
  rw [intervalIntegral.integral_congr hk,
    b66m_real_integral_reparam R t θ hθ hlin (γ k) (hγ k).1 (fun t ↦ t - k) (contDiff_id.sub contDiff_const)]
  simp only [sub_self, add_sub_cancel_left]
  rfl

/-- The actual corrected form is homogeneous under real tangent scalars. -/
theorem b66m_correctedParameterForm_real_smul (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (p : rf8_fibre R.C t) (c : ℝ) (v : ℂ) :
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, c • v⟩ =
      c • b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h) ⟨p, v⟩ := by
  obtain ⟨V, G, _, hp, _, hG⟩ :=
    b66m_correctedParameterForm_local_primitive R t hU ht θ q hqf hq h ρ hρ p
  rw [hG p hp (c • v), hG p hp v]
  exact (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G p).map_smul c v

/-- Integrate an actual parameter local form along a retained fibre segment. -/
theorem b66m_parameterLocalForm_segment_integral (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (h : Fin 10 → ℂ) {c : ℝ → R.C}
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) (k : ℤ) :
    b3_pathIntegral ℂ (rf8_fibre R.C t)
      (K.segF (b6t_polydisc mr_base) (Subset.refl _) t k)
      (b66m_parameterLocalForm R t θ h (a k)) =
    ∫ s in (0 : ℝ)..1,
      fderiv ℂ (b66m_relCoef R θ (a k))
        (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k)) (h, 0) *
          (K.bb k t.val - K.a k) := by
  apply b63e_slice_segment_integral mr_base R.C (b6t_polydisc mr_base)
    (Subset.refl _) t (R.hincl t) (K.mem_atlas k) (K.fp k)
    (b66m_parameterLocalForm R t θ h (a k))
    (fun z => fderiv ℂ (b66m_relCoef R θ (a k)) z (h, 0)) ?_
    (K.a k) (K.bb k t.val) (fun s hs => K.ball_sub k (K.segment_mem K.cond_u₀ k hs)) ?_
  · intro p hp w
    have hpa : p.val ∈ (R.atlas.A (a k)).source := by rwa [← hφ k]
    have hf : (fun y : rf8_fibre R.C t => (K.φ k y.val).2) =
        b66m_sc_slice R t (a k) := by
      funext y
      rw [hφ k]
      rfl
    rw [hf, hφ k, b66m_sc_slice_value R t (a k) p hpa]
    rfl
  · intro s hs
    have hp := K.ball_sub k (K.segment_mem K.cond_u₀ k hs)
    rw [hφ k] at hp
    have han := b66m_relCoef_analytic R hU θ (a k) _ ⟨hp, t.property, ht⟩
    exact han.fderiv.continuousAt.clm_apply continuousAt_const

/-- The actual corrected global form integrates to the derivative of the retained loop period. -/
theorem b66m_correctedParameterForm_polygon_period (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc mr_base then
      (R.P ⟨u, hu⟩ (b63e_fibreLoopClass mr_base R.C ⟨u, hu⟩ hc hcp)).val
        (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
          θ ⟨u, hu⟩) else 0) t.val h =
    b3_pathIntegral ℂ (rf8_fibre R.C t)
      (K.loopF (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀).1
      (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h)) := by
  let γ := K.segF (b6t_polydisc mr_base) (Subset.refl _) t
  let B := b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
    (b66m_parameterLocalForm R t θ h)
  have hg := K.segF_good (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀
  have hp : ∀ k, (b66m_sc_pt R t (K.v k t.val).2).val = K.v k t.val := by
    intro k
    apply Prod.ext
    · rw [K.v_u₀]
      rfl
    · rfl
  have hsrc : ∀ k s, (γ k s).val ∈ (R.atlas.A (a k)).source := by
    intro k s
    change (K.segF (b6t_polydisc mr_base) (Subset.refl _) t k s).val ∈ _
    rw [K.segF_val _ _ _ K.cond_u₀, ← hφ k]
    exact (K.φ k).map_target (K.ball_sub k (K.w_mem K.cond_u₀ k s))
  have hzero : ∀ k, γ k 0 = b66m_sc_pt R t (K.v k t.val).2 := by
    intro k
    apply Subtype.ext
    change (K.segF (b6t_polydisc mr_base) (Subset.refl _) t k 0).val = _
    rw [K.segF_val _ _ _ K.cond_u₀, K.seg_zero k (by norm_num)]
    exact (hp k).symm
  have hone : ∀ k, γ k 1 = b66m_sc_pt R t (K.v (k + 1) t.val).2 := by
    intro k
    apply Subtype.ext
    change (K.segF (b6t_polydisc mr_base) (Subset.refl _) t k 1).val = _
    rw [K.segF_val _ _ _ K.cond_u₀, K.seg_one K.cond_u₀ k (by norm_num)]
    exact (hp (k + 1)).symm
  have hs : ∀ k : ℤ, b3_pathIntegral ℂ (rf8_fibre R.C t) (γ k) B =
      (∫ s in (0 : ℝ)..1, fderiv ℂ (b66m_relCoef R θ (a k))
        (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k)) (h, 0) *
          (K.bb k t.val - K.a k)) -
      (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) (a k)
        (b66m_sc_pt R t (K.v (k + 1) t.val).2) -
      b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) (a k)
        (b66m_sc_pt R t (K.v k t.val).2)) := by
    intro k
    have he := b66m_correctedParameterForm_pathIntegral R t hU ht θ q hqf hq h ρ hρ
      (a k) (γ k) (hg k).1 (hsrc k)
    rw [hone, hzero] at he
    change b3_pathIntegral ℂ (rf8_fibre R.C t) (γ k) B = _ at he
    rw [b66m_parameterLocalForm_segment_integral R t hU ht θ h K a hφ k] at he
    exact he
  rw [b66m_retained_coefficient_derivative R t U hU ht θ q hq hc hcp K a hφ h]
  symm
  change b3_pathIntegral ℂ (rf8_fibre R.C t)
    (fun s => γ ⌊(K.N : ℝ) * s⌋ (Int.fract ((K.N : ℝ) * s))) B = _
  rw [b66m_real_floorLoop_pathIntegral R t B
    (b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ)
    (b66m_correctedParameterForm_real_smul R t hU ht θ q hqf hq h ρ hρ)
    K.N γ (fun k => γ k 0) hg]
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, b66m_polygon_potential_endpoints R t ρ hρ _
    (b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)) K a hφ ha]
  ring

/-- The corrected form represents the derivative of the original fixed-cycle period function. -/
theorem b66m_correctedParameterForm_flat_period (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (q : b66g_Coeff R) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    fderiv ℂ (b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
      R.P θ s (b63e_fibreLoopClass mr_base R.C s hc hcp)) t.val h =
    b3_pathIntegral ℂ (rf8_fibre R.C t)
      (K.loopF (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀).1
      (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h)) := by
  rw [b66m_flat_loop_period R s θ hc hcp]
  exact b66m_correctedParameterForm_polygon_period R t hU ht θ q hqf hq h ρ hρ
    hc hcp K a hφ ha

end HodgeLean.Foundations.Program
