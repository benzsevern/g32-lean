import HodgeLean.Foundations.Program.PrymVariationFramesCover
import HodgeLean.Foundations.Program.PrymVariationFramesParamIntegral

noncomputable section
open Set Filter Topology Metric
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

namespace b63e_Cover

variable {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
  [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)] {u₀ : Fin 10 → ℂ}
  {Γ : ℝ → b6t_polydisc b × C} (K : b63e_Cover b C u₀ Γ)

/-- The `k`-th segment in the fibre at `t`. -/
def segF (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) (k : ℤ) (τ : ℝ) :
    b63l_parameterFibre b C V hV t :=
  b63e_slice b C V hV t (K.φ k) (K.w k t.val τ)

theorem segF_val (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (ht : ∀ k, K.cond t.val k) (k : ℤ) (τ : ℝ) :
    (K.segF V hV t k τ).val = K.seg k t.val τ :=
  b63e_slice_val b C V hV t (K.φ k) (K.fp k) (K.ball_sub k (K.w_mem ht k τ))

theorem segF_add (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) (k : ℤ) :
    K.segF V hV t (k + K.N) = K.segF V hV t k := by
  funext τ
  simp only [segF, K.φ_add, K.w_add]

theorem contDiff_w (k : ℤ) (u : Fin 10 → ℂ) : ContDiff ℝ 1 (K.w k u) :=
  contDiff_const.add ((Complex.ofRealCLM.contDiff.comp b3A_step_contDiff).mul contDiff_const)

variable [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]

theorem segF_good (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (ht : ∀ k, K.cond t.val k) (k : ℤ) :
    b3A_IsGoodPath (E := ℂ) (K.segF V hV t k) (K.segF V hV t k 0)
      (K.segF V hV t (k + 1) 0) := by
  refine ⟨b63e_slice_comp_contMDiff b C V hV t hincl (K.mem_atlas k) (K.fp k) (K.contDiff_w k _)
    (fun τ ↦ K.ball_sub k (K.w_mem ht k τ)), ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with τ hτ
    simp only [segF, K.w_zero k (le_of_lt hτ), K.w_zero k (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with τ hτ
    apply Subtype.ext
    rw [K.segF_val V hV t ht, K.segF_val V hV t ht, K.seg_one ht k (le_of_lt hτ),
      K.seg_zero (k + 1) (by norm_num)]

/-- The moving polygonal loop in the fibre at `t`. -/
def loopF (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (ht : ∀ k, K.cond t.val k) : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t) :=
  ⟨fun τ ↦ K.segF V hV t ⌊(K.N : ℝ) * τ⌋ (Int.fract ((K.N : ℝ) * τ)), fun τ ↦ by
    simp only [mul_add, mul_one]
    rw [Int.floor_add_natCast, Int.fract_add_natCast, K.segF_add], by
    have h := b3Rest_floorPath_contMDiff (K.segF V hV t) (fun k ↦ K.segF V hV t k 0)
      (K.segF_good V hV t hincl ht)
    exact h.comp ((contDiff_const.mul contDiff_id).contMDiff)⟩

theorem loopF_val (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (ht : ∀ k, K.cond t.val k) (τ : ℝ) :
    ((K.loopF V hV t hincl ht).1 τ).val = K.floorLoop t.val ((K.N : ℝ) * τ) :=
  K.segF_val V hV t ht _ _

theorem loopF_pathIntegral (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hincl : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (ht : ∀ k, K.cond t.val k)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ}
    (hθ : θ ∈ b3_HolForm ℂ (b63l_parameterFibre b C V hV t))
    (A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ)
    (hθA : ∀ k, ∀ x : b63l_parameterFibre b C V hV t, x.val ∈ (K.φ k).source →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) x, θ ⟨x, v⟩ = A k (K.φ k x.val) * (show ℂ from
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun z : b63l_parameterFibre b C V hV t ↦ (K.φ k z.val).2) x v))
    (hAc : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1,
      ContinuousAt (A k) (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k))) :
    b3_pathIntegral ℂ _ (K.loopF V hV t hincl ht).1 θ =
      ∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
        A k (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k)) * (K.bb k t.val - K.a k) := by
  rw [show (K.loopF V hV t hincl ht).1 = fun τ ↦
      K.segF V hV t ⌊(K.N : ℝ) * τ⌋ (Int.fract ((K.N : ℝ) * τ)) from rfl,
    b63e_floorLoop_pathIntegral hθ K.N (K.segF V hV t) (fun k ↦ K.segF V hV t k 0)
      (K.segF_good V hV t hincl ht)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact b63e_slice_segment_integral b C V hV t hincl (K.mem_atlas k) (K.fp k) θ (A k) (hθA k)
    (K.a k) (K.bb k t.val) (fun s hs ↦ K.ball_sub k (K.segment_mem ht k hs)) (hAc k)

end b63e_Cover

open scoped Classical in
set_option maxHeartbeats 400000 in
theorem b63e_fibre_period_analyticAt (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hA : ∀ q : b6t_polydisc b × C, ∃ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      q ∈ φ.source ∧ ∀ y ∈ φ.source, (φ y).1 = y.1.val)
    (hincl : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ x.val))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (θ : b63e_relForm b C V hV U) (u₀ : V)
    (hu₀ : u₀.val ∈ U) {c : ℝ → C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    AnalyticAt ℂ (fun u ↦ if h : u ∈ V then
      (P ⟨u, h⟩ (b63e_fibreLoopClass b C ⟨u, hV h⟩ hc hcp)).val
        (b63e_relFormAt b C V hV θ ⟨u, h⟩) else 0) u₀.val := by
  classical
  obtain ⟨K⟩ : Nonempty (b63e_Cover b C u₀.val
      (fun τ ↦ ((⟨u₀.val, hV u₀.property⟩ : b6t_polydisc b), c τ))) :=
    b63e_exists_cover b C hA ⟨u₀.val, hV u₀.property⟩ hc hcp
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
  have hI : ∀ k, AnalyticAt ℂ (I k) u₀.val := by
    intro k
    set Φ : ((Fin 10 → ℂ) × ℂ) × ℂ → ℂ := fun q ↦
      A k (q.1.1, K.a k + q.2 * (q.1.2 - K.a k)) * (q.1.2 - K.a k)
    have hΦ : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ Φ ((u₀.val, K.bb k u₀.val), (s : ℂ)) := by
      intro s hs
      have hpt := K.ball_sub k (K.segment_mem K.cond_u₀ k hs)
      have hA' := hAat k _ hpt u₀.property hu₀
      have hg : AnalyticAt ℂ (fun q : ((Fin 10 → ℂ) × ℂ) × ℂ ↦
          (q.1.1, K.a k + q.2 * (q.1.2 - K.a k))) ((u₀.val, K.bb k u₀.val), (s : ℂ)) :=
        (analyticAt_fst.comp analyticAt_fst).prod (analyticAt_const.add (analyticAt_snd.mul
          ((analyticAt_snd.comp analyticAt_fst).sub analyticAt_const)))
      have hl : AnalyticAt ℂ (fun q : ((Fin 10 → ℂ) × ℂ) × ℂ ↦ q.1.2 - K.a k)
          ((u₀.val, K.bb k u₀.val), (s : ℂ)) :=
        (analyticAt_snd.comp analyticAt_fst).sub analyticAt_const
      exact (AnalyticAt.comp (g := A k)
        (f := fun q : ((Fin 10 → ℂ) × ℂ) × ℂ ↦ (q.1.1, K.a k + q.2 * (q.1.2 - K.a k)))
        hA' hg).mul hl
    have h := b63e_analyticAt_intervalIntegral hΦ
    have hin : AnalyticAt ℂ (fun u ↦ (u, K.bb k u)) u₀.val := analyticAt_id.prod (hbb k)
    exact AnalyticAt.comp (g := fun x : (Fin 10 → ℂ) × ℂ ↦ ∫ s in (0 : ℝ)..1, Φ (x, (s : ℂ)))
      (f := fun u ↦ (u, K.bb k u)) h hin
  have hsum : AnalyticAt ℂ (fun u ↦ ∑ k ∈ Finset.range K.N, I k u) u₀.val :=
    Finset.analyticAt_fun_sum _ (fun k _ ↦ hI k)
  refine hsum.congr ?_
  have hnhds : ∀ᶠ u in 𝓝 u₀.val, (∀ k, K.cond u k) ∧ u ∈ V ∧ u ∈ U :=
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

end HodgeLean.Foundations.Program
