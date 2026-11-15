import HodgeLean.Foundations.Program.GriffithsTransversalityComparison
import HodgeLean.Foundations.Program.HolomorphicODE

/-! Periods of a relative form over nearby fibres along moving retained polygons, their
analyticity in the parameter, and their derivative as a chain period.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff Interval
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

section B66gTransport

theorem b66g_transport_trans (R : rf8_SharedFamily) (s t u : b6t_polydisc mr_base) :
    b6m_transport mr_base R.C s u =
      (b6m_transport mr_base R.C s t).trans (b6m_transport mr_base R.C t u) :=
  Homeomorph.ext fun _ => rfl

theorem b66g_H1Equiv_trans (R : rf8_SharedFamily) (s t u : b6t_polydisc mr_base)
    (x : b6m_H1 (rf8_fibre R.C s)) :
    b6m_H1Equiv (b6m_transport mr_base R.C s u) x =
      b6m_H1Equiv (b6m_transport mr_base R.C t u) (b6m_H1Equiv (b6m_transport mr_base R.C s t) x) := by
  have h := b6m_homology_linearMap_ext (rf8_fibre R.C s) (b6m_H1 (rf8_fibre R.C u))
    (b6m_H1Equiv (b6m_transport mr_base R.C s u)).toLinearMap
    ((b6m_H1Equiv (b6m_transport mr_base R.C t u)).toLinearMap.comp
      (b6m_H1Equiv (b6m_transport mr_base R.C s t)).toLinearMap) (fun γ => ?_)
  · exact LinearMap.congr_fun h x
  · simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_apply]
    rw [b66g_loopClass_eq_cls, b66g_cls_map, b66g_cls_map]
    erw [b66g_cls_map]
    rfl

end B66gTransport

section B66gRelCoef

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

/-- The coefficient of a relative form in a retained chart. -/
theorem b66g_relCoef_exists
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R) :
    ∃ α : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ α ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) ∧
      ∀ (u : b6t_polydisc mr_base) (x : rf8_fibre R.C u), u.val ∈ U →
        x.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
          θ.val u ⟨x, v⟩ = α (u.val, b66g_slice R u a x) * b66g_sliceD R u a x v := by
  obtain ⟨α, hα, hθ⟩ := θ.property.2 (R.atlas.A a) (R.atlas.hA a).2 (R.atlas.hparam a)
  refine ⟨α, hα, fun u x hu hx v => ?_⟩
  rw [hθ u x hu hx v, b66g_slice_value R u a x hx]
  rfl

/-- The chosen coefficient of a relative form in a retained chart. -/
def b66g_relCoef (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (a : b66k_Index R) : (Fin 10 → ℂ) × ℂ → ℂ :=
  (b66g_relCoef_exists R θ a).choose

theorem b66g_relCoef_open (hU : IsOpen U) (a : b66k_Index R) :
    IsOpen ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) :=
  (R.atlas.A a).open_target.inter (((rf5_polydisc_isOpen mr_base).inter hU).preimage continuous_fst)

theorem b66g_relCoef_analytic (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R) :
    AnalyticOnNhd ℂ (b66g_relCoef R θ a)
      ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) :=
  ((b66g_relCoef_open R hU a).analyticOn_iff_analyticOnNhd).1
    (b66g_relCoef_exists R θ a).choose_spec.1

theorem b66g_relCoef_spec
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a : b66k_Index R)
    (u : b6t_polydisc mr_base) (x : rf8_fibre R.C u) (hu : u.val ∈ U)
    (hx : x.val ∈ (R.atlas.A a).source) (v : ℂ) :
    θ.val u ⟨x, v⟩ = b66g_relCoef R θ a (u.val, b66g_slice R u a x) * b66g_sliceD R u a x v :=
  (b66g_relCoef_exists R θ a).choose_spec.2 u x hu hx v

theorem b66g_sliceD_one_ne (t : b6t_polydisc mr_base) (a : b66k_Index R) (x : rf8_fibre R.C t)
    (hx : x.val ∈ (R.atlas.A a).source) : b66g_sliceD R t a x 1 ≠ 0 := by
  intro h
  apply (b66g_slice_coordinate_aux R t a).2 x hx
  ext1
  change b66g_sliceD R t a x 1 = 0
  exact h

/-- At the base fibre the chart coefficient of `θ` is the coefficient of the given form. -/
theorem b66g_relCoef_base {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    (a : b66k_Index R) (x : rf8_fibre R.C t) (hx : x.val ∈ (R.atlas.A a).source) :
    b66g_relCoef R θ a (t.val, b66g_slice R t a x) = q a x.val.2 := by
  have h1 := b66g_relCoef_spec R θ a t x ht hx 1
  have h2 := hq a x hx (1 : ℂ)
  rw [h1] at h2
  exact mul_right_cancel₀ (b66g_sliceD_one_ne R t a x hx) h2

end B66gRelCoef

section B66gSegAnalytic

/-- Parameter–endpoint pairs whose segment from `c` stays in `W`. -/
def b66g_tube (W : Set ((Fin 10 → ℂ) × ℂ)) (c : ℂ) : Set ((Fin 10 → ℂ) × ℂ) :=
  {z | ∀ r ∈ Icc (0 : ℝ) 1, (z.1, c + (r : ℂ) * (z.2 - c)) ∈ W}

theorem b66g_segMap_continuous (c : ℂ) :
    Continuous (fun p : ((Fin 10 → ℂ) × ℂ) × ℝ => (p.1.1, c + (p.2 : ℂ) * (p.1.2 - c))) :=
  (continuous_fst.comp continuous_fst).prodMk (continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_snd).mul
      ((continuous_snd.comp continuous_fst).sub continuous_const)))

theorem b66g_tube_open {W : Set ((Fin 10 → ℂ) × ℂ)} (hW : IsOpen W) (c : ℂ) :
    IsOpen (b66g_tube W c) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := z)
    (P := fun z (r : ℝ) => (z.1, c + (r : ℂ) * (z.2 - c)) ∈ W) fun r hr =>
      (b66g_segMap_continuous c).continuousAt.preimage_mem_nhds (hW.mem_nhds (hz r hr))

/-- Segment integrals of a jointly analytic coefficient are jointly analytic in the parameter
and the endpoint. -/
theorem b66g_segInt_analytic {W : Set ((Fin 10 → ℂ) × ℂ)} (hW : IsOpen W)
    {α : (Fin 10 → ℂ) × ℂ → ℂ} (hα : AnalyticOnNhd ℂ α W) (c : ℂ) :
    AnalyticOnNhd ℂ (fun z => b66g_segInt (fun w => α (z.1, w)) c z.2) (b66g_tube W c) := by
  refine b65_parameter_integral_analytic ℂ ((Fin 10 → ℂ) × ℂ)
    (fun p : ℝ × ((Fin 10 → ℂ) × ℂ) => α (p.2.1, c + (p.1 : ℂ) * (p.2.2 - c)) * (p.2.2 - c))
    (b66g_tube W c) 0 1 (b66g_tube_open hW c) ?_ ?_
  · intro p hp
    obtain ⟨hr, hz⟩ := hp
    rw [uIcc_of_le zero_le_one] at hr
    have hm := hz p.1 hr
    have hc : Continuous (fun p : ℝ × ((Fin 10 → ℂ) × ℂ) =>
        (p.2.1, c + (p.1 : ℂ) * (p.2.2 - c))) :=
      (continuous_fst.comp continuous_snd).prodMk (continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          ((continuous_snd.comp continuous_snd).sub continuous_const)))
    exact (((hα _ hm).continuousAt.comp_of_eq hc.continuousAt rfl).mul
      ((continuous_snd.comp continuous_snd).sub continuous_const).continuousAt).continuousWithinAt
  · intro r hr z hz
    rw [uIcc_of_le zero_le_one] at hr
    have hm := hz r hr
    have hin : AnalyticAt ℂ (fun z : (Fin 10 → ℂ) × ℂ => (z.1, c + (r : ℂ) * (z.2 - c))) z :=
      analyticAt_fst.prod (analyticAt_const.add (analyticAt_const.mul
        (analyticAt_snd.sub analyticAt_const)))
    exact ((hα _ hm).comp_of_eq hin rfl).mul (analyticAt_snd.sub analyticAt_const)

/-- Derivative of a segment integral of a jointly analytic coefficient along a line. -/
theorem b66g_segInt_hasDerivAt_line {W : Set ((Fin 10 → ℂ) × ℂ)} (hW : IsOpen W)
    {α : (Fin 10 → ℂ) × ℂ → ℂ} (hα : AnalyticOnNhd ℂ α W) (c : ℂ)
    {p v : (Fin 10 → ℂ) × ℂ} (hp : p ∈ b66g_tube W c) :
    HasDerivAt (fun l : ℂ => b66g_segInt (fun w => α ((p + l • v).1, w)) c (p + l • v).2)
      (∫ r in (0 : ℝ)..1, (fderiv ℂ α (p.1, c + (r : ℂ) * (p.2 - c)) (v.1, (r : ℂ) * v.2) *
        (p.2 - c) + α (p.1, c + (r : ℂ) * (p.2 - c)) * v.2)) 0 := by
  set z : ℂ → (Fin 10 → ℂ) × ℂ := fun l => p + l • v with hz
  have hzc : Continuous z := continuous_const.add (continuous_id.smul continuous_const)
  have hnhds : z ⁻¹' b66g_tube W c ∈ 𝓝 (0 : ℂ) :=
    hzc.continuousAt.preimage_mem_nhds ((b66g_tube_open hW c).mem_nhds (by simpa [hz] using hp))
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set ε := ε₀ / 2
  have hε : 0 < ε := by positivity
  have hcb : Metric.closedBall (0 : ℂ) ε ⊆ z ⁻¹' b66g_tube W c :=
    (Metric.closedBall_subset_ball (by simp only [ε]; linarith)).trans hball
  let G : ℂ → ℝ → (Fin 10 → ℂ) × ℂ := fun l r => ((z l).1, c + (r : ℂ) * ((z l).2 - c))
  have hGc : Continuous (fun q : ℂ × ℝ => G q.1 q.2) :=
    ((continuous_fst.comp (hzc.comp continuous_fst))).prodMk (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_snd).mul
        ((continuous_snd.comp (hzc.comp continuous_fst)).sub continuous_const)))
  have hGW : ∀ l ∈ Metric.closedBall (0 : ℂ) ε, ∀ r ∈ Icc (0 : ℝ) 1, G l r ∈ W :=
    fun l hl r hr => hcb hl r hr
  let F : ℂ → ℝ → ℂ := fun l r => α (G l r) * ((z l).2 - c)
  let F' : ℂ → ℝ → ℂ := fun l r =>
    fderiv ℂ α (G l r) (v.1, (r : ℂ) * v.2) * ((z l).2 - c) + α (G l r) * v.2
  have hfd : AnalyticOnNhd ℂ (fderiv ℂ α) W := hα.fderiv
  have hF'c : ContinuousOn (fun q : ℂ × ℝ => F' q.1 q.2)
      (Metric.closedBall (0 : ℂ) ε ×ˢ Icc (0 : ℝ) 1) := by
    intro q hq
    have hm := hGW q.1 hq.1 q.2 hq.2
    have h1 : ContinuousAt (fun q : ℂ × ℝ => fderiv ℂ α (G q.1 q.2)) q :=
      (hfd _ hm).continuousAt.comp_of_eq hGc.continuousAt rfl
    have h2 : ContinuousAt (fun q : ℂ × ℝ => α (G q.1 q.2)) q :=
      (hα _ hm).continuousAt.comp_of_eq hGc.continuousAt rfl
    have hv : Continuous (fun q : ℂ × ℝ => ((v.1, (q.2 : ℂ) * v.2) : (Fin 10 → ℂ) × ℂ)) :=
      continuous_const.prodMk ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have h3 : Continuous (fun q : ℂ × ℝ => (z q.1).2 - c) :=
      (continuous_snd.comp (hzc.comp continuous_fst)).sub continuous_const
    exact (((h1.clm_apply hv.continuousAt).mul h3.continuousAt).add
      (h2.mul continuousAt_const)).continuousWithinAt
  have hFc : ∀ l ∈ Metric.closedBall (0 : ℂ) ε, ContinuousOn (F l) (Icc (0 : ℝ) 1) := by
    intro l hl r hr
    have hm := hGW l hl r hr
    have hc : Continuous (fun r : ℝ => G l r) :=
      continuous_const.prodMk (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
    exact (((hα _ hm).continuousAt.comp_of_eq hc.continuousAt rfl).mul
      continuousAt_const).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ε |>.prod isCompact_Icc).exists_bound_of_continuousOn
    hF'c
  have hIoc : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (F := F) (F' := F') (x₀ := 0)
    (bound := fun _ => M) (Metric.closedBall_mem_nhds 0 hε)
    (Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 hε) fun l hl => ?_) ?_ ?_ ?_
    intervalIntegrable_const ?_
  · have h0 : z 0 = p := by simp [hz]
    have := key.2
    simp only [F', G, h0] at this
    exact this
  · rw [hIoc]
    exact ((hFc l hl).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact (hFc 0 (Metric.mem_closedBall_self hε.le)).intervalIntegrable_of_Icc zero_le_one
  · rw [hIoc]
    have hc : ContinuousOn (fun r : ℝ => F' 0 r) (Icc (0 : ℝ) 1) :=
      hF'c.comp (f := fun r : ℝ => ((0 : ℂ), r)) (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨Metric.mem_closedBall_self hε.le, hr⟩)
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Filter.Eventually.of_forall fun r hr l hl => ?_
    rw [hIoc] at hr
    exact hM (l, r) ⟨hl, Ioc_subset_Icc_self hr⟩
  · refine Filter.Eventually.of_forall fun r hr l hl => ?_
    rw [hIoc] at hr
    have hm := hGW l hl r (Ioc_subset_Icc_self hr)
    have hz' : HasDerivAt z v l := by
      have := ((hasDerivAt_id l).smul_const v).const_add p
      simpa [hz] using this
    have h1 : HasDerivAt (fun l => (z l).1) v.1 l :=
      (hasFDerivAt_fst (𝕜 := ℂ) (p := z l)).comp_hasDerivAt l hz'
    have h2 : HasDerivAt (fun l => (z l).2) v.2 l :=
      (hasFDerivAt_snd (𝕜 := ℂ) (p := z l)).comp_hasDerivAt l hz'
    have hG : HasDerivAt (fun l => G l r) (v.1, (r : ℂ) * v.2) l :=
      h1.prodMk (((h2.sub_const c).const_mul (r : ℂ)).const_add c)
    have hαG := (hα _ hm).differentiableAt.hasFDerivAt.comp_hasDerivAt l hG
    exact hαG.mul (h2.sub_const c)

end B66gSegAnalytic

section B66gPeriodsNear

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

/-- The period of `θ` along a moving polygon, as a sum of segment integrals of its chart
coefficients. -/
def b66g_perTerm (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (D : b66g_Poly R) (u : Fin 10 → ℂ) : ℂ :=
  ∑ k ∈ Finset.range D.N, b66g_segInt (fun w => b66g_relCoef R θ (D.a k) (u, w)) (D.c k) (D.E u k)

theorem b66g_period_poly (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    {u : b6t_polydisc mr_base} (hu : u.val ∈ U) (D : b66g_Poly R) (hD : D.Valid u) :
    b3_period ℂ (rf8_fibre R.C u) (D.smoothLoop hD)
        (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ u) =
      b66g_perTerm R θ D u.val := by
  rw [D.period_eq hD _ (fun k w => b66g_relCoef R θ (D.a k) (u.val, w))
    (fun k y hy v => b66g_relCoef_spec R θ (D.a k) u y hu hy v) (fun k => ?_)]
  · rfl
  · intro w hw
    have hm : (u.val, w) ∈ (R.atlas.A (D.a k)).target ∩
        Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) := ⟨hw, u.property, hu⟩
    exact ((b66g_relCoef_analytic R hU θ (D.a k) _ hm).continuousAt.comp_of_eq
      (f := fun w : ℂ => (u.val, w)) (continuous_const.prodMk continuous_id).continuousAt
      rfl).continuousWithinAt

variable {s t : b6t_polydisc mr_base} {n : ℕ} {B : Module.Basis (Fin n) ℤ (b66g_Homology R s)}

/-- Near `t`, the transported periods are finite sums of segment integrals along the moving
representatives. -/
theorem b66g_periods_near (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (P : b66g_Rep R s t B) :
    ∀ᶠ u in 𝓝 t.val, b66g_periods R s B θ u =
      fun i => ∑ j, (P.f i j : ℂ) * b66g_perTerm R θ (P.D i j) u := by
  have h1 : ∀ᶠ w in 𝓝 t.val, w ∈ b6t_polydisc mr_base ∩ U :=
    ((rf5_polydisc_isOpen mr_base).inter hU).mem_nhds ⟨t.property, ht⟩
  have h2 : ∀ᶠ w in 𝓝 t.val, ∀ i j, ∃ h : w ∈ b6t_polydisc mr_base, (P.D i j).Valid ⟨w, h⟩ :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      (P.D i j).valid_eventually (P.hv i j)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
  filter_upwards [Metric.ball_mem_nhds t.val hε] with u hu
  obtain ⟨⟨hup, huU⟩, -⟩ := hball hu
  have hline : ∀ s' ∈ Icc (0 : ℝ) 1, b66g_Poly.lineP t.val u s' ∈ Metric.ball t.val ε := by
    intro s' hs'
    have hc := (convex_ball t.val ε).add_smul_sub_mem (Metric.mem_ball_self hε) hu hs'
    simpa [b66g_Poly.lineP, Complex.coe_smul] using hc
  lift u to b6t_polydisc mr_base using hup
  funext i
  have hdef : b66g_periods R s B θ u.val i =
      (R.P u (b6m_H1Equiv (b6m_transport mr_base R.C s u) (B i))).val
        (b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ u) := by
    change b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) R.P θ s
      (B i) u.val = _
    unfold b63e_periodFunction
    rw [dite_eq_left_of_eq_true (eq_true u.property)]
  have hvu : ∀ j, (P.D i j).Valid u := fun j => by
    obtain ⟨h, hv⟩ := (hball hu).2 i j
    exact hv
  have hcls : ∀ j, b6m_H1Equiv (b6m_transport mr_base R.C t u)
      (b6m_loopClass (rf8_fibre R.C t) ((P.D i j).smoothLoop (P.hv i j))) =
      b6m_loopClass (rf8_fibre R.C u) ((P.D i j).smoothLoop (hvu j)) := by
    intro j
    exact ((P.D i j).loopClass_transport (fun s' hs' => (hball (hline s' hs')).2 i j)
      (P.hv i j) (hvu j)).symm
  rw [hdef, b66g_H1Equiv_trans R s t u (B i), ← P.hrep i, map_sum]
  simp only [map_sum, AddSubgroup.val_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcls' : b6m_H1Equiv (b6m_transport mr_base R.C t u)
      (P.f i j • b6m_loopClass (rf8_fibre R.C t) ((P.D i j).smoothLoop (P.hv i j))) =
      P.f i j • b6m_loopClass (rf8_fibre R.C u) ((P.D i j).smoothLoop (hvu j)) := by
    rw [← hcls j]
    exact map_zsmul _ _ _
  have hP' : R.P u (P.f i j • b6m_loopClass (rf8_fibre R.C u) ((P.D i j).smoothLoop (hvu j))) =
      P.f i j • b3_latticePeriod ℂ (rf8_fibre R.C u) ((P.D i j).smoothLoop (hvu j)) := by
    rw [← R.hP u]
    exact map_zsmul _ _ _
  rw [hcls', hP']
  change ((P.f i j • b3_latticePeriod ℂ (rf8_fibre R.C u) ((P.D i j).smoothLoop (hvu j)) :
    b3_periodLattice ℂ (rf8_fibre R.C u)) : b3_HolForm ℂ (rf8_fibre R.C u) → ℂ) _ = _
  rw [AddSubgroup.coe_zsmul, Pi.smul_apply, zsmul_eq_mul]
  congr 1
  exact b66g_period_poly R hU θ huU (P.D i j) _

end B66gPeriodsNear

section B66gPerDeriv

/-- Evaluation of the line derivative of a segment integral. -/
theorem b66g_line_integral_eval {W : Set ((Fin 10 → ℂ) × ℂ)}
    {α : (Fin 10 → ℂ) × ℂ → ℂ} (hα : AnalyticOnNhd ℂ α W) (c : ℂ) (t₀ : Fin 10 → ℂ) (e : ℂ)
    (hseg : ∀ r ∈ Icc (0 : ℝ) 1, (t₀, c + (r : ℂ) * (e - c)) ∈ W) (h : Fin 10 → ℂ) (δ : ℂ) :
    ∫ r in (0 : ℝ)..1, (fderiv ℂ α (t₀, c + (r : ℂ) * (e - c)) (h, (r : ℂ) * δ) * (e - c) +
        α (t₀, c + (r : ℂ) * (e - c)) * δ) =
      b66g_segInt (fun w => fderiv ℂ α (t₀, w) (h, 0)) c e + α (t₀, e) * δ := by
  set w : ℝ → (Fin 10 → ℂ) × ℂ := fun r => (t₀, c + (r : ℂ) * (e - c)) with hw
  have hwc : Continuous w :=
    continuous_const.prodMk (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hfd : AnalyticOnNhd ℂ (fderiv ℂ α) W := hα.fderiv
  have hcF : ∀ r ∈ Icc (0 : ℝ) 1, ContinuousAt (fun r => fderiv ℂ α (w r)) r := fun r hr =>
    (hfd _ (hseg r hr)).continuousAt.comp_of_eq hwc.continuousAt rfl
  have hcα : ∀ r ∈ Icc (0 : ℝ) 1, ContinuousAt (fun r => α (w r)) r := fun r hr =>
    (hα _ (hseg r hr)).continuousAt.comp_of_eq hwc.continuousAt rfl
  have hsplit : ∀ r : ℝ, fderiv ℂ α (w r) (h, (r : ℂ) * δ) =
      fderiv ℂ α (w r) (h, 0) + (r : ℂ) * δ * fderiv ℂ α (w r) (0, 1) := by
    intro r
    have : ((h, (r : ℂ) * δ) : (Fin 10 → ℂ) × ℂ) = (h, 0) + ((r : ℂ) * δ) • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  let A : ℝ → ℂ := fun r => fderiv ℂ α (w r) (h, 0) * (e - c)
  let Bf : ℝ → ℂ := fun r => (r : ℂ) * fderiv ℂ α (w r) (0, 1) * (e - c) + α (w r)
  have hint : ∀ r : ℝ, fderiv ℂ α (w r) (h, (r : ℂ) * δ) * (e - c) + α (w r) * δ = A r + δ * Bf r := by
    intro r
    rw [hsplit r]
    simp only [A, Bf]
    ring
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    intro r hr
    exact (((hcF r hr).clm_apply continuousAt_const).mul continuousAt_const).continuousWithinAt
  have hBc : ∀ r ∈ Icc (0 : ℝ) 1, ContinuousAt Bf r := fun r hr =>
    (((Complex.continuous_ofReal.continuousAt.mul ((hcF r hr).clm_apply continuousAt_const)).mul
      continuousAt_const).add (hcα r hr))
  have hBi : IntervalIntegrable Bf MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact fun r hr => (hBc r hr).continuousWithinAt
  have hB : ∫ r in (0 : ℝ)..1, Bf r = α (t₀, e) := by
    have hd : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => (r : ℂ) * α (w r)) (Bf r) r := by
      intro r hr
      rw [uIcc_of_le zero_le_one] at hr
      have hwr : HasDerivAt w ((0 : Fin 10 → ℂ), e - c) r := by
        have h2 : HasDerivAt (fun r : ℝ => c + (r : ℂ) * (e - c)) (1 * (e - c)) r :=
          ((hasDerivAt_id r).ofReal_comp.mul_const (e - c)).const_add c
        rw [one_mul] at h2
        exact (hasDerivAt_const r t₀).prodMk h2
      have hmem : w r ∈ W := by rw [hw]; exact hseg r hr
      have hαw := ((hα _ hmem).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r hwr
      have hr' : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
      have := hr'.mul hαw
      have e1 : ((0 : Fin 10 → ℂ), e - c) = (e - c) • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
        ext <;> simp
      convert this using 1
      · rfl
      · rw [ContinuousLinearMap.coe_restrictScalars', e1, map_smul, smul_eq_mul]
        simp only [Bf, Function.comp_apply]
        ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hBi]
    simp [hw]
  rw [intervalIntegral.integral_congr (fun r _ => hint r), intervalIntegral.integral_add hAi
    (hBi.const_mul δ), intervalIntegral.integral_const_mul, hB, mul_comm δ]
  rfl

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

theorem b66g_E_analytic {D : b66g_Poly R} {t : b6t_polydisc mr_base} (hD : D.Valid t) (k : ℤ) :
    AnalyticAt ℂ (fun u => D.E u k) t.val := by
  have hm : (t.val, D.c (k + 1)) ∈ ((R.atlas.A (D.a (k + 1))).symm.trans (R.atlas.A (D.a k))).source := by
    refine ⟨(hD k).2.1, ?_⟩
    have := (hD k).2.2
    rwa [b66g_inv_val R t (D.a (k + 1)) (hD k).2.1] at this
  exact (b66k_transition_analytic R _ _ _ hm).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl

theorem b66g_tube_mem {t : b6t_polydisc mr_base} (ht : t.val ∈ U) {D : b66g_Poly R}
    (hD : D.Valid t) (k : ℤ) :
    (t.val, D.E t.val k) ∈ b66g_tube ((R.atlas.A (D.a k)).target ∩
      Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U)) (D.c k) :=
  fun r hr => ⟨(hD k).1 r hr, t.property, ht⟩

theorem b66g_perTerm_term (hU : IsOpen U) {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    {D : b66g_Poly R} (hD : D.Valid t) (k : ℤ) (h : Fin 10 → ℂ) :
    AnalyticAt ℂ (fun u => b66g_segInt (fun w => b66g_relCoef R θ (D.a k) (u, w)) (D.c k)
      (D.E u k)) t.val ∧
    fderiv ℂ (fun u => b66g_segInt (fun w => b66g_relCoef R θ (D.a k) (u, w)) (D.c k)
      (D.E u k)) t.val h =
      b66g_segInt (fun w => fderiv ℂ (b66g_relCoef R θ (D.a k)) (t.val, w) (h, 0)) (D.c k)
          (D.E t.val k) +
        b66g_relCoef R θ (D.a k) (t.val, D.E t.val k) * fderiv ℂ (fun u => D.E u k) t.val h := by
  set α := b66g_relCoef R θ (D.a k)
  have hWo := b66g_relCoef_open R hU (D.a k)
  have hα := b66g_relCoef_analytic R hU θ (D.a k)
  set Ψ : (Fin 10 → ℂ) × ℂ → ℂ := fun z => b66g_segInt (fun w => α (z.1, w)) (D.c k) z.2
  set g : (Fin 10 → ℂ) → (Fin 10 → ℂ) × ℂ := fun u => (u, D.E u k)
  have hmem := b66g_tube_mem R ht hD k
  have hΨ : AnalyticAt ℂ Ψ (g t.val) := b66g_segInt_analytic hWo hα (D.c k) _ hmem
  have hE := b66g_E_analytic R hD k
  have hgd : HasFDerivAt g ((ContinuousLinearMap.id ℂ _).prod
      (fderiv ℂ (fun u => D.E u k) t.val)) t.val :=
    (hasFDerivAt_id _).prodMk hE.differentiableAt.hasFDerivAt
  have hfun : (fun u => b66g_segInt (fun w => α (u, w)) (D.c k) (D.E u k)) = Ψ ∘ g := rfl
  refine ⟨hfun ▸ hΨ.comp_of_eq (analyticAt_id.prod hE) rfl, ?_⟩
  have hcomp := hΨ.differentiableAt.hasFDerivAt.comp t.val hgd
  rw [hfun, hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq]
  set v : (Fin 10 → ℂ) × ℂ := (h, fderiv ℂ (fun u => D.E u k) t.val h)
  have hline1 := b66g_segInt_hasDerivAt_line hWo hα (D.c k) (v := v) hmem
  have hl : HasDerivAt (fun l : ℂ => g t.val + l • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add (g t.val)
    simpa using this
  have hline2 : HasDerivAt (fun l : ℂ => Ψ (g t.val + l • v)) (fderiv ℂ Ψ (g t.val) v) 0 :=
    hΨ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  rw [hline2.unique hline1]
  exact b66g_line_integral_eval hα (D.c k) t.val (D.E t.val k) hmem h _

theorem b66g_perTerm_deriv (hU : IsOpen U) {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    {D : b66g_Poly R} (hD : D.Valid t) (h : Fin 10 → ℂ) :
    AnalyticAt ℂ (b66g_perTerm R θ D) t.val ∧
    fderiv ℂ (b66g_perTerm R θ D) t.val h = ∑ k ∈ Finset.range D.N,
      (b66g_segInt (fun w => fderiv ℂ (b66g_relCoef R θ (D.a k)) (t.val, w) (h, 0)) (D.c k)
          (D.E t.val k) +
        b66g_relCoef R θ (D.a k) (t.val, D.E t.val k) * fderiv ℂ (fun u => D.E u k) t.val h) := by
  have hfun : b66g_perTerm R θ D = fun u => ∑ k ∈ Finset.range D.N,
      b66g_segInt (fun w => b66g_relCoef R θ (D.a k) (u, w)) (D.c k) (D.E u k) := rfl
  have han : ∀ k ∈ Finset.range D.N, AnalyticAt ℂ (fun u => b66g_segInt
      (fun w => b66g_relCoef R θ (D.a k) (u, w)) (D.c k) (D.E u k)) t.val :=
    fun k _ => (b66g_perTerm_term R hU ht θ hD k h).1
  refine ⟨hfun ▸ Finset.analyticAt_fun_sum _ han, ?_⟩
  rw [hfun, fderiv_fun_sum (fun k hk => (han k hk).differentiableAt)]
  simp only [sum_apply]
  exact Finset.sum_congr rfl fun k _ => (b66g_perTerm_term R hU ht θ hD k h).2

end B66gPerDeriv

section B66gLiftLaw

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)}

/-- Near a point of an overlap, the chart coefficients of a relative form obey the
transformation law of one-forms. -/
theorem b66g_relCoef_law (hU : IsOpen U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (a b : b66k_Index R)
    {p₀ : (Fin 10 → ℂ) × ℂ} (hp₀ : p₀ ∈ (R.atlas.A a).target)
    (hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source)
    (hp₀U : p₀.1 ∈ b6t_polydisc mr_base ∩ U) :
    ∀ᶠ p in 𝓝 p₀, b66g_relCoef R θ a p =
      b66g_relCoef R θ b (p.1, b66k_transition R a b p) *
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
  set x := b66g_inv R u a p.2
  have hxv : x.val = (R.atlas.A a).symm p := b66g_inv_val R u a hd
  have hxa : x.val ∈ (R.atlas.A a).source := b66g_inv_mem R u a hd
  have hxb : x.val ∈ (R.atlas.A b).source := by rw [hxv]; exact hpb
  have h1 := b66g_relCoef_spec R θ a u x hpU.2 hxa 1
  have h2 := b66g_relCoef_spec R θ b u x hpU.2 hxb 1
  have h3 := b66g_slice_change R u a b x hxa hxb 1
  have hsa : b66g_slice R u a x = p.2 := b66g_slice_inv R u a hd
  have hsb : b66g_slice R u b x = b66k_transition R a b p := by
    change (R.atlas.A b x.val).2 = _
    rw [hxv]
    rfl
  have hv : b66k_vertical R u a b x.val.2 = fderiv ℂ (b66k_transition R a b) p (0, 1) := by
    unfold b66k_vertical
    rw [← b66g_fibre_val R u x, hxv, (R.atlas.A a).right_inv hpa]
  rw [h1, hsa, h3, hsb, hv] at h2
  have hne := b66g_sliceD_one_ne R u a x hxa
  have := mul_right_cancel₀ hne (h2.trans (mul_assoc _ _ _).symm)
  exact this

/-- The parameter derivative of the chart coefficients of `θ` is a lift of the contraction of
the Kodaira–Spencer cocycle with the form `q` that `θ` restricts to at `t`. -/
theorem b66g_isLift_deriv (hU : IsOpen U) {t : b6t_polydisc mr_base} (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    (h : Fin 10 → ℂ) :
    b66g_IsLift R t (b66g_contract R q (b66k_cocycle R t h))
      (fun a w => fderiv ℂ (b66g_relCoef R θ a) (t.val, w) (h, 0)) := by
  have hW : ∀ a w, w ∈ b66k_domain R t a → (t.val, w) ∈ (R.atlas.A a).target ∩
      Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) := fun a w hw => ⟨hw, t.property, ht⟩
  refine ⟨fun a w hw => ?_, fun a b w hw => ?_⟩
  · have hfd := (b66g_relCoef_analytic R hU θ a).fderiv _ (hW a w hw)
    have hin : AnalyticAt ℂ (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) w :=
      analyticAt_const.prod analyticAt_id
    exact (ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).analyticAt _ |>.comp_of_eq
      (hfd.comp_of_eq hin rfl) rfl
  · set p₀ : (Fin 10 → ℂ) × ℂ := (t.val, w)
    set τ := b66k_transition R a b
    obtain ⟨hm, hτd, -, -⟩ := b66g_transition_mem R t a b w hw
    have hτa : AnalyticAt ℂ τ p₀ := b66k_transition_analytic R a b p₀ hm
    have hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source := hm.2
    set αa := b66g_relCoef R θ a
    set αb := b66g_relCoef R θ b
    set e := τ p₀
    have hαa := b66g_relCoef_analytic R hU θ a
    have hαb := b66g_relCoef_analytic R hU θ b
    have hWb : (t.val, e) ∈ (R.atlas.A b).target ∩ Prod.fst ⁻¹' (b6t_polydisc mr_base ∩ U) :=
      hW b e hτd
    -- the transformation law and its derivative in the parameter direction
    have hlaw := b66g_relCoef_law R hU θ a b hm.1 hp₀b ⟨t.property, ht⟩
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
      filter_upwards [b66g_overlap_eventually R t a b w hw] with z hz
      have hzb : (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A b).source :=
        hz.1.2
      have hqb := b66g_relCoef_base R ht θ q hq b _ hzb
      have hsl : b66g_slice R t b (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2) =
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

end B66gLiftLaw

section B66gPeriodsDeriv

variable (R : rf8_SharedFamily) {U : Set (Fin 10 → ℂ)} {s t : b6t_polydisc mr_base} {n : ℕ}
  {B : Module.Basis (Fin n) ℤ (b66g_Homology R s)}

theorem b66g_endpoint_term (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    {D : b66g_Poly R} (hD : D.Valid t) (k : ℤ) (h : Fin 10 → ℂ) :
    b66g_relCoef R θ (D.a k) (t.val, D.E t.val k) * fderiv ℂ (fun u => D.E u k) t.val h =
      b66g_contract R q (b66k_cocycle R t h) (D.a (k + 1)) (D.a k) (D.V t (k + 1)).val.2 := by
  have hVv : (D.V t (k + 1)).val = (t, (D.V t (k + 1)).val.2) := b66g_fibre_val R t _
  have hm1 : (t, (D.V t (k + 1)).val.2) ∈ (R.atlas.A (D.a (k + 1))).source := by
    rw [← hVv]; exact b66g_inv_mem R t (D.a (k + 1)) (hD k).2.1
  have hm0 : (t, (D.V t (k + 1)).val.2) ∈ (R.atlas.A (D.a k)).source := by
    rw [← hVv]; exact (hD k).2.2
  have hA : R.atlas.A (D.a (k + 1)) (t, (D.V t (k + 1)).val.2) = (t.val, D.c (k + 1)) := by
    rw [← hVv]
    change R.atlas.A _ (b66g_inv R t (D.a (k + 1)) (D.c (k + 1))).val = _
    rw [b66g_inv_val R t (D.a (k + 1)) (hD k).2.1, (R.atlas.A (D.a (k + 1))).right_inv
      (hD k).2.1]
  have hq0 := b66g_relCoef_base R ht θ q hq (D.a k) (D.V t (k + 1)) (hD k).2.2
  rw [← D.E_eq_slice hD k] at hq0
  have hEd : fderiv ℂ (fun u => D.E u k) t.val h =
      fderiv ℂ (b66k_transition R (D.a (k + 1)) (D.a k)) (t.val, D.c (k + 1)) (h, 0) := by
    have hm : (t.val, D.c (k + 1)) ∈
        ((R.atlas.A (D.a (k + 1))).symm.trans (R.atlas.A (D.a k))).source := by
      refine ⟨(hD k).2.1, ?_⟩
      have := (hD k).2.2
      rwa [b66g_inv_val R t (D.a (k + 1)) (hD k).2.1] at this
    have htr := (b66k_transition_analytic R _ _ _ hm).differentiableAt.hasFDerivAt
    have hl : HasFDerivAt (fun u : Fin 10 → ℂ => ((u, D.c (k + 1)) : (Fin 10 → ℂ) × ℂ))
        ((ContinuousLinearMap.id ℂ _).prod 0) t.val :=
      (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
    have := (htr.comp t.val hl).fderiv
    rw [show (fun u => D.E u k) = b66k_transition R (D.a (k + 1)) (D.a k) ∘
      (fun u : Fin 10 → ℂ => ((u, D.c (k + 1)) : (Fin 10 → ℂ) × ℂ)) from rfl, this]
    rfl
  have hov : (t, (D.V t (k + 1)).val.2) ∈
      (R.atlas.A (D.a (k + 1))).source ∩ (R.atlas.A (D.a k)).source := ⟨hm1, hm0⟩
  rw [hq0, hEd]
  simp only [b66g_contract, b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk, hov, ↓reduceIte, hA]

/-- Differentiability of the transported periods and their derivative as a chain period. -/
theorem b66g_periods_deriv (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U) (q : b66g_Coeff R)
    (hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v))
    (P : b66g_Rep R s t B) :
    DifferentiableAt ℂ (b66g_periods R s B θ) t.val ∧ ∀ h : Fin 10 → ℂ,
      fderiv ℂ (b66g_periods R s B θ) t.val h =
        b66g_cdrVec P (fun a w => fderiv ℂ (b66g_relCoef R θ a) (t.val, w) (h, 0))
          (b66g_contract R q (b66k_cocycle R t h)) := by
  set V : (Fin 10 → ℂ) → Fin n → ℂ := fun u i => ∑ j, (P.f i j : ℂ) * b66g_perTerm R θ (P.D i j) u
  have hnear : b66g_periods R s B θ =ᶠ[𝓝 t.val] V := b66g_periods_near R hU ht θ P
  have hVi : ∀ i, DifferentiableAt ℂ (fun u => V u i) t.val := fun i =>
    DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul
      ((b66g_perTerm_deriv R hU ht θ (P.hv i j) 0).1.differentiableAt)
  have hV : DifferentiableAt ℂ V t.val := differentiableAt_pi.2 hVi
  refine ⟨hnear.differentiableAt_iff.2 hV, fun h => ?_⟩
  rw [hnear.fderiv_eq]
  funext i
  rw [fderiv_pi (fun i => hVi i)]
  change fderiv ℂ (fun u => V u i) t.val h = _
  have hfun : (fun u => V u i) = fun u => ∑ j, (P.f i j : ℂ) * b66g_perTerm R θ (P.D i j) u := rfl
  have hdj : ∀ j ∈ (Finset.univ : Finset (Fin (P.m i))), DifferentiableAt ℂ
      (fun u => (P.f i j : ℂ) * b66g_perTerm R θ (P.D i j) u) t.val := fun j _ =>
    (differentiableAt_const _).mul ((b66g_perTerm_deriv R hU ht θ (P.hv i j) 0).1.differentiableAt)
  rw [hfun, fderiv_fun_sum hdj]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_const_mul ((b66g_perTerm_deriv R hU ht θ (P.hv i j) 0).1.differentiableAt),
    smul_apply, smul_eq_mul, (b66g_perTerm_deriv R hU ht θ (P.hv i j) h).2]
  congr 1
  unfold b66g_cdr
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [b66g_endpoint_term R ht θ q hq (P.hv i j) k h]

end B66gPeriodsDeriv

end HodgeLean.Foundations.Program
