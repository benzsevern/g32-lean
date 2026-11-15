import HodgeLean.Foundations.Program.GriffithsTransversalityDefs
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.LogDeriv

noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b66g_vertical_comp (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b c : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66k_vertical R t a c x = b66k_vertical R t b c x * b66k_vertical R t a b x := by
  let u := R.atlas.A a (t, x)
  let w := R.atlas.A b (t, x)
  have hab : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨(R.atlas.A a).map_source ha, ?_⟩
    change (R.atlas.A a).symm u ∈ (R.atlas.A b).source
    simpa only [u, (R.atlas.A a).left_inv ha] using hb
  have hbc : w ∈ ((R.atlas.A b).symm.trans (R.atlas.A c)).source := by
    refine ⟨(R.atlas.A b).map_source hb, ?_⟩
    change (R.atlas.A b).symm w ∈ (R.atlas.A c).source
    simpa only [w, (R.atlas.A b).left_inv hb] using hc
  have dab := (b66k_transition_analytic R a b u hab).differentiableAt
  have dbc := (b66k_transition_analytic R b c w hbc).differentiableAt
  let T : ((Fin 10 → ℂ) × ℂ) → ((Fin 10 → ℂ) × ℂ) :=
    fun v => (v.1, b66k_transition R a b v)
  have hT : T u = w := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam b _ hb).symm
    · exact congrArg (fun y => (R.atlas.A b y).2) ((R.atlas.A a).left_inv ha)
  have he : (fun v => b66k_transition R b c (T v)) =ᶠ[𝓝 u]
      b66k_transition R a c := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hab]
      with v hv
    have ht : T v = R.atlas.A b ((R.atlas.A a).symm v) := by
      apply Prod.ext
      · exact (b6a_transition_fst mr_base R.C R.atlas.A R.atlas.hparam a b v hv).symm
      · rfl
    change (R.atlas.A c ((R.atlas.A b).symm (T v))).2 = _
    rw [ht]
    rw [(R.atlas.A b).left_inv (x := (R.atlas.A a).symm v) hv.2]
    rfl
  have dbc' : HasFDerivAt (b66k_transition R b c)
      (fderiv ℂ (b66k_transition R b c) w) (T u) := by
    rw [hT]
    exact dbc.hasFDerivAt
  have hder := dbc'.comp u (hasFDerivAt_fst.prodMk dab.hasFDerivAt)
  have hf := (hder.congr_of_eventuallyEq he.symm).fderiv
  have hl (L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ) (q : ℂ) :
      L (0, q) = q * L (0, 1) := by
    have hp : ((0 : Fin 10 → ℂ), q) = q • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
      simp
    rw [hp, map_smul]
    rfl
  simp only [b66k_vertical]
  change fderiv ℂ (b66k_transition R a c) u (0, 1) = _
  rw [hf]
  change fderiv ℂ (b66k_transition R b c) w
    (0, fderiv ℂ (b66k_transition R a b) u (0, 1)) = _
  rw [hl, mul_comm]

theorem b66g_overlap_eventually (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    ∀ᶠ w in 𝓝 z,
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∧
      R.atlas.A a (t, ((R.atlas.A a).symm (t.val, w)).2) = (t.val, w) ∧
      (R.atlas.A b (t, ((R.atlas.A a).symm (t.val, w)).2)).2 =
        b66k_transition R a b (t.val, w) := by
  have hi := b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hopen := ((R.atlas.A a).symm.trans (R.atlas.A b)).open_source
  have hev := (continuous_const.prodMk continuous_id).continuousAt
    (hopen.mem_nhds hm)
  filter_upwards [hev] with w hw
  change (t.val, w) ∈ (R.atlas.A a).target ∧
    (R.atlas.A a).symm (t.val, w) ∈ (R.atlas.A b).source at hw
  have hiw := b66k_inverse_slice R t a w hw.1
  rw [hiw]
  exact ⟨⟨(R.atlas.A a).map_target hw.1, hw.2⟩, (R.atlas.A a).right_inv hw.1, rfl⟩

theorem b66g_transition_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source ∧
    b66k_transition R a b (t.val, z) ∈ b66k_domain R t b ∧
    AnalyticAt ℂ (fun w => b66k_transition R a b (t.val, w)) z ∧
    AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1)) z := by
  have hi := b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hd : ContDiffAt ℂ ω (b66k_transition R a b) (t.val, z) :=
    (b66k_transition_analytic R a b _ hm).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => fderiv ℂ (b66k_transition R a b) u (0, 1)) (t.val, z) :=
    (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
  refine ⟨hm, ?_, ?_, ?_⟩
  · have hy : (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source := hm.2
    change (t.val, (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).2) ∈ (R.atlas.A b).target
    have h1 : (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).1 = t.val := by
      rw [R.atlas.hparam b _ hy, b66k_inverse_parameter R a _ hz.1]
    convert (R.atlas.A b).map_source hy using 1
    exact Prod.ext h1.symm rfl
  · exact (b66k_transition_analytic R a b _ hm).comp
      (analyticAt_const.prod analyticAt_id)
  · exact (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt

theorem b66g_boundaries_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_boundaries R t ≤
      b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t) ∧
    b66g_scalarBoundaries R t ≤ b66g_scalarCycles R t := by
  constructor
  · refine Submodule.span_le.mpr ?_
    rintro c ⟨v, hv, rfl⟩
    constructor
    · apply Submodule.subset_span
      refine ⟨?_, ?_⟩
      · intro a b z hz
        obtain ⟨_, hdom, han, hvert⟩ := b66g_transition_mem R t a b z hz
        have h1 : AnalyticAt ℂ (fun w =>
            fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) * v a w -
              v b (b66k_transition R a b (t.val, w))) z :=
          (hvert.mul (hv a z hz.1)).sub (AnalyticAt.comp (f := fun w =>
            b66k_transition R a b (t.val, w)) (hv b _ hdom) han)
        apply h1.congr
        filter_upwards [b66g_overlap_eventually R t a b z hz] with w ⟨hmem, ha, hb⟩
        simp only [b66k_boundary, ite_eq_left hmem, b66k_vertical, ha, hb]
      · intro a b x hx
        simp only [b66k_boundary, ite_eq_right hx]
    · change b66k_differential R t (b66k_boundary R t v) = 0
      funext a b c x
      simp only [b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      split_ifs with hx
      · simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
            (R.atlas.A c).source from ⟨hx.1.1, hx.2⟩),
          ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩
            (R.atlas.A c).source from ⟨hx.1.2, hx.2⟩), ite_eq_left hx.1,
          b66g_vertical_comp R t a b c x hx.1.1 hx.1.2 hx.2]
        ring
      · rfl
  · refine Submodule.span_le.mpr ?_
    rintro c ⟨v, hv, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_, ?_⟩
    · intro a b z hz
      obtain ⟨_, hdom, han, _⟩ := b66g_transition_mem R t a b z hz
      have h1 : AnalyticAt ℂ (fun w =>
          v a w - v b (b66k_transition R a b (t.val, w))) z :=
        (hv a z hz.1).sub (AnalyticAt.comp (f := fun w =>
          b66k_transition R a b (t.val, w)) (hv b _ hdom) han)
      apply h1.congr
      filter_upwards [b66g_overlap_eventually R t a b z hz] with w ⟨hmem, ha, hb⟩
      simp only [b66g_scalarBoundary, ite_eq_left hmem, ha, hb]
    · intro a b x hx
      simp only [b66g_scalarBoundary, ite_eq_right hx]
    · intro a b c x ha hb hc
      simp only [b66g_scalarBoundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
          (R.atlas.A c).source from ⟨ha, hc⟩),
        ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩
          (R.atlas.A c).source from ⟨hb, hc⟩),
        ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
          (R.atlas.A b).source from ⟨ha, hb⟩)]
      ring

theorem b66g_slice_value (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    R.atlas.A a y.val = (t.val, (R.atlas.A a y.val).2) := by
  refine Prod.ext ?_ rfl
  rw [R.atlas.hparam a _ hy]
  exact congrArg Subtype.val y.property

theorem b66g_slice_coordinate_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun p : rf8_fibre R.C t => (R.atlas.A a p.val).2)
      {p | p.val ∈ (R.atlas.A a).source} ∧
    ∀ p : rf8_fibre R.C t, p.val ∈ (R.atlas.A a).source →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p ≠ 0 := by
  set F : rf8_fibre R.C t → ℂ := fun y => (R.atlas.A a y.val).2
  have hchart : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (R.atlas.A a) (R.atlas.A a).source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (R.atlas.hA a).2)
  have hsnd : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (Prod.snd : (Fin 10 → ℂ) × ℂ → ℂ) := contDiff_snd.contMDiff
  have hF : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F {p | p.val ∈ (R.atlas.A a).source} :=
    hsnd.comp_contMDiffOn (hchart.comp (R.hincl t).contMDiffOn (fun p hp => hp))
  refine ⟨hF, fun p hp hzero => ?_⟩
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have hFp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F p := hF.contMDiffAt (hopen.mem_nhds hp)
  let e := extChartAt 𝓘(ℂ, ℂ) p
  let g : ℂ → ℂ := F ∘ e.symm
  have hg : AnalyticAt ℂ g (e p) := by
    have h := (contMDiffAt_iff.mp hFp).2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
      modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h
    exact h.analyticAt
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e p) := by
    refine inter_mem (extChartAt_target_mem_nhds p) ?_
    apply (continuousAt_extChartAt_symm p).preimage_mem_nhds
    rw [extChartAt_to_inv p]
    exact hopen.mem_nhds hp
  have hinj : InjOn g (e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source}) := by
    intro w₁ hw₁ w₂ hw₂ hw
    have h1 := b66g_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66g_slice_value R t a (e.symm w₂) hw₂.2
    have hv : (e.symm w₁).val = (e.symm w₂).val := by
      apply (R.atlas.A a).injOn hw₁.2 hw₂.2
      rw [h1, h2]
      exact congrArg (fun z => (t.val, z)) hw
    have hy : e.symm w₁ = e.symm w₂ := Subtype.ext hv
    rw [← e.right_inv hw₁.1, ← e.right_inv hw₂.1, hy]
  apply rf8_deriv_ne_zero_of_injOn hU hg hinj
  have hm := (hFp.mdifferentiableAt (by simp)).mfderiv_abuse
  rw [hzero] at hm
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, range_id, fderivWithin_univ] at hm
  change fderiv ℂ (F ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) (extChartAt 𝓘(ℂ, ℂ) p p) 1 = 0
  rw [← hm]
  rfl

theorem b66g_forms_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    (∀ a, AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_domain R t a)) ∧
    (∀ a b x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      q a x = b66k_vertical R t a b x ^ m * q b x) ∧
    ∀ a x, (t, x) ∉ (R.atlas.A a).source → q a x = 0 := by
  induction hq using Submodule.span_induction with
  | mem q hq => exact hq
  | zero =>
    refine ⟨fun a z _ => analyticAt_const, fun _ _ _ _ _ => by simp, fun _ _ _ => rfl⟩
  | add q r _ _ hq hr =>
    refine ⟨fun a => (hq.1 a).add (hr.1 a), fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hq.2.1 a b x ha hb, hr.2.1 a b x ha hb]
      ring
    · simp only [Pi.add_apply]
      rw [hq.2.2 a x hx, hr.2.2 a x hx, add_zero]
  | smul k q _ hq =>
    refine ⟨fun a => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · exact (hq.1 a).const_smul (c := k)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hq.2.1 a b x ha hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hq.2.2 a x hx, mul_zero]

theorem b66g_holomorphic_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ b66k_holomorphicCochains R t) :
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b)) ∧
    ∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hu
  | zero => exact ⟨fun a b z _ => analyticAt_const, fun _ _ _ _ => rfl⟩
  | add u w _ _ hu hw =>
    refine ⟨fun a b => (hu.1 a b).add (hw.1 a b), fun a b x hx => ?_⟩
    simp only [Pi.add_apply]
    rw [hu.2 a b x hx, hw.2 a b x hx, add_zero]
  | smul k u _ hu =>
    refine ⟨fun a b => ?_, fun a b x hx => ?_⟩
    · exact (hu.1 a b).const_smul (c := k)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu.2 a b x hx, mul_zero]

theorem b66g_kernel_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ LinearMap.ker (b66k_differential R t))
    (a b c : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) (hc : (t, x) ∈ (R.atlas.A c).source) :
    u a c x = u b c x + b66k_vertical R t b c x * u a b x := by
  have h := congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hu) a) b) c) x
  simp only [b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩
      (R.atlas.A c).source from ⟨⟨ha, hb⟩, hc⟩)] at h
  linear_combination h

theorem b66g_chart_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (b : b66k_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) ∧
    ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x := by
  have h1 : R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) :=
    Prod.ext (R.atlas.hparam b _ hb) rfl
  refine ⟨h1, ?_⟩
  rw [← h1, (R.atlas.A b).left_inv hb]

theorem b66g_target_coefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t 1 a b)
    (hq : AnalyticOnNhd ℂ (fun z => q b ((R.atlas.A b).symm (t.val, z)).2)
      (b66k_domain R t b)) :
    AnalyticAt ℂ (fun w => q b ((R.atlas.A a).symm (t.val, w)).2) z := by
  obtain ⟨_, hdom, han, _⟩ := b66g_transition_mem R t a b z hz
  have h1 : AnalyticAt ℂ (fun w =>
      q b ((R.atlas.A b).symm (t.val, b66k_transition R a b (t.val, w))).2) z :=
    AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) (hq _ hdom) han
  apply h1.congr
  filter_upwards [b66g_overlap_eventually R t a b z hz] with w ⟨hmem, _, hb⟩
  rw [← hb, (b66g_chart_slice R t b _ hmem.2).2]

theorem b66g_contract_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) {u : b66k_Cochain R}
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)) :
    b66g_contract R q u ∈ b66g_scalarCycles R t := by
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 1 hq
  obtain ⟨hua, huz⟩ := b66g_holomorphic_spec R t hu.1
  apply Submodule.subset_span
  refine ⟨fun a b z hz => ?_, fun a b x hx => ?_, fun a b c x ha hb hc => ?_⟩
  · exact (b66g_target_coefficient R t q a b z hz (hqa b)).mul (hua a b z hz)
  · simp only [b66g_contract, huz a b x hx, mul_zero]
  · simp only [b66g_contract]
    rw [b66g_kernel_spec R t hu.2 a b c x ha hb hc, hql b c x hb hc, pow_one]
    ring

theorem b66g_contract_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) {u : b66k_Cochain R}
    (hu : u ∈ b66k_boundaries R t) :
    b66g_contract R q u ∈ b66g_scalarBoundaries R t := by
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 1 hq
  obtain ⟨v, hv, rfl⟩ := b66k_boundary_representation R t u hu
  apply Submodule.subset_span
  refine ⟨fun a z => q a ((R.atlas.A a).symm (t.val, z)).2 * v a z,
    fun a => (hqa a).mul (hv a), ?_⟩
  funext a b x
  simp only [b66g_contract, b66k_boundary, b66g_scalarBoundary]
  split_ifs with hx
  · rw [(b66g_chart_slice R t a x hx.1).2, (b66g_chart_slice R t b x hx.2).2,
      hql a b x hx.1 hx.2, pow_one]
    ring
  · exact mul_zero _

theorem b66g_cup_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (∃ C : b66k_cechH1 R t →ₗ[ℂ] (b66g_forms R t 1 →ₗ[ℂ] b66g_H1O R t),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (q : b66g_forms R t 1),
      (C c q).val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u)) ∧
    ∀ q r : b66g_forms R t 1, b66g_product R q.val r.val ∈ b66g_forms R t 2 := by
  constructor
  · let Z := b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)
    let Φ : Z →ₗ[ℂ] (b66g_forms R t 1 →ₗ[ℂ] b66g_H1O R t) :=
      LinearMap.mk₂ ℂ (fun (u : Z) (q : b66g_forms R t 1) =>
        (⟨(b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u.val),
          Submodule.mem_map_of_mem (b66g_contract_mem R t q.property u.property)⟩ :
            b66g_H1O R t))
        (fun u w q => by
          apply Subtype.ext
          change (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val (u.val + w.val)) =
            (b66g_scalarBoundaries R t).mkQ _ + (b66g_scalarBoundaries R t).mkQ _
          rw [← map_add]
          congr 1
          funext a b x
          simp only [b66g_contract, Pi.add_apply]
          ring)
        (fun k u q => by
          apply Subtype.ext
          change (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val (k • u.val)) =
            k • (b66g_scalarBoundaries R t).mkQ _
          rw [← map_smul]
          congr 1
          funext a b x
          simp only [b66g_contract, Pi.smul_apply, smul_eq_mul]
          ring)
        (fun u q r => by
          apply Subtype.ext
          change (b66g_scalarBoundaries R t).mkQ (b66g_contract R (q.val + r.val) u.val) =
            (b66g_scalarBoundaries R t).mkQ _ + (b66g_scalarBoundaries R t).mkQ _
          rw [← map_add]
          congr 1
          funext a b x
          simp only [b66g_contract, Pi.add_apply]
          ring)
        (fun k u q => by
          apply Subtype.ext
          change (b66g_scalarBoundaries R t).mkQ (b66g_contract R (k • q.val) u.val) =
            k • (b66g_scalarBoundaries R t).mkQ _
          rw [← map_smul]
          congr 1
          funext a b x
          simp only [b66g_contract, Pi.smul_apply, smul_eq_mul]
          ring)
    let f : Z →ₗ[ℂ] b66k_Quotient R t := (b66k_boundaries R t).mkQ ∘ₗ Z.subtype
    have hker : LinearMap.ker f ≤ LinearMap.ker Φ := by
      intro u hu
      have hb : u.val ∈ b66k_boundaries R t :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hu)
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro q
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero _).mpr (b66g_contract_boundary R t q.property hb)
    have hrange : LinearMap.range f = b66k_cechH1 R t := by
      simp only [f, LinearMap.range_comp, Submodule.range_subtype]
      rfl
    refine ⟨(LinearMap.ker f).liftQ Φ hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap, ?_⟩
    intro u hu c hc q
    have he : f.quotKerEquivRange.symm (LinearEquiv.ofEq _ _ hrange.symm c) =
        (LinearMap.ker f).mkQ ⟨u, hu⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      simp only [LinearEquiv.coe_ofEq_apply, Submodule.mkQ_apply,
        LinearMap.quotKerEquivRange_apply_mk]
      exact hc
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
      Submodule.liftQ_apply, Submodule.mkQ_apply]
    rfl
  · intro q r
    obtain ⟨hqa, hql, hqz⟩ := b66g_forms_spec R t 1 q.property
    obtain ⟨hra, hrl, hrz⟩ := b66g_forms_spec R t 1 r.property
    apply Submodule.subset_span
    refine ⟨fun a => (hqa a).mul (hra a), fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · simp only [b66g_product]
      rw [hql a b x ha hb, hrl a b x ha hb]
      ring
    · simp only [b66g_product, hqz a x hx, zero_mul]


/-- Fibre coordinate of a retained chart. -/
def b66g_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R) :
    rf8_fibre R.C t → ℂ := fun y => (R.atlas.A a y.val).2

/-- Derivative of the fibre coordinate of a retained chart. -/
def b66g_sliceD (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (p : rf8_fibre R.C t) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) p

/-- Derivative of a fibre chart. -/
def b66g_chartD (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x₀ y : rf8_fibre R.C t) :
    ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x₀) y

theorem b66g_clm_apply (L : ℂ →L[ℂ] ℂ) (v : ℂ) : L v = v * L 1 := by
  have : v = v • (1 : ℂ) := by simp
  conv_lhs => rw [this]
  rw [map_smul, smul_eq_mul]

theorem b66g_fibre_val (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (y : rf8_fibre R.C t) : y.val = (t, y.val.2) :=
  Prod.ext y.property rfl

theorem b66g_slice_contMDiffAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_slice R t a) y :=
  (b66g_slice_coordinate_aux R t a).1.contMDiffAt
    (((R.atlas.A a).open_source.preimage continuous_subtype_val).mem_nhds hy)

theorem b66g_slice_chart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (x₀ y : rf8_fibre R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (hya : y.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ∧
    deriv (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ≠ 0 ∧
    ∀ v : ℂ, b66g_sliceD R t a y v =
      deriv (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
        (extChartAt 𝓘(ℂ, ℂ) x₀ y) * b66g_chartD R t x₀ y v := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set h := b66g_slice R t a ∘ e.symm
  have hyt : e y ∈ e.target := e.map_source hy
  have hinv : e.symm (e y) = y := e.left_inv hy
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y) :=
    (contMDiffOn_extChartAt_symm x₀ (e y) hyt).contMDiffAt
      (extChartAt_target_mem_nhds' hyt)
  have hsl : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_slice R t a) (e.symm (e y)) := by
    rw [hinv]
    exact b66g_slice_contMDiffAt R t a y hya
  have hh : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω h (e y) := hsl.comp (e y) hsym
  have han : AnalyticAt ℂ h (e y) := (contMDiffAt_iff_contDiffAt.mp hh).analyticAt
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y) := by
    refine inter_mem (extChartAt_target_mem_nhds' hyt) ?_
    apply (continuousAt_extChartAt_symm'' hyt).preimage_mem_nhds
    rw [hinv]
    exact hopen.mem_nhds hya
  have hinj : InjOn h (e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source}) := by
    intro w₁ hw₁ w₂ hw₂ hw
    have h1 := b66g_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66g_slice_value R t a (e.symm w₂) hw₂.2
    have hv : (e.symm w₁).val = (e.symm w₂).val := by
      apply (R.atlas.A a).injOn hw₁.2 hw₂.2
      rw [h1, h2]
      exact congrArg (fun z => (t.val, z)) hw
    have hy' : e.symm w₁ = e.symm w₂ := Subtype.ext hv
    rw [← e.right_inv hw₁.1, ← e.right_inv hw₂.1, hy']
  refine ⟨han, rf8_deriv_ne_zero_of_injOn hU han hinj, fun v => ?_⟩
  have heq : b66g_slice R t a =ᶠ[𝓝 y] h ∘ e := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy'
    simp only [h, Function.comp_apply, e.left_inv hy']
  have hmd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) h (e y) :=
    mdifferentiableAt_iff_differentiableAt.mpr han.differentiableAt
  have hme : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℂ, ℂ)])
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) y
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv h (e y))).comp
        (b66g_chartD R t x₀ y)) :=
    (HasMFDerivAt.comp (g := h) (f := e) y
      han.differentiableAt.hasDerivAt.hasFDerivAt.hasMFDerivAt
      hme.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66g_sliceD
  rw [hH.mfderiv]
  exact mul_comm (b66g_chartD R t x₀ y v) _

theorem b66g_transition_hasDerivAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ)
    (hz : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    HasDerivAt (fun w => b66k_transition R a b (t.val, w))
      (fderiv ℂ (b66k_transition R a b) (t.val, z) (0, 1)) z := by
  have hd := (b66k_transition_analytic R a b _ hz).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (0, 1) z :=
    (hasDerivAt_const z t.val).prodMk (hasDerivAt_id z)
  exact hd.comp_hasDerivAt z hi

theorem b66g_slice_change (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (p : rf8_fibre R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source) (v : ℂ) :
    b66g_sliceD R t b p v = b66k_vertical R t a b p.val.2 * b66g_sliceD R t a p v := by
  set g : ℂ → ℂ := fun w => b66k_transition R a b (t.val, w)
  have hpa := b66g_slice_value R t a p ha
  have hz : (t.val, b66g_slice R t a p) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A b).source
      rw [← hpa, (R.atlas.A a).left_inv ha]
      exact hb
  have hg := b66g_transition_hasDerivAt R t a b _ hz
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66g_slice R t b =ᶠ[𝓝 p] g ∘ b66g_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A b y.val).2 =
      (R.atlas.A b ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2))).2
    rw [← b66g_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (b66g_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hg.differentiableAt
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) p :=
    (b66g_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t b) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (fderiv ℂ (b66k_transition R a b) (t.val, b66g_slice R t a p) (0, 1))).comp
        (b66g_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := g) (f := b66g_slice R t a) p hg.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66g_sliceD at hH ⊢
  rw [hH.mfderiv]
  have hv : fderiv ℂ (b66k_transition R a b) (t.val, b66g_slice R t a p) (0, 1) =
      b66k_vertical R t a b p.val.2 := by
    change _ = fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, p.val.2)) (0, 1)
    rw [← b66g_fibre_val R t p]
    exact congrArg (fun u => fderiv ℂ (b66k_transition R a b) u (0, 1)) hpa.symm
  rw [← hv]
  exact mul_comm (b66g_sliceD R t a p v) _

theorem b66g_slice_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source) :
    b66g_sliceD R t a p 1 ≠ 0 := by
  intro h0
  apply (b66g_slice_coordinate_aux R t a).2 p ha
  apply ContinuousLinearMap.ext
  intro (v : ℂ)
  have hz : b66g_sliceD R t a p = 0 :=
    ContinuousLinearMap.ext_ring (by rw [h0]; rfl)
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hz

/-- The differential on the fibre with given retained chart coefficients. -/
def b66g_toForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_Coeff R →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) where
  toFun q P := q P.proj.val P.proj.val.2 * b66g_sliceD R t P.proj.val P.proj P.2
  map_add' q r := by
    funext P
    simp only [Pi.add_apply]
    ring
  map_smul' c q := by
    funext P
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Retained chart coefficients of a differential on the fibre. -/
def b66g_ofForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) : b66g_Coeff R := fun a x =>
  if (t, x) ∈ (R.atlas.A a).source then
    θ ⟨(⟨(t, x), rfl⟩ : rf8_fibre R.C t),
      ((b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹ : ℂ)⟩ else 0

theorem b66g_lin_smul' {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ}
    (hlin : ∀ (x : X) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x : X) (c : ℂ)
    (w : TangentSpace 𝓘(ℂ, ℂ) x) :
    θ ⟨x, c • w⟩ = c * θ ⟨x, w⟩ := by
  have h0 : θ ⟨x, (0 : TangentSpace 𝓘(ℂ, ℂ) x)⟩ = 0 := by
    have := hlin x 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have := hlin x c w 0
  rw [h0, add_zero, add_zero] at this
  exact this

theorem b66g_lin_smul {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ}
    (hlin : ∀ (x : X) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x : X) (c w : ℂ) :
    θ ⟨x, c * w⟩ = c * θ ⟨x, w⟩ :=
  b66g_lin_smul' hlin x c w

theorem b66g_fibre_mk (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (p : rf8_fibre R.C t) : (⟨(t, p.val.2), rfl⟩ : rf8_fibre R.C t) = p :=
  Subtype.ext (b66g_fibre_val R t p).symm

theorem b66g_mem_source (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (p : rf8_fibre R.C t) :
    p.val ∈ (R.atlas.A a).source ↔ (t, p.val.2) ∈ (R.atlas.A a).source := by
  rw [← b66g_fibre_val R t p]

theorem b66g_toForm_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (a : b66k_Index R)
    (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source) (v : ℂ) :
    b66g_toForm R t q ⟨p, v⟩ = q a p.val.2 * b66g_sliceD R t a p v := by
  obtain ⟨_, hql, _⟩ := b66g_forms_spec R t 1 hq
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hlaw := hql a p.val p.val.2 ((b66g_mem_source R t a p).mp ha)
    ((b66g_mem_source R t p.val p).mp hb)
  change q p.val p.val.2 * b66g_sliceD R t p.val p v = _
  rw [b66g_slice_change R t a p.val p ha hb v, hlaw, pow_one]
  ring

theorem b66g_form_chart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ}
    (hlin : ∀ (x : rf8_fibre R.C t) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x₀ y : rf8_fibre R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (v : ℂ) :
    θ ⟨y, v⟩ = b66g_chartD R t x₀ y v * b4cov_coef θ x₀ 1 (extChartAt 𝓘(ℂ, ℂ) x₀ y) := by
  have h1 : b4cov_vec x₀ y (b66g_chartD R t x₀ y v) = v :=
    (congrArg (b4cov_vec x₀ y) (b4cov_triv_eq_mfderiv x₀ y hy v).symm).trans
      (b4cov_vec_triv x₀ y hy v)
  have h2 : b4cov_vec x₀ y (b66g_chartD R t x₀ y v) =
      b66g_chartD R t x₀ y v • b4cov_vec x₀ y (1 : ℂ) := by
    rw [← b4cov_vec_smul x₀ y hy, smul_eq_mul, mul_one]
  have h3 : b4cov_coef θ x₀ 1 (extChartAt 𝓘(ℂ, ℂ) x₀ y) = θ ⟨y, b4cov_vec x₀ y (1 : ℂ)⟩ := by
    rw [b4cov_coef, (extChartAt 𝓘(ℂ, ℂ) x₀).left_inv hy]
  rw [h3]
  refine Eq.trans ?_ (b66g_lin_smul' hlin y _ _)
  rw [← h2, h1]

theorem b66g_chartD_vec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x₀ y : rf8_fibre R.C t) (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (u : ℂ) :
    b66g_chartD R t x₀ y (b4cov_vec x₀ y u) = u :=
  (b4cov_triv_eq_mfderiv x₀ y hy (b4cov_vec x₀ y u)).symm.trans (b4cov_triv_vec x₀ y hy u)

theorem b66g_toForm_lin (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (x : rf8_fibre R.C t) (c v w : ℂ) :
    b66g_toForm R t q ⟨x, c * v + w⟩ =
      c * b66g_toForm R t q ⟨x, v⟩ + b66g_toForm R t q ⟨x, w⟩ := by
  change q x.val x.val.2 * b66g_sliceD R t x.val x (c * v + w) =
    c * (q x.val x.val.2 * b66g_sliceD R t x.val x v) +
      q x.val x.val.2 * b66g_sliceD R t x.val x w
  rw [b66g_clm_apply (b66g_sliceD R t x.val x) (c * v + w),
    b66g_clm_apply (b66g_sliceD R t x.val x) v, b66g_clm_apply (b66g_sliceD R t x.val x) w]
  ring

theorem b66g_toForm_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66g_toForm R t q ∈ b3_HolForm ℂ (rf8_fibre R.C t) := by
  obtain ⟨hqa, _, _⟩ := b66g_forms_spec R t 1 hq
  have hF : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  apply b4cov_mem_holForm_of_coef hF
  · intro x c v w
    exact b66g_toForm_lin R t q x c v w
  · intro x₀
    set e := extChartAt 𝓘(ℂ, ℂ) x₀
    set a := x₀.val
    set u : ℂ := b4cov_lineEquiv hF 1
    set h := b66g_slice R t a ∘ e.symm
    have hx₀ : x₀.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
    obtain ⟨han, _, _⟩ := b66g_slice_chart R t a x₀ x₀ (mem_extChartAt_source x₀) hx₀
    have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
      (R.atlas.A a).open_source.preimage continuous_subtype_val
    have hex : e x₀ ∈ e.target := e.map_source (mem_extChartAt_source x₀)
    have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e x₀) := by
      refine inter_mem (extChartAt_target_mem_nhds' hex) ?_
      apply (continuousAt_extChartAt_symm'' hex).preimage_mem_nhds
      rw [e.left_inv (mem_extChartAt_source x₀)]
      exact hopen.mem_nhds hx₀
    have hval : h (e x₀) = b66g_slice R t a x₀ := by
      simp only [h, Function.comp_apply, e.left_inv (mem_extChartAt_source x₀)]
    have hdom : h (e x₀) ∈ b66k_domain R t a := by
      rw [hval]
      change (t.val, (R.atlas.A a x₀.val).2) ∈ (R.atlas.A a).target
      rw [← b66g_slice_value R t a x₀ hx₀]
      exact (R.atlas.A a).map_source hx₀
    have hQ : AnalyticAt ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2) (h (e x₀)) :=
      hqa a _ hdom
    have hR : AnalyticAt ℂ (fun s => q a ((R.atlas.A a).symm (t.val, h s)).2 *
        (deriv h s * u)) (e x₀) :=
      (AnalyticAt.comp (f := h) hQ han).mul (han.deriv.mul analyticAt_const)
    apply hR.congr
    filter_upwards [hU] with s hs
    have hy : e.symm s ∈ e.source := e.map_target hs.1
    obtain ⟨_, _, hD⟩ := b66g_slice_chart R t a x₀ (e.symm s) hy hs.2
    change q a ((R.atlas.A a).symm (t.val, h s)).2 * (deriv h s * u) =
      q (e.symm s).val (e.symm s).val.2 *
        b66g_sliceD R t (e.symm s).val (e.symm s) (b4cov_vec x₀ (e.symm s) u)
    have hpt : ((R.atlas.A a).symm (t.val, h s)).2 = (e.symm s).val.2 := by
      change ((R.atlas.A a).symm (t.val, (R.atlas.A a (e.symm s).val).2)).2 = _
      rw [← b66g_slice_value R t a _ hs.2, (R.atlas.A a).left_inv hs.2]
    have k1 : b66g_sliceD R t a (e.symm s) (b4cov_vec x₀ (e.symm s) u) = deriv h s * u := by
      refine (hD _).trans ?_
      rw [b66g_chartD_vec R t x₀ _ hy, e.right_inv hs.1]
    have hap := b66g_toForm_apply R t hq a (e.symm s) hs.2 (b4cov_vec x₀ (e.symm s) u)
    refine Eq.trans ?_ hap.symm
    rw [k1, hpt]

theorem b66g_form_one {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ}
    (hlin : ∀ (x : X) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x : X) (w : ℂ) :
    θ ⟨x, w⟩ = w * θ ⟨x, (1 : ℂ)⟩ := by
  have h := b66g_lin_smul hlin x w 1
  rw [mul_one] at h
  exact h

theorem b66g_toForm_ofForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ}
    (hlin : ∀ (x : rf8_fibre R.C t) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) :
    b66g_toForm R t (b66g_ofForm R t θ) = θ := by
  funext P
  obtain ⟨p, v⟩ := P
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hsrc := (b66g_mem_source R t p.val p).mp hb
  change b66g_ofForm R t θ p.val p.val.2 * b66g_sliceD R t p.val p v = θ ⟨p, v⟩
  suffices hw : ∀ w : ℂ, b66g_ofForm R t θ p.val p.val.2 * b66g_sliceD R t p.val p w =
      θ ⟨p, w⟩ from hw v
  intro v
  unfold b66g_ofForm
  rw [ite_eq_left hsrc, b66g_fibre_mk R t p]
  have hne := b66g_slice_ne R t p.val p hb
  rw [b66g_form_one hlin p, b66g_form_one hlin p v, b66g_clm_apply (b66g_sliceD R t p.val p) v]
  field_simp

theorem b66g_ofForm_toForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    b66g_ofForm R t (b66g_toForm R t q) = q := by
  obtain ⟨_, _, hqz⟩ := b66g_forms_spec R t 1 hq
  funext a x
  unfold b66g_ofForm
  split_ifs with h
  · have hap := b66g_toForm_apply R t hq a ⟨(t, x), rfl⟩ h
      ((b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    refine hap.trans ?_
    have hne := b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [b66g_clm_apply (b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change q a x * (_ * _) = q a x
    field_simp
  · exact (hqz a x h).symm

theorem b66g_ofForm_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ}
    (hθ : θ ∈ b3_HolForm ℂ (rf8_fibre R.C t)) :
    b66g_ofForm R t θ ∈ b66g_forms R t 1 := by
  have hlin := hθ.2
  apply Submodule.subset_span
  refine ⟨fun a z₀ hz₀ => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩
  · let y₀ : rf8_fibre R.C t :=
      ⟨(R.atlas.A a).symm (t.val, z₀), Subtype.ext (b66k_inverse_parameter R a _ hz₀)⟩
    have hy₀a : y₀.val ∈ (R.atlas.A a).source := (R.atlas.A a).map_target hz₀
    set e := extChartAt 𝓘(ℂ, ℂ) y₀
    set h := b66g_slice R t a ∘ e.symm
    obtain ⟨han, hder, _⟩ :=
      b66g_slice_chart R t a y₀ y₀ (mem_extChartAt_source y₀) hy₀a
    have hz : h (e y₀) = z₀ := by
      change (R.atlas.A a (e.symm (e y₀)).val).2 = z₀
      rw [e.left_inv (mem_extChartAt_source y₀)]
      change (R.atlas.A a ((R.atlas.A a).symm (t.val, z₀))).2 = z₀
      rw [(R.atlas.A a).right_inv hz₀]
    rw [← hz]
    refine (analyticAt_comp_iff_of_deriv_ne_zero han hder).mp ?_
    have hex : e y₀ ∈ e.target := e.map_source (mem_extChartAt_source y₀)
    have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
      (R.atlas.A a).open_source.preimage continuous_subtype_val
    have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y₀) := by
      refine inter_mem (extChartAt_target_mem_nhds' hex) ?_
      apply (continuousAt_extChartAt_symm'' hex).preimage_mem_nhds
      rw [e.left_inv (mem_extChartAt_source y₀)]
      exact hopen.mem_nhds hy₀a
    have hK : AnalyticAt ℂ (fun s => b4cov_coef θ y₀ 1 s / deriv h s) (e y₀) :=
      (b4cov_coef_analyticAt θ hθ.1 y₀ 1 _ hex).div han.deriv hder
    apply hK.congr
    filter_upwards [hU] with s hs
    have hy : e.symm s ∈ e.source := e.map_target hs.1
    obtain ⟨_, _, hD⟩ := b66g_slice_chart R t a y₀ (e.symm s) hy hs.2
    have hpt : ((R.atlas.A a).symm (t.val, h s)).2 = (e.symm s).val.2 := by
      change ((R.atlas.A a).symm (t.val, (R.atlas.A a (e.symm s).val).2)).2 = _
      rw [← b66g_slice_value R t a _ hs.2, (R.atlas.A a).left_inv hs.2]
    change _ = b66g_ofForm R t θ a ((R.atlas.A a).symm (t.val, h s)).2
    rw [hpt]
    unfold b66g_ofForm
    rw [ite_eq_left ((b66g_mem_source R t a _).mp hs.2), b66g_fibre_mk R t (e.symm s)]
    have hne := b66g_slice_ne R t a (e.symm s) hs.2
    have h1 := hD 1
    rw [e.right_inv hs.1] at h1
    rw [b66g_form_chart R t hlin y₀ (e.symm s) hy, e.right_inv hs.1,
      b66g_clm_apply (b66g_chartD R t y₀ (e.symm s)), h1]
    rw [h1] at hne
    have hc : b66g_chartD R t y₀ (e.symm s) 1 ≠ 0 := right_ne_zero_of_mul hne
    field_simp
    rfl
  · unfold b66g_ofForm
    rw [ite_eq_left ha, ite_eq_left hb, pow_one]
    have hch := b66g_slice_change R t a b ⟨(t, x), rfl⟩ ha hb 1
    have hna := b66g_slice_ne R t a ⟨(t, x), rfl⟩ ha
    have hnb := b66g_slice_ne R t b ⟨(t, x), rfl⟩ hb
    have e1 : (b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹ =
        b66k_vertical R t a b x * (b66g_sliceD R t b ⟨(t, x), rfl⟩ 1)⁻¹ := by
      rw [hch] at hnb ⊢
      have hv : b66k_vertical R t a b x ≠ 0 := left_ne_zero_of_mul hnb
      field_simp
    rw [e1]
    exact b66g_lin_smul hlin _ _ _
  · unfold b66g_ofForm
    rw [ite_eq_right hx]

theorem b66g_pullback_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (g : b4b_Group) (a : b66k_Index R)
    (p : rf8_fibre R.C t) (ha : p.val ∈ (R.atlas.A a).source) (v : ℂ) :
    b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q) ⟨p, v⟩ =
      b66g_pull R t 1 g q a p.val.2 * b66g_sliceD R t a p v := by
  set c : b66k_Index R := (g • p).val
  set D := b66k_deckCoordinate R t g a c
  have hc : (g • p).val ∈ (R.atlas.A c).source := (R.atlas.hA c).1
  have hpa := b66g_slice_value R t a p ha
  have hsym : (R.atlas.A a).symm (t.val, b66g_slice R t a p) = p.val := by
    change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) = p.val
    rw [← hpa, (R.atlas.A a).left_inv ha]
  have hz : b66g_slice R t a p ∈ b66k_refinementDomain R t g a c := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · rw [hsym]
      exact hc
  have hD : HasDerivAt D (deriv D (b66g_slice R t a p)) (b66g_slice R t a p) :=
    (b66k_deckCoordinate_analytic R t g a c _ hz).differentiableAt.hasDerivAt
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66g_slice R t c ∘ (fun x : rf8_fibre R.C t => g • x) =ᶠ[𝓝 p]
      D ∘ b66g_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A c (t, g • y.val.2)).2 =
      (R.atlas.A c (t, g • ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2)).2)).2
    rw [← b66g_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t a) p :=
    (b66g_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hmc : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66g_slice R t c) (g • p) :=
    (b66g_slice_contMDiffAt R t c (g • p) hc).mdifferentiableAt (by simp)
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : rf8_fibre R.C t => g • x) p :=
    ((R.hG t g) p).mdifferentiableAt (by simp)
  have hmD : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) D (b66g_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hD.differentiableAt
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b66g_slice R t c ∘ (fun x : rf8_fibre R.C t => g • x)) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv D (b66g_slice R t a p))).comp
        (b66g_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := D) (f := b66g_slice R t a) p hD.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  have hchain := mfderiv_comp_apply p hmc hmg v
  rw [hH.mfderiv] at hchain
  have hsrc : (t, p.val.2) ∈ (R.atlas.A a).source := (b66g_mem_source R t a p).mp ha
  have hval : (R.atlas.A a (t, p.val.2)).2 = b66g_slice R t a p := by
    change _ = (R.atlas.A a p.val).2
    rw [← b66g_fibre_val R t p]
  change q (g • p).val (g • p).val.2 *
      b66g_sliceD R t c (g • p) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : rf8_fibre R.C t => g • x) p v) =
    (if (t, p.val.2) ∈ (R.atlas.A a).source then q (t, g • p.val.2) (g • p.val.2) *
      deriv (b66k_deckCoordinate R t g a (t, g • p.val.2)) (R.atlas.A a (t, p.val.2)).2 ^ 1
      else 0) * b66g_sliceD R t a p v
  rw [ite_eq_left hsrc, pow_one, hval]
  have k : b66g_sliceD R t c (g • p)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : rf8_fibre R.C t => g • x) p v) =
      deriv D (b66g_slice R t a p) * b66g_sliceD R t a p v :=
    hchain.symm.trans (mul_comm (b66g_sliceD R t a p v) _)
  refine (congrArg (fun w => q (g • p).val (g • p).val.2 * w) k).trans ?_
  change q c (g • p.val.2) * (deriv D (b66g_slice R t a p) * b66g_sliceD R t a p v) =
    q c (g • p.val.2) * deriv D (b66g_slice R t a p) * b66g_sliceD R t a p v
  ring

theorem b66g_projector_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (a : b66k_Index R) (x : R.C) :
    b66g_projector R t q a x =
      ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) * b66g_pull R t 1 g q a x := by
  unfold b66g_projector
  rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply]
  rfl

theorem b66g_projector_form (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) :
    (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q)) ∈
        b3_HolForm ℂ (rf8_fibre R.C t) ∧
    b66g_ofForm R t (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q)) =
        b66g_projector R t q := by
  have hmem : (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
      b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q)) ∈
        b3_HolForm ℂ (rf8_fibre R.C t) :=
    Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
      (b3_pullback_mem_holForm _ (R.hG t g) _ (b66g_toForm_mem R t hq))
  refine ⟨hmem, ?_⟩
  funext a x
  rw [b66g_projector_apply]
  unfold b66g_ofForm
  split_ifs with h
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    have hap := b66g_pullback_apply R t q g a ⟨(t, x), rfl⟩ h
      ((b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    have hne := b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [hap, b66g_clm_apply (b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change _ * (b66g_pull R t 1 g q a x * _) = _
    field_simp
  · symm
    refine Finset.sum_eq_zero fun g _ => ?_
    change _ * (if (t, x) ∈ (R.atlas.A a).source then _ else 0) = 0
    rw [ite_eq_right h, mul_zero]

theorem b66g_homG_top (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ b4b_Group V) :
    Module.finrank ℂ (b4_HomG ρ (fun g => b4_formRepresentation (R.hG t) g) ⊤) =
      Module.finrank ℂ (b4_HomG ρ (fun g => b4_formAct ℂ (C := rf8_fibre R.C t) g)
        (b3_HolForm ℂ (rf8_fibre R.C t))) := by
  let e : b4_HomG ρ (fun g => b4_formRepresentation (R.hG t) g) ⊤ ≃ₗ[ℂ]
      Representation.IntertwiningMap ρ (b4_formRepresentation (R.hG t)) :=
    { toFun := fun φ => (φ.val).intertwiningMap_of_isIntertwiningMap ρ _ φ.2.2
      invFun := fun ψ => ⟨ψ.toLinearMap, fun _ => trivial, fun g v =>
        LinearMap.congr_fun (ψ.isIntertwining' g) v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, (b4_homGFormEquiv (R.hG t) ρ).finrank_eq]

theorem b66g_primitive_finrank (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    haveI : FiniteDimensional ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) :=
      b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
    Module.finrank ℂ ((⊤ : Submodule ℂ (b3_HolForm ℂ (rf8_fibre R.C t))).map
      (∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g)) = 6 := by
  have : FiniteDimensional ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) :=
    b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
  have hq : Function.Injective (b6_branch t.val) :=
    (b6t_polydisc_neighbourhood mr_base R.atlas.hb).2.2.2 t.property
  rw [b63d_finrank_primitive_image (b4_formRepresentation (R.hG t)) ⊤ (fun _ => le_top),
    b66g_homG_top, b66g_homG_top,
    b63d_natural_holo_multiplicity (rf8_fibre R.C t) (R.hG t)
      (b63d_projection mr_base R.C R.atlas.f (b6t_polydisc mr_base) (Subset.refl _) t)
      (R.hk t) (R.hsurj t) (R.hgal t) (b6_branch t.val) hq (R.hbranch t) (R.hrot t),
    b63d_conjugate_holo_multiplicity (rf8_fibre R.C t) (R.hG t)
      (b63d_projection mr_base R.C R.atlas.f (b6t_polydisc mr_base) (Subset.refl _) t)
      (R.hk t) (R.hsurj t) (R.hgal t) (b6_branch t.val) hq (R.hbranch t) (R.hrot t)]

/-- The comparison of retained one-form coefficients with fibre differentials. -/
def b66g_formEquiv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t) where
  toFun q := ⟨b66g_toForm R t q.val, b66g_toForm_mem R t q.property⟩
  map_add' q r := Subtype.ext (map_add (b66g_toForm R t) q.val r.val)
  map_smul' c q := Subtype.ext (map_smul (b66g_toForm R t) c q.val)
  invFun θ := ⟨b66g_ofForm R t θ.val, b66g_ofForm_mem R t θ.property⟩
  left_inv q := Subtype.ext (b66g_ofForm_toForm R t q.property)
  right_inv θ := Subtype.ext (b66g_toForm_ofForm R t θ.property.2)

theorem b66g_formEquiv_projector (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_forms R t 1) :
    ((b66g_formEquiv R t).symm
      ((∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g)
        (b66g_formEquiv R t q))).val = b66g_projector R t q.val := by
  rw [← (b66g_projector_form R t q.property).2]
  change b66g_ofForm R t _ = b66g_ofForm R t _
  congr 1
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  have hre := Equiv.sum_comp (Equiv.inv b4b_Group) (fun g => (b4b_projectorCoeff g⁻¹ : ℂ) •
    b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q.val))
  simp only [Equiv.inv_apply, inv_inv] at hre
  refine Eq.trans ?_ (hre.trans (Finset.sum_congr rfl fun g _ => by
    rw [b63l_projectorCoeff_inverse]))
  exact Finset.sum_congr rfl fun g _ => rfl

theorem b66g_primitiveForms_finrank (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Module.finrank ℂ (b66g_primitiveForms R t) = 6 := by
  have : FiniteDimensional ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) :=
    b3Forms_holForm_finiteDimensional (Module.finrank_self ℂ)
  set P := ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b4_formRepresentation (R.hG t) g
  set M := b66g_formEquiv R t
  let f := (b66g_forms R t 1).subtype ∘ₗ M.symm.toLinearMap
  have hf : Function.Injective f :=
    (b66g_forms R t 1).injective_subtype.comp M.symm.injective
  have hrange : LinearMap.range ((b66g_projector R t).comp (b66g_forms R t 1).subtype) =
      (LinearMap.range P).map f := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨P (M q), ⟨M q, rfl⟩, b66g_formEquiv_projector R t q⟩
    · rintro ⟨θ, ⟨θ', rfl⟩, rfl⟩
      refine ⟨M.symm θ', ?_⟩
      change b66g_projector R t (M.symm θ').val = (M.symm (P θ')).val
      rw [← b66g_formEquiv_projector R t (M.symm θ'), LinearEquiv.apply_symm_apply]
  have hle : LinearMap.range ((b66g_projector R t).comp (b66g_forms R t 1).subtype) ≤
      b66g_forms R t 1 := by
    rw [hrange]
    rintro x ⟨θ, _, rfl⟩
    exact (M.symm θ).property
  have hprim : b66g_primitiveForms R t =
      LinearMap.range ((b66g_projector R t).comp (b66g_forms R t 1).subtype) :=
    inf_eq_right.mpr hle
  rw [hprim, hrange, ← (Submodule.equivMapOfInjective f hf _).finrank_eq, ← Submodule.map_top]
  exact b66g_primitive_finrank R t

theorem b66g_primitive_comparison_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (∃ M : b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t),
      (∀ (q : b66g_forms R t 1) (a : b66k_Index R) (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        (M q).val ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v)) ∧
      ∀ q : b66g_forms R t 1, ∃ qP : b66g_forms R t 1,
        qP.val = b66g_projector R t q.val ∧
        (M qP).val = ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
          b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (M q).val) ∧
    Module.finrank ℂ (b66g_primitiveForms R t) = 6 := by
  refine ⟨⟨b66g_formEquiv R t, fun q a p hp v => b66g_toForm_apply R t q.property a p hp v,
    fun q => ?_⟩, b66g_primitiveForms_finrank R t⟩
  obtain ⟨hmem, heq⟩ := b66g_projector_form R t q.property
  exact ⟨⟨b66g_ofForm R t _, b66g_ofForm_mem R t hmem⟩, heq, b66g_toForm_ofForm R t hmem.2⟩

theorem b66g_pull_one (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_Coeff R) (g : b4b_Group) :
    b66g_pull R t 1 g q = b66g_ofForm R t
      (b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q)) := by
  funext a x
  unfold b66g_ofForm
  split_ifs with h
  · have hap := b66g_pullback_apply R t q g a ⟨(t, x), rfl⟩ h
      ((b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    have hne := b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [hap, b66g_clm_apply (b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change _ = b66g_pull R t 1 g q a x * (_ * _)
    field_simp
  · change (if (t, x) ∈ (R.atlas.A a).source then _ else 0) = 0
    rw [ite_eq_right h]

theorem b66g_pull_one_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (g : b4b_Group) :
    b66g_pull R t 1 g q ∈ b66g_forms R t 1 := by
  rw [b66g_pull_one]
  exact b66g_ofForm_mem R t (b3_pullback_mem_holForm _ (R.hG t g) _ (b66g_toForm_mem R t hq))

theorem b66g_toForm_pull (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (g : b4b_Group) :
    b66g_toForm R t (b66g_pull R t 1 g q) =
      b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (b66g_toForm R t q) := by
  rw [b66g_pull_one]
  exact b66g_toForm_ofForm R t
    (b3_pullback_mem_holForm _ (R.hG t g) _ (b66g_toForm_mem R t hq)).2

theorem b66g_pull_pull (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (g h : b4b_Group) :
    b66g_pull R t 1 g (b66g_pull R t 1 h q) = b66g_pull R t 1 (h * g) q := by
  rw [b66g_pull_one R t (b66g_pull R t 1 h q), b66g_toForm_pull R t hq,
    b4cov_pullback_comp _ _ (R.hG t g) (R.hG t h), b66g_pull_one]
  have hc : ((fun x : rf8_fibre R.C t => h • x) ∘ fun x => g • x) = fun x => (h * g) • x :=
    funext fun x => (mul_smul h g x).symm
  rw [hc]

theorem b66g_pull_product (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : b66g_Coeff R) (g : b4b_Group) :
    b66g_pull R t 2 g (b66g_product R q r) =
      b66g_product R (b66g_pull R t 1 g q) (b66g_pull R t 1 g r) := by
  funext a x
  simp only [b66g_pull, LinearMap.coe_mk, AddHom.coe_mk, b66g_product]
  split_ifs <;> ring_nf

theorem b66g_average_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (P : b66g_Coeff R) :
    b66g_average R t P =
      (Fintype.card b4b_Group : ℂ)⁻¹ • ∑ g : b4b_Group, b66g_pull R t 2 g P := by
  unfold b66g_average
  rw [LinearMap.smul_apply, LinearMap.sum_apply]

theorem b66g_average_product (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q r : b66g_Coeff R} (hq : q ∈ b66g_forms R t 1) (hr : r ∈ b66g_forms R t 1) :
    b66g_average R t (b66g_product R q r) ∈ b66g_forms R t 2 ∧
    ∀ g : b4b_Group, b66g_pull R t 2 g (b66g_average R t (b66g_product R q r)) =
      b66g_average R t (b66g_product R q r) := by
  constructor
  · rw [b66g_average_apply]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_)
    rw [b66g_pull_product]
    exact (b66g_cup_aux R t).2 ⟨_, b66g_pull_one_mem R t hq g⟩ ⟨_, b66g_pull_one_mem R t hr g⟩
  · intro g
    rw [b66g_average_apply, map_smul, map_sum]
    congr 1
    have hre := Equiv.sum_comp (Equiv.mulRight g)
      (fun h => b66g_pull R t 2 h (b66g_product R q r))
    refine Eq.trans ?_ hre
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [b66g_pull_product, b66g_pull_product, b66g_pull_product, b66g_pull_pull R t hq,
      b66g_pull_pull R t hr]
    rfl

theorem b66g_dslope_analytic {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀) :
    AnalyticAt ℂ (dslope D z₀) z₀ := by
  obtain ⟨p, hp⟩ := hD
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem b66g_taylor {φ : ℂ → ℂ} {w₀ : ℂ} (hφ : AnalyticAt ℂ φ w₀) (N : ℕ) :
    ∃ (a : Fin N → ℂ) (ρ : ℂ → ℂ), AnalyticAt ℂ ρ w₀ ∧
      ∀ w, φ w = ∑ i : Fin N, a i * (w - w₀) ^ (i : ℕ) + (w - w₀) ^ N * ρ w := by
  induction N with
  | zero => exact ⟨Fin.elim0, φ, hφ, fun w => by simp⟩
  | succ N ih =>
    obtain ⟨a, ρ, hρ, h⟩ := ih
    refine ⟨Fin.snoc a (ρ w₀), dslope ρ w₀, b66g_dslope_analytic hρ, fun w => ?_⟩
    rw [h w, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    have hs := sub_smul_dslope ρ w₀ w
    rw [smul_eq_mul] at hs
    have : ρ w = ρ w₀ + (w - w₀) * dslope ρ w₀ w := by rw [hs]; ring
    rw [this, pow_succ]
    ring

theorem b66g_principal_part {f : ℂ → ℂ} {w₀ : ℂ} (hf : MeromorphicAt f w₀) :
    ∃ (N : ℕ) (c : Fin N → ℂ) (ρ : ℂ → ℂ), AnalyticAt ℂ ρ w₀ ∧
      ∀ᶠ w in 𝓝[≠] w₀, f w = ρ w + ∑ k : Fin N, c k / (w - w₀) ^ (k.val + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f w₀ := by
    rcases eq_or_ne (meromorphicOrderAt f w₀) ⊤ with h | h
    · exact ⟨0, by rw [h]; exact le_top⟩
    · set a := (meromorphicOrderAt f w₀).untop₀
      have ha : meromorphicOrderAt f w₀ = (a : WithTop ℤ) :=
        (WithTop.coe_untop₀_of_ne_top h).symm
      refine ⟨(-a).toNat, ?_⟩
      rw [ha, WithTop.coe_le_coe]
      omega
  obtain ⟨φ, hφ, hfφ⟩ := TauCeti.Contour.exists_analyticAt_eventuallyEq_zpow_smul hf hN
  obtain ⟨a, ρ, hρ, hφe⟩ := b66g_taylor hφ N
  refine ⟨N, fun k => a (Fin.rev k), ρ, hρ, ?_⟩
  filter_upwards [hfφ, self_mem_nhdsWithin] with w hw hne
  have he : w - w₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [hw, hφe w, smul_eq_mul, mul_add, Finset.mul_sum]
  have hre := Equiv.sum_comp Fin.revPerm (fun k : Fin N => a (Fin.rev k) / (w - w₀) ^ (k.val + 1))
  simp only [Fin.revPerm_apply, Fin.rev_rev] at hre
  rw [← hre, zpow_neg, zpow_natCast, add_comm]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (Fin.rev i).val + 1 + i.val = N := by
      rw [Fin.val_rev]
      omega
    have hpow : (w - w₀) ^ N = (w - w₀) ^ ((Fin.rev i).val + 1) * (w - w₀) ^ (i : ℕ) := by
      rw [← pow_add, hi]
    rw [hpow]
    field_simp

theorem b66g_residue_simple {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) :
    TauCeti.Contour.residue (fun z => deriv D z / (D z - D z₀) ^ (0 + 1)) z₀ = 1 := by
  have hm : MeromorphicAt (fun z => D z - D z₀) z₀ := (hD.sub analyticAt_const).meromorphicAt
  have hord : meromorphicOrderAt (fun z => D z - D z₀) z₀ = ((1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff hm]
    refine ⟨dslope D z₀, b66g_dslope_analytic hD, by rwa [dslope_same], ?_⟩
    exact Filter.Eventually.of_forall fun z => by
      rw [zpow_one, sub_smul_dslope]
  have h := TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt hm hord
  rw [Int.cast_one] at h
  rw [← h]
  congr 1
  funext z
  simp only [logDeriv_apply, zero_add, pow_one]
  rw [deriv_sub_const]

theorem b66g_residue_higher {D : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) (i : ℕ) :
    TauCeti.Contour.residue (fun z => deriv D z / (D z - D z₀) ^ (i + 1 + 1)) z₀ = 0 := by
  have hψ0 : dslope D z₀ z₀ ≠ 0 := by rwa [dslope_same]
  set ψ := dslope D z₀
  have hψ : AnalyticAt ℂ ψ z₀ := b66g_dslope_analytic hD
  have hDψ : ∀ z, D z - D z₀ = (z - z₀) * ψ z := fun z => by
    rw [← smul_eq_mul, sub_smul_dslope]
  have hDfun : D = fun z => D z₀ + (z - z₀) * ψ z := by
    funext z
    rw [← hDψ z]
    ring
  set χ : ℂ → ℂ := fun z => (ψ z ^ (i + 1))⁻¹
  have hχ : AnalyticAt ℂ χ z₀ := (hψ.pow (i + 1)).inv (pow_ne_zero _ hψ0)
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ψ z ∧ ψ z ≠ 0 :=
    hψ.eventually_analyticAt.and (hψ.continuousAt.eventually_ne hψ0)
  have hkey : (fun z => deriv D z / (D z - D z₀) ^ (i + 1 + 1)) =ᶠ[𝓝[≠] z₀]
      (fun z => (z - z₀) ^ (-((i + 2 : ℕ) : ℤ)) • χ z) +
      (fun z => (z - z₀) ^ (-((i + 1 : ℕ) : ℤ)) •
        ((-(1 / ((i : ℂ) + 1))) * deriv χ z)) := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z ⟨hza, hzn⟩ hz
    have he : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hdD : deriv D z = ψ z + (z - z₀) * deriv ψ z := by
      rw [hDfun]
      have h1 : HasDerivAt (fun z => D z₀ + (z - z₀) * ψ z)
          (1 * ψ z + (z - z₀) * deriv ψ z) z :=
        (((hasDerivAt_id z).sub_const z₀).mul hza.differentiableAt.hasDerivAt).const_add _
      rw [h1.deriv, one_mul]
    have hdχ : deriv χ z = -(((i + 1 : ℕ) : ℂ) * ψ z ^ i * deriv ψ z) /
        (ψ z ^ (i + 1)) ^ 2 := by
      have h2 := ((hza.differentiableAt.hasDerivAt.pow (i + 1)).inv (pow_ne_zero _ hzn)).deriv
      simp only [Pi.pow_apply, Nat.add_sub_cancel] at h2
      exact h2
    simp only [Pi.add_apply, smul_eq_mul, χ]
    rw [hdD, hdχ, hDψ z, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow]
    push_cast
    field_simp
    ring
  rw [TauCeti.Contour.residue_congr_nhdsNE hkey]
  have hm1 : MeromorphicAt (fun z => (z - z₀) ^ (-((i + 2 : ℕ) : ℤ)) • χ z) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).smul hχ.meromorphicAt
  have hχd : AnalyticAt ℂ (fun z => (-(1 / ((i : ℂ) + 1))) * deriv χ z) z₀ :=
    analyticAt_const.mul hχ.deriv
  have hm2 : MeromorphicAt (fun z => (z - z₀) ^ (-((i + 1 : ℕ) : ℤ)) •
      ((-(1 / ((i : ℂ) + 1))) * deriv χ z)) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).smul hχd.meromorphicAt
  rw [TauCeti.Contour.residue_add hm1 hm2,
    TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by omega) hχ
      (Filter.Eventually.of_forall fun _ => rfl),
    TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by omega) hχd
      (Filter.Eventually.of_forall fun _ => rfl)]
  have ht1 : (-1 - (-((i + 2 : ℕ) : ℤ))).toNat = i + 1 := by omega
  have ht2 : (-1 - (-((i + 1 : ℕ) : ℤ))).toNat = i := by omega
  rw [ht1, ht2, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  field_simp
  ring

theorem b66g_residue_comp {D f : ℂ → ℂ} {z₀ : ℂ} (hD : AnalyticAt ℂ D z₀)
    (hD' : deriv D z₀ ≠ 0) (hf : MeromorphicAt f (D z₀)) :
    TauCeti.Contour.residue (fun z => f (D z) * deriv D z) z₀ =
      TauCeti.Contour.residue f (D z₀) := by
  obtain ⟨N, c, ρ, hρ, hfe⟩ := b66g_principal_part hf
  rw [TauCeti.Contour.residue_of_laurent_expansion hρ hfe]
  have hT := hD.differentiableAt.hasDerivAt.tendsto_nhdsNE hD'
  have hcomp : (fun z => f (D z) * deriv D z) =ᶠ[𝓝[≠] z₀]
      (fun z => ρ (D z) * deriv D z) +
        ∑ k : Fin N, fun z => c k * (deriv D z / (D z - D z₀) ^ (k.val + 1)) := by
    filter_upwards [hT.eventually hfe] with z hz
    rw [hz, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hmk : ∀ k : Fin N, MeromorphicAt
      (fun z => c k * (deriv D z / (D z - D z₀) ^ (k.val + 1))) z₀ := fun k =>
    analyticAt_const.meromorphicAt.mul (hD.deriv.meromorphicAt.div
      ((hD.sub analyticAt_const).pow _).meromorphicAt)
  have hρD : AnalyticAt ℂ (fun z => ρ (D z) * deriv D z) z₀ :=
    (AnalyticAt.comp (f := D) hρ hD).mul hD.deriv
  rw [TauCeti.Contour.residue_congr_nhdsNE hcomp,
    TauCeti.Contour.residue_add hρD.meromorphicAt
      (MeromorphicAt.sum fun k _ => hmk k),
    TauCeti.Contour.residue_eq_zero_of_analyticAt hρD, zero_add,
    TauCeti.Contour.residue_sum _ fun k _ => hmk k]
  simp only [TauCeti.Contour.residue_const_mul]
  have hval : ∀ k : Fin N, TauCeti.Contour.residue
      (fun z => deriv D z / (D z - D z₀) ^ (k.val + 1)) z₀ = if k.val = 0 then 1 else 0 := by
    intro k
    rcases Nat.eq_zero_or_eq_succ_pred k.val with h | h
    · rw [ite_eq_left h, h]
      exact b66g_residue_simple hD hD'
    · rw [ite_eq_right (by omega), h]
      exact b66g_residue_higher hD hD' _
  simp only [hval, mul_ite, mul_one, mul_zero]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · rw [dite_eq_left hN, Finset.sum_eq_single ⟨0, hN⟩]
    · simp
    · intro k _ hk
      exact ite_eq_right fun h0 => hk (Fin.ext h0)
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem b66g_refinement_iff (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) (hz : (t.val, z) ∈ (R.atlas.A a).target) :
    b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈ (R.atlas.A b).source ↔
      z ∈ b66k_refinementDomain R t g a b := by
  constructor
  · intro h
    refine ⟨hz, ?_⟩
    unfold b66k_totalDeck at h
    rwa [← b66k_inverse_slice R t a z hz] at h
  · intro h
    unfold b66k_totalDeck
    rw [← b66k_inverse_slice R t a z hz]
    exact h.2

theorem b66g_refinement_eventually (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t g a b) :
    ∀ᶠ w in 𝓝 z, w ∈ b66k_refinementDomain R t g a b := by
  have h := b66k_deck_overlap_nhds R g a b (t.val, z) hz.1
    ((b66g_refinement_iff R t g a b z hz.1).mpr hz)
  have hc : Tendsto (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (𝓝 z) (𝓝 (t.val, z)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [hc.eventually h] with w hw
  exact (b66g_refinement_iff R t g a b w hw.1).mp hw.2

theorem b66g_refinement_point (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) :
    (R.atlas.A a (t, x)).2 ∈ b66k_refinementDomain R t g a b := by
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  refine ⟨?_, ?_⟩
  · rw [hpa]
    exact (R.atlas.A a).map_source ha
  · rw [hpa, (R.atlas.A a).left_inv ha]
    exact hb

theorem b66g_deck_value (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source) :
    b66k_deckCoordinate R t g a b (R.atlas.A a (t, x)).2 = (R.atlas.A b (t, g • x)).2 := by
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  unfold b66k_deckCoordinate
  rw [hpa, (R.atlas.A a).left_inv ha]

theorem b66g_deck_inverse (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t g a b) :
    b66k_deckCoordinate R t g a b z ∈ b66k_refinementDomain R t g⁻¹ b a ∧
    (fun w => b66k_deckCoordinate R t g⁻¹ b a (b66k_deckCoordinate R t g a b w)) =ᶠ[𝓝 z]
      id ∧
    deriv (b66k_deckCoordinate R t g⁻¹ b a) (b66k_deckCoordinate R t g a b z) *
      deriv (b66k_deckCoordinate R t g a b) z = 1 := by
  have hx := b66k_inverse_slice R t a z hz.1
  set x := ((R.atlas.A a).symm (t.val, z)).2
  have hxa : (t, x) ∈ (R.atlas.A a).source := by
    rw [hx]
    exact (R.atlas.A a).map_target hz.1
  have hza : (R.atlas.A a (t, x)).2 = z := by
    rw [hx, (R.atlas.A a).right_inv hz.1]
  have hgx : (t, g • x) ∈ (R.atlas.A b).source := hz.2
  have hmem : b66k_deckCoordinate R t g a b z ∈ b66k_refinementDomain R t g⁻¹ b a := by
    have h1 := b66g_deck_value R t g a b x hxa
    rw [hza] at h1
    rw [h1]
    have h2 := b66g_refinement_point R t g⁻¹ b a (g • x) hgx (by rwa [inv_smul_smul])
    exact h2
  have hid : (fun w => b66k_deckCoordinate R t g⁻¹ b a (b66k_deckCoordinate R t g a b w)) =ᶠ[𝓝 z]
      id := by
    filter_upwards [b66g_refinement_eventually R t g a b z hz] with w hw
    have hxw := b66k_inverse_slice R t a w hw.1
    set y := ((R.atlas.A a).symm (t.val, w)).2
    have hya : (t, y) ∈ (R.atlas.A a).source := by
      rw [hxw]
      exact (R.atlas.A a).map_target hw.1
    have hyw : (R.atlas.A a (t, y)).2 = w := by
      rw [hxw, (R.atlas.A a).right_inv hw.1]
    have h1 := b66g_deck_value R t g a b y hya
    rw [hyw] at h1
    rw [h1, b66g_deck_value R t g⁻¹ b a (g • y) hw.2, inv_smul_smul, hyw]
    rfl
  refine ⟨hmem, hid, ?_⟩
  have hD := (b66k_deckCoordinate_analytic R t g a b z hz).differentiableAt.hasDerivAt
  have hE := (b66k_deckCoordinate_analytic R t g⁻¹ b a _ hmem).differentiableAt.hasDerivAt
  have hc := hE.comp z hD
  have hc' := hc.congr_of_eventuallyEq hid.symm
  have := hc'.unique (hasDerivAt_id z)
  rw [← this]

theorem b66g_deck_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t g a b) :
    deriv (b66k_deckCoordinate R t g a b) z ≠ 0 := by
  intro h0
  have h := (b66g_deck_inverse R t g a b z hz).2.2
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem b66g_deck_chain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b c d : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 * b66k_vertical R t a c x =
      b66k_vertical R t b d (g • x) *
        deriv (b66k_deckCoordinate R t g a b) (R.atlas.A a (t, x)).2 := by
  set z := (R.atlas.A a (t, x)).2
  have hzab := b66g_refinement_point R t g a b x ha hb
  have hzcd := b66g_refinement_point R t g c d x hc hd
  have hzac : z ∈ b66k_refinementDomain R t 1 a c :=
    b66g_refinement_point R t 1 a c x ha (by rwa [one_smul])
  have hgx : (R.atlas.A b (t, g • x)).2 ∈ b66k_refinementDomain R t 1 b d :=
    b66g_refinement_point R t 1 b d (g • x) hb (by rwa [one_smul])
  obtain ⟨hmac, _, _, _⟩ := b66g_transition_mem R t a c z hzac
  obtain ⟨hmbd, _, _, _⟩ := b66g_transition_mem R t b d _ hgx
  have hTac := b66g_transition_hasDerivAt R t a c z hmac
  have hTbd := b66g_transition_hasDerivAt R t b d _ hmbd
  have hpc : b66k_transition R a c (t.val, z) = (R.atlas.A c (t, x)).2 := by
    change (R.atlas.A c ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2))).2 = _
    rw [show (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) from
      Prod.ext (R.atlas.hparam a _ ha).symm rfl, (R.atlas.A a).left_inv ha]
  have hDab := (b66k_deckCoordinate_analytic R t g a b z hzab).differentiableAt.hasDerivAt
  have hDcd := (b66k_deckCoordinate_analytic R t g c d _ hzcd).differentiableAt.hasDerivAt
  rw [← hpc] at hDcd
  have hL := hDcd.comp z hTac
  have hDv : b66k_deckCoordinate R t g a b z = (R.atlas.A b (t, g • x)).2 :=
    b66g_deck_value R t g a b x ha
  rw [← hDv] at hTbd
  have hR := hTbd.comp z hDab
  have heq : (b66k_deckCoordinate R t g c d ∘ fun w => b66k_transition R a c (t.val, w)) =ᶠ[𝓝 z]
      ((fun w => b66k_transition R b d (t.val, w)) ∘ b66k_deckCoordinate R t g a b) := by
    have hev1 := b66g_refinement_eventually R t g a b z hzab
    have hev2 := b66g_overlap_eventually R t a c z hzac
    filter_upwards [hev1, hev2] with w hw1 hw2
    obtain ⟨hmem, haw, hcw⟩ := hw2
    set y := ((R.atlas.A a).symm (t.val, w)).2
    have hyw : (R.atlas.A a (t, y)).2 = w := by rw [haw]
    simp only [Function.comp_apply]
    rw [← hcw, b66g_deck_value R t g c d y hmem.2]
    have h1 := b66g_deck_value R t g a b y hmem.1
    rw [hyw] at h1
    rw [h1]
    change _ = (R.atlas.A d ((R.atlas.A b).symm
      (t.val, (R.atlas.A b (t, g • y)).2))).2
    rw [show (t.val, (R.atlas.A b (t, g • y)).2) = R.atlas.A b (t, g • y) from
      Prod.ext (R.atlas.hparam b _ hw1.2).symm rfl, (R.atlas.A b).left_inv hw1.2]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  have hva : fderiv ℂ (b66k_transition R a c) (t.val, z) (0, 1) = b66k_vertical R t a c x := by
    change _ = fderiv ℂ (b66k_transition R a c) (R.atlas.A a (t, x)) (0, 1)
    rw [show (t.val, z) = R.atlas.A a (t, x) from Prod.ext (R.atlas.hparam a _ ha).symm rfl]
  have hvb : fderiv ℂ (b66k_transition R b d) (t.val, b66k_deckCoordinate R t g a b z) (0, 1) =
      b66k_vertical R t b d (g • x) := by
    change _ = fderiv ℂ (b66k_transition R b d) (R.atlas.A b (t, g • x)) (0, 1)
    rw [hDv, show (t.val, (R.atlas.A b (t, g • x)).2) = R.atlas.A b (t, g • x) from
      Prod.ext (R.atlas.hparam b _ hb).symm rfl]
  rw [hva, hvb, hpc] at hfin
  exact hfin

/-- The pulled-back splitting minus the original and the holomorphic deck correction. -/
def b66g_pulled (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (g : b4b_Group)
    (v : b66k_Index R → ℂ → ℂ) (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (a b : b66k_Index R) (z : ℂ) : ℂ :=
  v b (b66k_deckCoordinate R t g a b z) / deriv (b66k_deckCoordinate R t g a b) z -
    v a z - V a b z / deriv (b66k_deckCoordinate R t g a b) z

theorem b66g_pulled_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    (a b c d : b66k_Index R) (x : R.C) (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    b66g_pulled R t g v V c d (R.atlas.A c (t, x)).2 =
      b66k_vertical R t a c x * b66g_pulled R t g v V a b (R.atlas.A a (t, x)).2 := by
  have hch := b66g_deck_chain R t g a b c d x ha hc hb hd
  have hne1 := b66g_deck_ne R t g a b _ (b66g_refinement_point R t g a b x ha hb)
  have hne2 := b66g_deck_ne R t g c d _ (b66g_refinement_point R t g c d x hc hd)
  have hac := hv a c x hx ha hc
  have hbd := hv b d (g • x) hgx hb hd
  have hdi := hV a b c d x ha hc hb hd
  simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A c).source from ⟨ha, hc⟩),
    ite_eq_left (show (t, g • x) ∈ (R.atlas.A b).source ∩
      (R.atlas.A d).source from ⟨hb, hd⟩)] at hac hbd
  unfold b66g_pulled
  rw [b66g_deck_value R t g a b x ha, b66g_deck_value R t g c d x hc]
  rw [hac, hbd] at hdi
  set A' := deriv (b66k_deckCoordinate R t g a b) (R.atlas.A a (t, x)).2
  set C' := deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2
  set vb := v b (R.atlas.A b (t, g • x)).2
  set Vab := V a b (R.atlas.A a (t, x)).2
  rw [← sub_eq_zero]
  have hE : A' * v d (R.atlas.A d (t, g • x)).2 - A' * C' * v c (R.atlas.A c (t, x)).2 -
      A' * V c d (R.atlas.A c (t, x)).2 - b66k_vertical R t a c x * C' * vb +
      b66k_vertical R t a c x * A' * C' * v a (R.atlas.A a (t, x)).2 +
      b66k_vertical R t a c x * C' * Vab = 0 := by
    linear_combination (-A') * hdi - (vb - Vab) * hch
  have hq : v d (R.atlas.A d (t, g • x)).2 / C' - v c (R.atlas.A c (t, x)).2 -
      V c d (R.atlas.A c (t, x)).2 / C' -
      b66k_vertical R t a c x * (vb / A' - v a (R.atlas.A a (t, x)).2 - Vab / A') =
      (A' * v d (R.atlas.A d (t, g • x)).2 - A' * C' * v c (R.atlas.A c (t, x)).2 -
      A' * V c d (R.atlas.A c (t, x)).2 - b66k_vertical R t a c x * C' * vb +
      b66k_vertical R t a c x * A' * C' * v a (R.atlas.A a (t, x)).2 +
      b66k_vertical R t a c x * C' * Vab) / (A' * C') := by
    field_simp
    ring
  rw [hq, hE, zero_div]

/-- Coefficient of the meromorphic one-form built from the pulled-back splitting. -/
def b66g_omega (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (g : b4b_Group)
    (v : b66k_Index R → ℂ → ℂ) (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (P : b66g_Coeff R) (a b : b66k_Index R) (z : ℂ) : ℂ :=
  b66g_pulled R t g v V a b z * P a ((R.atlas.A a).symm (t.val, z)).2

theorem b66g_omega_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2)
    (a b c d : b66k_Index R) (x : R.C) (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    b66g_omega R t g v V P a b (R.atlas.A a (t, x)).2 =
      b66k_vertical R t a c x * b66g_omega R t g v V P c d (R.atlas.A c (t, x)).2 := by
  have hlaw := b66g_pulled_law R t h g S v hv V hV a b c d x hx hgx ha hc hb hd
  obtain ⟨_, hPl, _⟩ := b66g_forms_spec R t 2 hP
  unfold b66g_omega
  rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t c x hc).2, hlaw,
    hPl a c x ha hc]
  ring

theorem b66g_omega_mero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66k_refinementDomain R t g a b))
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t g a b) :
    MeromorphicAt (b66g_omega R t g v V P a b) z := by
  obtain ⟨hPa, _, _⟩ := b66g_forms_spec R t 2 hP
  have hD := b66k_deckCoordinate_analytic R t g a b z hz
  have hDz : b66k_deckCoordinate R t g a b z ∈ b66k_domain R t b := by
    have := (b66g_deck_inverse R t g a b z hz).1
    exact this.1
  have h1 : MeromorphicAt (fun w => v b (b66k_deckCoordinate R t g a b w)) z :=
    (hmero b _ hDz).comp_analyticAt hD
  have hd : MeromorphicAt (deriv (b66k_deckCoordinate R t g a b)) z := hD.deriv.meromorphicAt
  unfold b66g_omega b66g_pulled
  exact (((h1.div hd).sub (hmero a z hz.1)).sub ((hVa a b z hz).meromorphicAt.div hd)).mul
    (hPa a z hz.1).meromorphicAt

theorem b66g_omega_analytic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66k_refinementDomain R t g a b))
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2) (a b : b66k_Index R) (x : R.C)
    (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hb : (t, g • x) ∈ (R.atlas.A b).source) :
    AnalyticAt ℂ (b66g_omega R t g v V P a b) (R.atlas.A a (t, x)).2 := by
  obtain ⟨hPa, _, _⟩ := b66g_forms_spec R t 2 hP
  have hz := b66g_refinement_point R t g a b x ha hb
  have hD := b66k_deckCoordinate_analytic R t g a b _ hz
  have hDz : b66k_deckCoordinate R t g a b (R.atlas.A a (t, x)).2 ∈ b66k_domain R t b :=
    (b66g_deck_inverse R t g a b _ hz).1.1
  have hvb : AnalyticAt ℂ (v b) (b66k_deckCoordinate R t g a b (R.atlas.A a (t, x)).2) := by
    apply hreg b _ hDz
    rw [b66g_deck_value R t g a b x ha, (b66g_chart_slice R t b _ hb).2]
    exact hgx
  have hva : AnalyticAt ℂ (v a) (R.atlas.A a (t, x)).2 := by
    apply hreg a _ hz.1
    rw [(b66g_chart_slice R t a x ha).2]
    exact hx
  have hne := b66g_deck_ne R t g a b _ hz
  unfold b66g_omega b66g_pulled
  exact ((((AnalyticAt.comp (f := b66k_deckCoordinate R t g a b) hvb hD).div hD.deriv hne).sub
    hva).sub ((hVa a b _ hz).div hD.deriv hne)).mul (hPa a _ hz.1)

/-- The fibre one-form with these coefficients in centred charts. -/
def b66g_omegaForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (g : b4b_Group)
    (v : b66k_Index R → ℂ → ℂ) (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (P : b66g_Coeff R) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ := fun q =>
  b66g_omega R t g v V P q.proj.val (g • q.proj).val (R.atlas.A q.proj.val q.proj.val).2 *
    b66g_sliceD R t q.proj.val q.proj q.2

theorem b66g_omegaForm_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2)
    (p : rf8_fibre R.C t) (hp1 : p.val.2 ∉ S) (hp2 : g • p.val.2 ∉ S) (a b : b66k_Index R)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : (g • p).val ∈ (R.atlas.A b).source) (w : ℂ) :
    b66g_omegaForm R t g v V P ⟨p, w⟩ =
      b66g_omega R t g v V P a b (R.atlas.A a p.val).2 * b66g_sliceD R t a p w := by
  have hc : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hd : (g • p).val ∈ (R.atlas.A (g • p).val).source := (R.atlas.hA (g • p).val).1
  have ha' := (b66g_mem_source R t a p).mp ha
  have hc' := (b66g_mem_source R t p.val p).mp hc
  have hlaw := b66g_omega_law R t h g S v hv V hV hP a b p.val (g • p).val p.val.2 hp1 hp2
    ha' hc' hb hd
  rw [← b66g_fibre_val R t p] at hlaw
  change b66g_omega R t g v V P p.val (g • p).val (R.atlas.A p.val p.val).2 *
    b66g_sliceD R t p.val p w = _
  rw [b66g_slice_change R t a p.val p ha hc w, hlaw]
  ring

theorem b66g_lineEquiv_apply (τ : ℂ) :
    b4cov_lineEquiv (Module.finrank_self ℂ) τ = τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

theorem b66g_omegaForm_loc (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2)
    (x₀ : rf8_fibre R.C t) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_omegaForm R t g v V P) x₀ =ᶠ[𝓝[≠] 0]
      fun τ => b66g_omega R t g v V P x₀.val (g • x₀).val
        ((b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) *
        deriv (fun σ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + σ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) τ := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set a₀ := x₀.val
  set b₀ := (g • x₀).val
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t a₀ ∘ e.symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have hx₀e : x₀ ∈ e.source := mem_extChartAt_source x₀
  have hex : e x₀ ∈ e.target := e.map_source hx₀e
  have ha₀ : x₀.val ∈ (R.atlas.A a₀).source := (R.atlas.hA a₀).1
  have hb₀ : (g • x₀).val ∈ (R.atlas.A b₀).source := (R.atlas.hA b₀).1
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a₀).source ∧
      (g • y).val ∈ (R.atlas.A b₀).source} := by
    refine ((R.atlas.A a₀).open_source.preimage continuous_subtype_val).inter ?_
    exact (R.atlas.A b₀).open_source.preimage
      (continuous_subtype_val.comp (R.hG t g).continuous)
  set B : Set (rf8_fibre R.C t) :=
    (fun x : R.C => (⟨(t, x), rfl⟩ : rf8_fibre R.C t)) ''
      ((↑S : Set R.C) ∪ (fun x => g⁻¹ • x) '' (↑S : Set R.C)) \ {x₀}
  have hBf : B.Finite :=
    ((S.finite_toSet.union (S.finite_toSet.image _)).image _).sdiff
  have hBc : Bᶜ ∈ 𝓝 x₀ := by
    refine (hBf.isClosed.isOpen_compl).mem_nhds ?_
    intro hx
    exact hx.2 rfl
  have hsc : Tendsto (fun τ : ℂ => e x₀ + τ * c₀) (𝓝 0) (𝓝 (e x₀)) := by
    have : Continuous (fun τ : ℂ => e x₀ + τ * c₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e x₀ + τ * c₀)) (𝓝 0) (𝓝 x₀) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  have hev1 : ∀ᶠ τ in 𝓝 (0 : ℂ), e x₀ + τ * c₀ ∈ e.target :=
    hsc.eventually (extChartAt_target_mem_nhds' hex)
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈
      {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a₀).source ∧
        (g • y).val ∈ (R.atlas.A b₀).source} :=
    hsymc.eventually (hopen.mem_nhds ⟨ha₀, hb₀⟩)
  have hev3 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈ Bᶜ :=
    hsymc.eventually hBc
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with τ h1 h2 h3 h4
  set y := e.symm (e x₀ + τ * c₀)
  have hy : y ∈ e.source := e.map_target h1
  have hyx : y ≠ x₀ := by
    intro hyx
    have := e.right_inv h1
    rw [show e.symm (e x₀ + τ * c₀) = y from rfl, hyx] at this
    have h5 : τ * c₀ = 0 := by linear_combination -this
    exact h4 (mul_eq_zero.mp h5 |>.resolve_right hc₀)
  have hyS : y.val.2 ∉ S ∧ g • y.val.2 ∉ S := by
    constructor
    · intro hS
      exact h3 ⟨⟨y.val.2, Or.inl hS, b66g_fibre_mk R t y⟩, hyx⟩
    · intro hS
      exact h3 ⟨⟨y.val.2, Or.inr ⟨g • y.val.2, hS, inv_smul_smul g _⟩,
        b66g_fibre_mk R t y⟩, hyx⟩
  obtain ⟨hyan, _, hD⟩ := b66g_slice_chart R t a₀ x₀ y hy h2.1
  have hey : e y = e x₀ + τ * c₀ := e.right_inv h1
  have hdΦ : deriv (fun σ => hh (e x₀ + σ * c₀)) τ = deriv hh (e x₀ + τ * c₀) * c₀ := by
    rw [hey] at hyan
    have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ τ := by
      simpa using ((hasDerivAt_id τ).mul_const c₀).const_add (e x₀)
    exact (hyan.differentiableAt.hasDerivAt.comp τ hs).deriv
  change b4cov_coef (b66g_omegaForm R t g v V P) x₀ c₀
    (e x₀ + b4cov_lineEquiv (Module.finrank_self ℂ) τ) = _
  rw [b66g_lineEquiv_apply τ]
  unfold b4cov_coef
  change b66g_omegaForm R t g v V P ⟨y, b4cov_vec x₀ y c₀⟩ = _
  refine (b66g_omegaForm_apply R t h g S v hv V hV hP y hyS.1 hyS.2 a₀ b₀ h2.1 h2.2
    (b4cov_vec x₀ y c₀)).trans ?_
  have hk : b66g_sliceD R t a₀ y (b4cov_vec x₀ y c₀) = deriv hh (e x₀ + τ * c₀) * c₀ := by
    refine (hD _).trans ?_
    rw [b66g_chartD_vec R t x₀ y hy, hey]
  rw [hk, hdΦ]
  rfl

theorem b66g_omegaForm_res (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2)
    (x₀ : rf8_fibre R.C t) :
    MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_omegaForm R t g v V P) x₀) 0 ∧
    TauCeti.Contour.residue
      (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_omegaForm R t g v V P) x₀) 0 =
      TauCeti.Contour.residue (b66g_omega R t g v V P x₀.val (g • x₀).val)
        (R.atlas.A x₀.val x₀.val).2 := by
  have hloc := b66g_omegaForm_loc R t h g S v hv V hV hP x₀
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t x₀.val ∘ e.symm
  set Φ : ℂ → ℂ := fun σ => hh (e x₀ + σ * c₀)
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have ha₀ : x₀.val ∈ (R.atlas.A x₀.val).source := (R.atlas.hA x₀.val).1
  obtain ⟨hhan, hhd, _⟩ := b66g_slice_chart R t x₀.val x₀ x₀ (mem_extChartAt_source x₀) ha₀
  have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c₀).const_add (e x₀)
  have hsa : AnalyticAt ℂ (fun σ : ℂ => e x₀ + σ * c₀) 0 := by fun_prop
  have hh0 : (fun σ : ℂ => e x₀ + σ * c₀) 0 = e x₀ := by simp
  have hhan' : AnalyticAt ℂ hh ((fun σ : ℂ => e x₀ + σ * c₀) 0) := by
    rw [hh0]
    exact hhan
  have hΦ : AnalyticAt ℂ Φ 0 := AnalyticAt.comp (f := fun σ : ℂ => e x₀ + σ * c₀) hhan' hsa
  have hΦd : deriv Φ 0 ≠ 0 := by
    change deriv (hh ∘ fun σ : ℂ => e x₀ + σ * c₀) 0 ≠ 0
    rw [(hhan'.differentiableAt.hasDerivAt.comp 0 hs).deriv]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero hhd hc₀
  have hΦ0 : Φ 0 = (R.atlas.A x₀.val x₀.val).2 := by
    simp only [Φ, hh, zero_mul, add_zero, Function.comp_apply,
      e.left_inv (mem_extChartAt_source x₀)]
    rfl
  have hgx : (g • x₀).val ∈ (R.atlas.A (g • x₀).val).source := (R.atlas.hA (g • x₀).val).1
  have hz : (R.atlas.A x₀.val x₀.val).2 ∈ b66k_refinementDomain R t g x₀.val (g • x₀).val := by
    have := b66g_refinement_point R t g x₀.val (g • x₀).val x₀.val.2
      ((b66g_mem_source R t _ x₀).mp ha₀) hgx
    rwa [← b66g_fibre_val R t x₀] at this
  have hm := b66g_omega_mero R t g v hmero V hVa hP x₀.val (g • x₀).val _ hz
  rw [← hΦ0] at hm
  have hcm : MeromorphicAt (fun τ => b66g_omega R t g v V P x₀.val (g • x₀).val (Φ τ) *
      deriv Φ τ) 0 :=
    (hm.comp_analyticAt hΦ).mul hΦ.deriv.meromorphicAt
  refine ⟨hcm.congr hloc.symm, ?_⟩
  rw [TauCeti.Contour.residue_congr_nhdsNE hloc, ← hΦ0]
  exact b66g_residue_comp hΦ hΦd hm

theorem b66g_omegaForm_lin (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (g : b4b_Group)
    (v : b66k_Index R → ℂ → ℂ) (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (P : b66g_Coeff R) (x : rf8_fibre R.C t) (c u w : ℂ) :
    b66g_omegaForm R t g v V P ⟨x, c * u + w⟩ =
      c * b66g_omegaForm R t g v V P ⟨x, u⟩ + b66g_omegaForm R t g v V P ⟨x, w⟩ := by
  unfold b66g_omegaForm
  simp only
  rw [b66g_clm_apply (b66g_sliceD R t x.val x) (c * u + w),
    b66g_clm_apply (b66g_sliceD R t x.val x) u, b66g_clm_apply (b66g_sliceD R t x.val x) w]
  ring

/-- The fibre point over a retained surface point. -/
def b66g_pt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) : R.C ↪ rf8_fibre R.C t where
  toFun x := ⟨(t, x), rfl⟩
  inj' _ _ hxy := congrArg (fun p : rf8_fibre R.C t => p.val.2) hxy

theorem b66g_omega_residue_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2) :
    ∑ x ∈ S ∪ S.image (fun x => g⁻¹ • x), TauCeti.Contour.residue
      (b66g_omega R t g v V P (t, x) (t, g • x)) (R.atlas.A (t, x) (t, x)).2 = 0 := by
  set θ := b66g_omegaForm R t g v V P
  have hres := b66g_omegaForm_res R t h g S v hmero hv V hVa hV hP
  have hlin : HurwitzPrymRR_IsLinear θ := fun x c u w => b66g_omegaForm_lin R t g v V P x c u w
  let w : b4c_MeroForm ℂ (rf8_fibre R.C t) (Module.finrank_self ℂ) :=
    ⟨θ, hlin, fun x => (hres x).1⟩
  have hsum := b4c_residue_sum (Module.finrank_self ℂ) w
  set F := S ∪ S.image (fun x => g⁻¹ • x)
  have hsupp : Function.support (fun x => b4c_res (hE := Module.finrank_self ℂ)
      (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) x) ⊆ ↑(F.map (b66g_pt R t)) := by
    intro p hp
    by_contra hnot
    apply hp
    have hpF : p.val.2 ∉ F := by
      intro hm
      apply hnot
      refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨p.val.2, hm, ?_⟩)
      exact b66g_fibre_mk R t p
    have h1 : p.val.2 ∉ S := fun hS => hpF (Finset.mem_union_left _ hS)
    have h2 : g • p.val.2 ∉ S := fun hS => hpF (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨g • p.val.2, hS, inv_smul_smul g _⟩))
    change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 0
    rw [(hres p).2]
    apply TauCeti.Contour.residue_eq_zero_of_analyticAt
    have ha : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
    have hb : (g • p).val ∈ (R.atlas.A (g • p).val).source := (R.atlas.hA (g • p).val).1
    have han := b66g_omega_analytic R t g S v hreg V hVa hP p.val (g • p).val p.val.2 h1 h2
      ((b66g_mem_source R t _ p).mp ha) hb
    rwa [← b66g_fibre_val R t p] at han
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map] at hsum
  refine Eq.trans ?_ hsum
  refine Finset.sum_congr rfl fun x _ => ?_
  exact ((hres (b66g_pt R t x)).2).symm

theorem b66g_vertical_self (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (b : b66k_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_vertical R t b b x = 1 := by
  have hu : R.atlas.A b (t, x) ∈ (R.atlas.A b).target := (R.atlas.A b).map_source hb
  have he : b66k_transition R b b =ᶠ[𝓝 (R.atlas.A b (t, x))] Prod.snd := by
    filter_upwards [(R.atlas.A b).open_target.mem_nhds hu] with u hu'
    change (R.atlas.A b ((R.atlas.A b).symm u)).2 = u.2
    rw [(R.atlas.A b).right_inv hu']
  unfold b66k_vertical
  rw [he.fderiv_eq, fderiv_snd]
  rfl

theorem b66g_pull_chart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2) (g : b4b_Group) (a b : b66k_Index R)
    (y : R.C) (hb : (t, y) ∈ (R.atlas.A b).source) (ha : (t, g • y) ∈ (R.atlas.A a).source) :
    b66g_pull R t 2 g P b y =
      P a (g • y) * deriv (b66k_deckCoordinate R t g b a) (R.atlas.A b (t, y)).2 ^ 2 := by
  obtain ⟨_, hPl, _⟩ := b66g_forms_spec R t 2 hP
  have hc : (t, g • y) ∈ (R.atlas.A (t, g • y)).source := (R.atlas.hA _).1
  have hch := b66g_deck_chain R t g b a b (t, g • y) y hb hb ha hc
  rw [b66g_vertical_self R t b y hb, mul_one] at hch
  change (if (t, y) ∈ (R.atlas.A b).source then P (t, g • y) (g • y) *
    deriv (b66k_deckCoordinate R t g b (t, g • y)) (R.atlas.A b (t, y)).2 ^ 2 else 0) = _
  rw [ite_eq_left hb, hch, hPl a (t, g • y) (g • y) ha hc]
  ring

theorem b66g_residueSum_extend (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S T : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hST : S ⊆ T) :
    b66g_residueSum R t T v q = b66g_residueSum R t S v q := by
  obtain ⟨hqa, _, _⟩ := b66g_forms_spec R t m hq
  unfold b66g_residueSum
  symm
  refine Finset.sum_subset hST fun x _ hx => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66g_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  apply TauCeti.Contour.residue_eq_zero_of_analyticAt
  refine (hreg (t, x) _ hdom ?_).mul (hqa (t, x) _ hdom)
  rw [(b66g_chart_slice R t (t, x) x hxa).2]
  exact hx

theorem b66g_residue_pull_inv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (V : b66k_Index R → b66k_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66g_Coeff R} (hP : P ∈ b66g_forms R t 2)
    (hPg : b66g_pull R t 2 g⁻¹ P ∈ b66g_forms R t 2) :
    b66g_residueSum R t S v (b66g_pull R t 2 g⁻¹ P) = b66g_residueSum R t S v P := by
  obtain ⟨hPa, _, _⟩ := b66g_forms_spec R t 2 hP
  obtain ⟨hQa, _, _⟩ := b66g_forms_spec R t 2 hPg
  set Q := b66g_pull R t 2 g⁻¹ P
  set F := S ∪ S.image (fun x => g⁻¹ • x)
  have hzero := b66g_omega_residue_sum R t h g S v hmero hreg hv V hVa hV hP
  have hterm : ∀ x : R.C, TauCeti.Contour.residue
      (b66g_omega R t g v V P (t, x) (t, g • x)) (R.atlas.A (t, x) (t, x)).2 =
      TauCeti.Contour.residue (fun w => v (t, g • x) w *
        Q (t, g • x) ((R.atlas.A (t, g • x)).symm (t.val, w)).2)
        (R.atlas.A (t, g • x) (t, g • x)).2 -
      TauCeti.Contour.residue (fun z => v (t, x) z *
        P (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 := by
    intro x
    set a : b66k_Index R := (t, x)
    set b : b66k_Index R := (t, g • x)
    have ha : (t, x) ∈ (R.atlas.A a).source := (R.atlas.hA a).1
    have hb : (t, g • x) ∈ (R.atlas.A b).source := (R.atlas.hA b).1
    set z₀ := (R.atlas.A a (t, x)).2
    set D := b66k_deckCoordinate R t g a b
    have hz := b66g_refinement_point R t g a b x ha hb
    have hDa := b66k_deckCoordinate_analytic R t g a b z₀ hz
    have hne := b66g_deck_ne R t g a b z₀ hz
    have hDz : D z₀ = (R.atlas.A b (t, g • x)).2 := b66g_deck_value R t g a b x ha
    have hDdom : D z₀ ∈ b66k_domain R t b := (b66g_deck_inverse R t g a b z₀ hz).1.1
    set f1 : ℂ → ℂ := fun z => v b (D z) / deriv D z * P a ((R.atlas.A a).symm (t.val, z)).2
    set f2 : ℂ → ℂ := fun z => v a z * P a ((R.atlas.A a).symm (t.val, z)).2
    set f3 : ℂ → ℂ := fun z => V a b z / deriv D z * P a ((R.atlas.A a).symm (t.val, z)).2
    have hsplit : b66g_omega R t g v V P a b = f1 - f2 - f3 := by
      funext z
      simp only [b66g_omega, b66g_pulled, f1, f2, f3, Pi.sub_apply, D]
      ring
    have hPz := (hPa a z₀ hz.1).meromorphicAt
    have hm1 : MeromorphicAt f1 z₀ :=
      ((((hmero b _ hDdom).comp_analyticAt hDa).div hDa.deriv.meromorphicAt)).mul hPz
    have hm2 : MeromorphicAt f2 z₀ := (hmero a z₀ hz.1).mul hPz
    have ha3 : AnalyticAt ℂ f3 z₀ := ((hVa a b z₀ hz).div hDa.deriv hne).mul (hPa a z₀ hz.1)
    rw [hsplit, TauCeti.Contour.residue_sub (hm1.sub hm2) ha3.meromorphicAt,
      TauCeti.Contour.residue_sub hm1 hm2, TauCeti.Contour.residue_eq_zero_of_analyticAt ha3,
      sub_zero]
    congr 1
    set Fb : ℂ → ℂ := fun w => v b w * Q b ((R.atlas.A b).symm (t.val, w)).2
    have hFm : MeromorphicAt Fb (D z₀) := (hmero b _ hDdom).mul (hQa b _ hDdom).meromorphicAt
    rw [← hDz, ← b66g_residue_comp hDa hne hFm]
    apply TauCeti.Contour.residue_congr_nhdsNE
    apply nhdsWithin_le_nhds
    filter_upwards [b66g_refinement_eventually R t g a b z₀ hz] with z hzz
    obtain ⟨hDzz, _, hinv⟩ := b66g_deck_inverse R t g a b z hzz
    have hxz := b66k_inverse_slice R t a z hzz.1
    set y := ((R.atlas.A a).symm (t.val, z)).2
    have hya : (t, y) ∈ (R.atlas.A a).source := by
      rw [hxz]
      exact (R.atlas.A a).map_target hzz.1
    have hyz : (R.atlas.A a (t, y)).2 = z := by rw [hxz, (R.atlas.A a).right_inv hzz.1]
    have hgy : (t, g • y) ∈ (R.atlas.A b).source := hzz.2
    have hDy : D z = (R.atlas.A b (t, g • y)).2 := by
      rw [← hyz]
      exact b66g_deck_value R t g a b y hya
    have hsy : ((R.atlas.A b).symm (t.val, D z)).2 = g • y := by
      rw [hDy]
      exact (b66g_chart_slice R t b (g • y) hgy).2
    have hpc := b66g_pull_chart R t hP g⁻¹ a b (g • y) hgy (by rwa [inv_smul_smul])
    rw [inv_smul_smul] at hpc
    have hpc' : Q b (g • y) = P a y *
        deriv (b66k_deckCoordinate R t g⁻¹ b a) (R.atlas.A b (t, g • y)).2 ^ 2 := hpc
    have hne' := b66g_deck_ne R t g a b z hzz
    simp only [Fb, f1]
    rw [hsy, hpc', ← hDy]
    have hinv' : deriv (b66k_deckCoordinate R t g⁻¹ b a) (D z) = (deriv D z)⁻¹ :=
      eq_inv_of_mul_eq_one_left hinv
    rw [hinv']
    simp only [D] at hne' ⊢
    field_simp
    rfl
  have hsum := Finset.sum_congr rfl fun x (_ : x ∈ F) => hterm x
  rw [Finset.sum_sub_distrib] at hsum
  rw [hzero] at hsum
  have h1 : ∑ x ∈ F, TauCeti.Contour.residue (fun z => v (t, x) z *
      P (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 =
      b66g_residueSum R t S v P :=
    b66g_residueSum_extend R t S F v hreg hP Finset.subset_union_left
  have h2 : ∑ x ∈ F, TauCeti.Contour.residue (fun w => v (t, g • x) w *
      Q (t, g • x) ((R.atlas.A (t, g • x)).symm (t.val, w)).2)
        (R.atlas.A (t, g • x) (t, g • x)).2 = b66g_residueSum R t S v Q := by
    have hinj : Set.InjOn (fun x : R.C => g • x) ↑F := fun x _ y _ hxy => smul_left_cancel g hxy
    rw [← b66g_residueSum_extend R t S (F.image (fun x => g • x)) v hreg hPg ?_]
    · unfold b66g_residueSum
      rw [Finset.sum_image hinj]
    · intro y hy
      refine Finset.mem_image.mpr ⟨g⁻¹ • y, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩), smul_inv_smul g y⟩
  rw [h1, h2] at hsum
  exact sub_eq_zero.mp hsum.symm

theorem b66g_residueSum_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (c : ℂ) (q : b66g_Coeff R) :
    b66g_residueSum R t S v (c • q) = c * b66g_residueSum R t S v q := by
  unfold b66g_residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TauCeti.Contour.residue_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem b66g_residueSum_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    {ι : Type} (s : Finset ι) (q : ι → b66g_Coeff R) (hq : ∀ i, q i ∈ b66g_forms R t 2) :
    b66g_residueSum R t S v (∑ i ∈ s, q i) = ∑ i ∈ s, b66g_residueSum R t S v (q i) := by
  unfold b66g_residueSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66g_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  have hm : ∀ i ∈ s, MeromorphicAt (fun z => v (t, x) z *
      q i (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 :=
    fun i _ => (hmero (t, x) _ hdom).mul
      ((b66g_forms_spec R t 2 (hq i)).1 (t, x) _ hdom).meromorphicAt
  rw [← TauCeti.Contour.residue_sum s hm]
  congr 1
  funext z
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]

theorem b66g_invariant_primitive_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (q r : b66g_primitiveForms R t) :
    ∃ Q : b66g_forms R t 2,
      Q.val = b66g_average R t (b66g_product R q.val r.val) ∧
      (∀ g : b4b_Group, b66g_pull R t 2 g Q.val = Q.val) ∧
      b66g_residueSum R t S v Q.val =
        b66g_residueSum R t S v (b66g_product R q.val r.val) := by
  have hq : q.val ∈ b66g_forms R t 1 := (Submodule.mem_inf.mp q.property).1
  have hr : r.val ∈ b66g_forms R t 1 := (Submodule.mem_inf.mp r.property).1
  obtain ⟨hmem, hinv⟩ := b66g_average_product R t hq hr
  refine ⟨⟨_, hmem⟩, rfl, hinv, ?_⟩
  set P := b66g_product R q.val r.val
  have hP : P ∈ b66g_forms R t 2 := (b66g_cup_aux R t).2 ⟨_, hq⟩ ⟨_, hr⟩
  have hPg : ∀ g : b4b_Group, b66g_pull R t 2 g P ∈ b66g_forms R t 2 := fun g => by
    rw [b66g_pull_product]
    exact (b66g_cup_aux R t).2 ⟨_, b66g_pull_one_mem R t hq g⟩ ⟨_, b66g_pull_one_mem R t hr g⟩
  have heach : ∀ g : b4b_Group, b66g_residueSum R t S v (b66g_pull R t 2 g P) =
      b66g_residueSum R t S v P := by
    intro g
    obtain ⟨V, hVa, hV⟩ := b66k_deck_invariant R t h g⁻¹
    have := b66g_residue_pull_inv R t h g⁻¹ S v hmero hreg hv V hVa hV hP
      (by rw [inv_inv]; exact hPg g)
    rwa [inv_inv] at this
  change b66g_residueSum R t S v (b66g_average R t P) = _
  rw [b66g_average_apply, b66g_residueSum_smul,
    b66g_residueSum_sum R t S v hmero Finset.univ _ hPg]
  simp only [heach, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card b4b_Group : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  rfl

section B66gMittagLeffler
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem b66g_principalClass_top [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (x₀ : C) : ∃ m : ℕ, LinearMap.range (RiemannRochAna_principalClassLinear
      (Module.finrank_self ℂ) (Finsupp.single x₀ (m : ℤ)) : _ →ₗ[ℂ] b4c_Dolbeault01 ℂ C) = ⊤ := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := RiemannRochAna_exists_single_holResidueKernel_bot (C := C) hE x₀
  refine ⟨m, ?_⟩
  set D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  have hD : ∀ y, 0 ≤ D y := by
    intro y
    simp only [D, Finsupp.single_apply]
    split_ifs <;> positivity
  have : Module.Finite ℂ (b4c_Dolbeault01 ℂ C) := (b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).1
  have h1 := RiemannRochAna_principalResidue_rank_add_holKernel (C := C) hE D
  rw [hm, finrank_bot, add_zero] at h1
  have hk := RiemannRochAna_principalClass_kernel_eq_residueKernel_effective hE D hD x₀
  have hc := (RiemannRochAna_principalClassLinear hE D).finrank_range_add_finrank_ker
  have hr := (RiemannRochAna_principalResidueLinear hE D).finrank_range_add_finrank_ker
  rw [hk] at hc
  apply Submodule.eq_top_of_finrank_eq
  rw [(b4c_dolbeault_finite_aux (E := ℂ) (C := C) hE).2]
  omega

theorem b66g_mittagLeffler [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (γ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (hγ : γ ∈ b4c_Smooth01 ℂ C) (x₀ : C) :
    ∃ F P : C → ℂ, ∃ N : ℕ, ∃ c : Fin N → ℂ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y) ∧
      (∀ y, y ≠ x₀ → ∀ v : ℂ, b4c_dbar ℂ C (F + P) ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      (∀ᶠ y in 𝓝 x₀, ∀ v : ℂ, b4c_dbar ℂ C F ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      P =ᶠ[𝓝 x₀] fun y => ∑ n, c n /
        RiemannRochAna_coordinate (Module.finrank_self ℂ) x₀ y ^ ((n : ℕ) + 1) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := b66g_principalClass_top (C := C) x₀
  set D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  let g : b4c_Smooth01 ℂ C := ⟨γ, hγ⟩
  have hg : (Submodule.mkQ _ g : b4c_Dolbeault01 ℂ C) ∈
      LinearMap.range (RiemannRochAna_principalClassLinear hE D) := by
    rw [hm]
    trivial
  obtain ⟨c', hc'⟩ := hg
  have hdiff : g - RiemannRochAna_principalObstructionLinear hE D c' ∈
      (Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
        (b4c_Smooth01 ℂ C).subtype := by
    rw [← Submodule.Quotient.eq]
    exact hc'.symm
  have hmem : γ - (RiemannRochAna_principalObstructionLinear hE D c').1 ∈
      b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) := by
    rw [← b4c_dbar_image_eq hE]
    exact hdiff
  obtain ⟨F, hF, hFd⟩ := hmem
  have hsupp : ∀ i : D.support, i.1 = x₀ := by
    intro i
    have := Finsupp.support_single_subset i.2
    simpa using this
  refine ⟨F, RiemannRochAna_principalScalar hE D c', ?_⟩
  have hoff : ∀ y, y ≠ x₀ → y ∉ D.support := fun y hy hyD => hy (hsupp ⟨y, hyD⟩)
  have hP : ∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (RiemannRochAna_principalScalar hE D c') y := fun y hy =>
    RiemannRochAna_principalScalar_smooth_off_support hE D c' y (hoff y hy)
  have hdF : ∀ q, b4c_dbar ℂ C F q = γ q - (RiemannRochAna_principalObstructionLinear hE D c').1 q :=
    fun q => congrFun hFd q
  have hnear : ∀ᶠ y in 𝓝 x₀, ∀ v : ℂ,
      (RiemannRochAna_principalObstructionLinear hE D c').1 ⟨y, v⟩ = 0 := by
    have hall : ∀ᶠ y in 𝓝 x₀, ∀ (i : D.support) (n : Fin (Int.toNat (D i.1))) (v : ℂ),
        RiemannRochAna_principalObstructionPow hE i.1
          (RiemannRochAna_divisorCutoff hE D i) n ⟨y, v⟩ = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro n
      have h := RiemannRochAna_principalObstructionPow_zero_germ hE i.1
        (RiemannRochAna_divisorCutoff hE D i) n (RiemannRochAna_divisorCutoff_spec hE D i).2.1
      have hx : (i : C) = x₀ := hsupp i
      exact hx ▸ h
    filter_upwards [hall] with y hy v
    rw [RiemannRochAna_principalObstructionLinear_apply]
    simp only [hy, mul_zero, Finset.sum_const_zero]
  by_cases hx : x₀ ∈ D.support
  · let i : D.support := ⟨x₀, hx⟩
    refine ⟨Int.toNat (D x₀), c' i, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · have hFm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y := (hF y).mdifferentiableAt (by simp)
      have hPm := (hP y hy).mdifferentiableAt (by simp)
      rw [RiemannRochAna_dbar_add_at _ _ y hFm hPm v, hdF,
        RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v]
      ring
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · exact RiemannRochAna_principalScalar_germ hE D c' i
  · have hzero : RiemannRochAna_principalScalar hE D c' = 0 := by
      funext y
      apply Finset.sum_eq_zero
      intro i _
      exact absurd (hsupp i ▸ i.2) hx
    refine ⟨0, Fin.elim0, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · rw [hzero, add_zero, hdF]
      have := RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v
      rw [hzero] at this
      rw [← this]
      have h0 := RiemannRochAna_dbar_const_germ (E := ℂ) (C := C) (u := (0 : C → ℂ)) (x := y)
        (a := 0) (Filter.EventuallyEq.refl _ _) v
      rw [h0, sub_zero]
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · rw [hzero]
      exact Filter.Eventually.of_forall fun y => by simp

end B66gMittagLeffler

section B66gSmoothing
attribute [local instance] b3Forms_isManifold_real

theorem b66g_scalarCycles_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {u : b66k_Cochain R} (hu : u ∈ b66g_scalarCycles R t) :
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b)) ∧
    (∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0) ∧
    ∀ a b c x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → (t, x) ∈ (R.atlas.A c).source →
      u a c x = u b c x + u a b x := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hu
  | zero => exact ⟨fun a b z _ => analyticAt_const, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩
  | add u w _ _ hu hw =>
    refine ⟨fun a b => (hu.1 a b).add (hw.1 a b), fun a b x hx => ?_,
      fun a b c x ha hb hc => ?_⟩
    · simp only [Pi.add_apply]
      rw [hu.2.1 a b x hx, hw.2.1 a b x hx, add_zero]
    · simp only [Pi.add_apply]
      rw [hu.2.2 a b c x ha hb hc, hw.2.2 a b c x ha hb hc]
      ring
  | smul k u _ hu =>
    refine ⟨fun a b => (hu.1 a b).const_smul (c := k), fun a b x hx => ?_,
      fun a b c x ha hb hc => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu.2.1 a b x hx, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hu.2.2 a b c x ha hb hc]
      ring

theorem b66g_inv_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ((R.atlas.A a).symm (t.val, b66g_slice R t a y)).2 = y.val.2 := by
  change ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2)).2 = _
  rw [← b66g_slice_value R t a y hy, (R.atlas.A a).left_inv hy]

theorem b66g_slice_domain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    b66g_slice R t a y ∈ b66k_domain R t a := by
  change (t.val, (R.atlas.A a y.val).2) ∈ (R.atlas.A a).target
  rw [← b66g_slice_value R t a y hy]
  exact (R.atlas.A a).map_source hy

theorem b66g_open_source (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
  (R.atlas.A a).open_source.preimage continuous_subtype_val

theorem b66g_cochain_holo (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (c b : b66k_Index R)
    (hu : AnalyticOnNhd ℂ (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 c b))
    (y : rf8_fibre R.C t) (hc : y.val ∈ (R.atlas.A c).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : rf8_fibre R.C t => u c b y.val.2) y := by
  have hz : b66g_slice R t c y ∈ b66k_refinementDomain R t 1 c b := by
    refine ⟨b66g_slice_domain R t c y hc, ?_⟩
    rw [b66g_inv_slice R t c y hc, one_smul, ← b66g_fibre_val R t y]
    exact hb
  have han := hu _ hz
  have hF : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2) (b66g_slice R t c y) :=
    han.contDiffAt.contMDiffAt
  apply (hF.comp y (b66g_slice_contMDiffAt R t c y hc)).congr_of_eventuallyEq
  filter_upwards [(b66g_open_source R t c).mem_nhds hc] with y' hy'
  simp only [Function.comp_apply, b66g_inv_slice R t c y' hy']

/-- Partition-of-unity splitting of a scalar cochain. -/
def b66g_tau (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (s : b66k_Cochain R) (b : b66k_Index R) (y : rf8_fibre R.C t) : ℂ :=
  -∑ᶠ c, ρ c y • s c b y.val.2

theorem b66g_tau_smooth (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (b : b66k_Index R)
    (y : rf8_fibre R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66g_tau R t ρ s b) y := by
  have hsa := (b66g_scalarCycles_spec R t hs).1
  apply ContMDiffAt.neg
  apply ρ.contMDiffAt_finsum
  intro c hc
  exact (b3A_contMDiffWithinAt_real
    (b66g_cochain_holo R t s c b (hsa c b) y (hρ c hc) hb)).of_le (by simp)

theorem b66g_tau_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (a b : b66k_Index R)
    (y : rf8_fibre R.C t) (ha : y.val ∈ (R.atlas.A a).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    b66g_tau R t ρ s a y - b66g_tau R t ρ s b y = s a b y.val.2 := by
  have hlaw := (b66g_scalarCycles_spec R t hs).2.2
  have hfin : (Function.support fun c => ρ c y).Finite := ρ.locallyFinite.point_finite y
  have hf1 : (Function.support fun c => ρ c y • s c a y.val.2).Finite :=
    hfin.subset fun c hc => by
      simp only [Function.mem_support] at hc ⊢
      exact fun h => hc (by rw [h, zero_smul])
  have hf2 : (Function.support fun c => ρ c y • s c b y.val.2).Finite :=
    hfin.subset fun c hc => by
      simp only [Function.mem_support] at hc ⊢
      exact fun h => hc (by rw [h, zero_smul])
  have hterm : ∀ c, ρ c y • s c b y.val.2 - ρ c y • s c a y.val.2 =
      ρ c y • s a b y.val.2 := by
    intro c
    by_cases h0 : ρ c y = 0
    · simp [h0]
    · have hyc : y.val ∈ (R.atlas.A c).source :=
        hρ c (subset_tsupport _ (Function.mem_support.mpr h0))
      rw [← smul_sub]
      congr 1
      rw [b66g_fibre_val R t y] at ha hb hyc
      rw [hlaw c a b y.val.2 hyc ha hb]
      ring
  unfold b66g_tau
  rw [neg_sub_neg, ← finsum_sub_distrib hf2 hf1]
  simp only [hterm]
  rw [← finsum_smul, ρ.sum_eq_one (mem_univ y), one_smul]

/-- The glued conjugate differential of the splitting. -/
def b66g_gamma (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (s : b66k_Cochain R) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ :=
  fun p => b4c_dbar ℂ (rf8_fibre R.C t) (b66g_tau R t ρ s p.1.val) p

theorem b66g_gamma_local (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (b : b66k_Index R)
    (y : rf8_fibre R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ∀ᶠ y' in 𝓝 y, ∀ v : ℂ, b66g_gamma R t ρ s ⟨y', v⟩ =
      b4c_dbar ℂ (rf8_fibre R.C t) (b66g_tau R t ρ s b) ⟨y', v⟩ := by
  have hsa := (b66g_scalarCycles_spec R t hs).1
  filter_upwards [(b66g_open_source R t b).mem_nhds hb] with y' hy' v
  have ha : y'.val ∈ (R.atlas.A y'.val).source := (R.atlas.hA y'.val).1
  have heq : b66g_tau R t ρ s y'.val =ᶠ[𝓝 y']
      b66g_tau R t ρ s b + fun y'' => s y'.val b y''.val.2 := by
    filter_upwards [(b66g_open_source R t y'.val).mem_nhds ha,
      (b66g_open_source R t b).mem_nhds hy'] with y'' h1 h2
    have := b66g_tau_sub R t ρ hρ hs y'.val b y'' h1 h2
    simp only [Pi.add_apply]
    linear_combination this
  change b4c_dbar ℂ (rf8_fibre R.C t) (b66g_tau R t ρ s y'.val) ⟨y', v⟩ = _
  rw [RiemannRochAna_dbar_congr heq v]
  have hS := b66g_cochain_holo R t s y'.val b (hsa _ _) y' ha hy'
  rw [RiemannRochAna_dbar_add_at _ _ y'
    ((b66g_tau_smooth R t ρ hρ hs b y' hy').mdifferentiableAt (by simp))
    ((b3A_contMDiffWithinAt_real hS).mdifferentiableWithinAt (by simp) |>.mdifferentiableAt
      Filter.univ_mem) v,
    RiemannRochAna_dbar_holomorphic_at _ y' (hS.mdifferentiableAt (by simp)) v, add_zero]

theorem b66g_gamma_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) :
    b66g_gamma R t ρ s ∈ b4c_Smooth01 ℂ (rf8_fibre R.C t) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  refine ⟨fun p => ?_, fun x a v w => ?_⟩
  · set b := p.1.val
    have hb : p.1.val ∈ (R.atlas.A b).source := (R.atlas.hA b).1
    obtain ⟨χ, hχ, hχ1, hχs⟩ := RiemannRochAna_cutoff hE p.1
      ((b66g_open_source R t b).mem_nhds hb)
    let u : rf8_fibre R.C t → ℂ := fun y => (χ y : ℂ) * b66g_tau R t ρ s b y
    have hu : u ∈ b4c_SmoothFun ℂ (rf8_fibre R.C t) := by
      intro y
      by_cases hy : y ∈ tsupport χ
      · exact (Complex.ofRealCLM.contMDiff.comp hχ).contMDiffAt.mul
          (b66g_tau_smooth R t ρ hρ hs b y (hχs hy))
      · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simp only [u, show χ z = 0 from hz, Complex.ofReal_zero, zero_mul]
    have hsm := RiemannRochAna_dbar_smooth (E := ℂ) (C := rf8_fibre R.C t) ⟨u, hu⟩
    apply (hsm p).congr_of_eventuallyEq
    have hbase : ∀ᶠ y' in 𝓝 p.1, ∀ v : ℂ, b66g_gamma R t ρ s ⟨y', v⟩ =
        b4c_dbar ℂ (rf8_fibre R.C t) u ⟨y', v⟩ := by
      filter_upwards [b66g_gamma_local R t ρ hρ hs b p.1 hb, hχ1.eventually_nhds]
        with y' h1 h2 v
      rw [h1 v]
      apply RiemannRochAna_dbar_congr
      filter_upwards [h2] with z hz
      simp only [u, show χ z = 1 from hz, Complex.ofReal_one, one_mul]
    have hp := (FiberBundle.continuous_proj ℂ
      (TangentSpace 𝓘(ℂ, ℂ) : rf8_fibre R.C t → Type)).continuousAt (x := p)
    filter_upwards [hp.preimage_mem_nhds hbase] with q hq
    rcases q with ⟨q1, q2⟩
    exact hq q2
  · exact RiemannRochAna_antilinear (E := ℂ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66g_tau R t ρ s x.val) x) a v w

theorem b66g_pt_continuous (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) :
    ContinuousAt (fun w => b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) z := by
  have hc : ContinuousAt (fun w : ℂ => (R.atlas.A a).symm (t.val, w)) z :=
    ((R.atlas.A a).continuousAt_symm hz).comp (continuous_const.prodMk continuous_id).continuousAt
  exact (b6m_coordinate mr_base R.C t).symm.continuous.continuousAt.comp
    (continuous_snd.continuousAt.comp hc)

theorem b66g_coord_analytic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (H : rf8_fibre R.C t → ℂ) (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a)
    (hH : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω H (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2)) :
    AnalyticAt ℂ (fun w => H (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z := by
  set y₀ := b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2
  have hy₀v : y₀.val = (R.atlas.A a).symm (t.val, z) := b66k_inverse_slice R t a z hz
  have hy₀a : y₀.val ∈ (R.atlas.A a).source := by
    rw [hy₀v]
    exact (R.atlas.A a).map_target hz
  set e := extChartAt 𝓘(ℂ, ℂ) y₀
  set h := b66g_slice R t a ∘ e.symm
  obtain ⟨han, hder, _⟩ := b66g_slice_chart R t a y₀ y₀ (mem_extChartAt_source y₀) hy₀a
  have hz' : h (e y₀) = z := by
    change (R.atlas.A a (e.symm (e y₀)).val).2 = z
    rw [e.left_inv (mem_extChartAt_source y₀), hy₀v, (R.atlas.A a).right_inv hz]
  rw [← hz']
  refine (analyticAt_comp_iff_of_deriv_ne_zero han hder).mp ?_
  have hex : e y₀ ∈ e.target := e.map_source (mem_extChartAt_source y₀)
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y₀) := by
    refine inter_mem (extChartAt_target_mem_nhds' hex) ?_
    apply (continuousAt_extChartAt_symm'' hex).preimage_mem_nhds
    rw [e.left_inv (mem_extChartAt_source y₀)]
    exact (b66g_open_source R t a).mem_nhds hy₀a
  have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y₀) :=
    (contMDiffOn_extChartAt_symm y₀ (e y₀) hex).contMDiffAt
      (extChartAt_target_mem_nhds' hex)
  have hH' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω H (e.symm (e y₀)) := by
    rw [e.left_inv (mem_extChartAt_source y₀)]
    exact hH
  have hK : AnalyticAt ℂ (H ∘ e.symm) (e y₀) :=
    (contMDiffAt_iff_contDiffAt.mp (hH'.comp (e y₀) hsym)).analyticAt
  apply hK.congr
  filter_upwards [hU] with w hw
  simp only [Function.comp_apply]
  rw [b66g_inv_slice R t a (e.symm w) hw.2]
  exact congrArg H (b66g_fibre_mk R t (e.symm w)).symm

theorem b66g_split_of_ml (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (y₀ : rf8_fibre R.C t)
    (F P : rf8_fibre R.C t → ℂ) (N : ℕ) (c : Fin N → ℂ)
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F)
    (hP : ∀ y, y ≠ y₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y)
    (hFP : ∀ y, y ≠ y₀ → ∀ v : ℂ,
      b4c_dbar ℂ (rf8_fibre R.C t) (F + P) ⟨y, v⟩ = b66g_gamma R t ρ s ⟨y, v⟩)
    (hFnear : ∀ᶠ y in 𝓝 y₀, ∀ v : ℂ,
      b4c_dbar ℂ (rf8_fibre R.C t) F ⟨y, v⟩ = b66g_gamma R t ρ s ⟨y, v⟩)
    (hPg : P =ᶠ[𝓝 y₀] fun y => ∑ n, c n /
        RiemannRochAna_coordinate (Module.finrank_self ℂ) y₀ y ^ ((n : ℕ) + 1)) :
    (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt
      (fun w => (b66g_tau R t ρ s a - (F + P)) (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z) ∧
    (∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ y₀.val.2 →
      AnalyticAt ℂ (fun w =>
        (b66g_tau R t ρ s a - (F + P)) (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z) ∧
    ∀ a b x, (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
      s a b x = (b66g_tau R t ρ s a - (F + P)) (b66g_pt R t
          ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2) -
        (b66g_tau R t ρ s b - (F + P)) (b66g_pt R t
          ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  let H : b66k_Index R → rf8_fibre R.C t → ℂ := fun a => b66g_tau R t ρ s a - (F + P)
  have hpt : ∀ a z, z ∈ b66k_domain R t a →
      (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A a).source := by
    intro a z hz
    change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
    rw [b66k_inverse_slice R t a z hz]
    exact (R.atlas.A a).map_target hz
  have hAn : ∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ y₀.val.2 →
      AnalyticAt ℂ (fun w => H a (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z := by
    intro a z hz hne
    apply b66g_coord_analytic R t (H a) a z hz
    set y := b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2
    have hya := hpt a z hz
    have hyne : y ≠ y₀ := fun h => hne (by rw [← h]; rfl)
    apply RiemannRochAna_analyticAt_of_dbar_germ hE (H a) y
    have hopen : IsOpen ({y' : rf8_fibre R.C t | y'.val ∈ (R.atlas.A a).source} ∩ {y₀}ᶜ) :=
      (b66g_open_source R t a).inter isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds ⟨hya, hyne⟩] with y' hy'
    have hτ := b66g_tau_smooth R t ρ hρ hs a y' hy'.1
    have hFP' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (F + P) y' := (hF y').add (hP y' hy'.2)
    refine ⟨hτ.sub hFP', fun v => ?_⟩
    rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
      (hFP'.mdifferentiableAt (by simp)) v, hFP y' hy'.2 v,
      ← (b66g_gamma_local R t ρ hρ hs a y' hy'.1).self_of_nhds v, sub_self]
  refine ⟨fun a z hz => ?_, hAn, fun a b x ha hb => ?_⟩
  · by_cases hne : ((R.atlas.A a).symm (t.val, z)).2 ≠ y₀.val.2
    · exact (hAn a z hz hne).meromorphicAt
    push Not at hne
    have hy : b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2 = y₀ := by
      rw [hne]
      exact b66g_fibre_mk R t y₀
    have hya : y₀.val ∈ (R.atlas.A a).source := hy ▸ hpt a z hz
    have hG1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_tau R t ρ s a - F) y₀ := by
      apply RiemannRochAna_analyticAt_of_dbar_germ hE _ y₀
      filter_upwards [(b66g_open_source R t a).mem_nhds hya, hFnear,
        b66g_gamma_local R t ρ hρ hs a y₀ hya] with y' h1 h2 h3
      have hτ := b66g_tau_smooth R t ρ hρ hs a y' h1
      refine ⟨hτ.sub (hF y'), fun v => ?_⟩
      rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
        ((hF y').mdifferentiableAt (by simp)) v, h2 v, h3 v, sub_self]
    have hk := RiemannRochAna_coordinate_analytic hE y₀ y₀ (mem_extChartAt_source y₀)
    have hA1 : AnalyticAt ℂ (fun w => b66g_tau R t ρ s a
        (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) -
        F (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z :=
      b66g_coord_analytic R t (b66g_tau R t ρ s a - F) a z hz (by rw [hy]; exact hG1)
    have hA2 : AnalyticAt ℂ (fun w => RiemannRochAna_coordinate hE y₀
        (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z :=
      b66g_coord_analytic R t _ a z hz (by rw [hy]; exact hk)
    have hM : MeromorphicAt (fun w => (b66g_tau R t ρ s a
        (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) -
        F (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) -
        ∑ n, c n / RiemannRochAna_coordinate hE y₀
          (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) ^ ((n : ℕ) + 1)) z :=
      hA1.meromorphicAt.sub (MeromorphicAt.fun_sum (s := Finset.univ)
        fun n _ => (MeromorphicAt.const (c n) z).div (hA2.meromorphicAt.pow ((n : ℕ) + 1)))
    apply hM.congr
    have htend := (b66g_pt_continuous R t a z hz).tendsto
    rw [hy] at htend
    filter_upwards [nhdsWithin_le_nhds (htend.eventually hPg)] with w hw
    simp only [Pi.sub_apply, Pi.add_apply, hw]
    ring
  · change s a b x = H a (b66g_pt R t ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2) -
      H b (b66g_pt R t ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2)
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2]
    have := b66g_tau_sub R t ρ hρ hs a b (b66g_pt R t x) ha hb
    simp only [H, Pi.sub_apply, Pi.add_apply]
    change _ = s a b x at this
    linear_combination -this

theorem b66g_scalar_split (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) :
    ∃ (x₀ : R.C) (h : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (h a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ x₀ →
        AnalyticAt ℂ (h a) z) ∧
      ∀ a b x, (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
        s a b x = h a (R.atlas.A a (t, x)).2 - h b (R.atlas.A b (t, x)).2 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (M := rf8_fibre R.C t) isClosed_univ
    (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
    (fun c => b66g_open_source R t c)
    (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
  obtain ⟨y₀⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  obtain ⟨F, P, N, c, hF, hP, hFP, hFnear, hPg⟩ :=
    b66g_mittagLeffler (b66g_gamma R t ρ s) (b66g_gamma_mem R t ρ hρ hs) y₀
  obtain ⟨hm, han, hsp⟩ := b66g_split_of_ml R t ρ hρ hs y₀ F P N c hF hP hFP hFnear hPg
  exact ⟨y₀.val.2, fun a w =>
    (b66g_tau R t ρ s a - (F + P)) (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2), hm, han, hsp⟩

theorem b66g_form_exists (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ q : b66g_Coeff R, q ∈ b66g_forms R t 1 ∧ q ≠ 0 := by
  have h6 := b66g_primitiveForms_finrank R t
  have hne : b66g_primitiveForms R t ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h6
    norm_num at h6
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨q, (inf_le_left : b66g_primitiveForms R t ≤ b66g_forms R t 1) hq, hq0⟩

theorem b66g_vertical_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) : b66k_vertical R t a b x ≠ 0 := by
  have hch := b66g_slice_change R t a b ⟨(t, x), rfl⟩ ha hb 1
  have hnb := b66g_slice_ne R t b ⟨(t, x), rfl⟩ hb
  rw [hch] at hnb
  exact left_ne_zero_of_mul hnb

theorem b66g_form_zero_iff (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (a : b66k_Index R)
    (y : rf8_fibre R.C t) (ha : y.val ∈ (R.atlas.A a).source) :
    q a y.val.2 = 0 ↔ q y.val y.val.2 = 0 := by
  have hb : y.val ∈ (R.atlas.A y.val).source := (R.atlas.hA y.val).1
  have ha' := (b66g_mem_source R t a y).mp ha
  have hb' := (b66g_mem_source R t y.val y).mp hb
  have hlaw := (b66g_forms_spec R t m hq).2.1 a y.val y.val.2 ha' hb'
  have hV := pow_ne_zero m (b66g_vertical_ne R t a y.val y.val.2 ha' hb')
  rw [hlaw]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hV, fun h => by rw [h, mul_zero]⟩

theorem b66g_form_dichotomy (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (y : rf8_fibre R.C t) :
    (∀ᶠ y' in 𝓝 y, q y'.val y'.val.2 = 0) ∨
      ∃ W ∈ 𝓝 y, ∀ y' ∈ W, y' ≠ y → q y'.val y'.val.2 ≠ 0 := by
  set a := y.val
  have ha : y.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  have hf : AnalyticAt ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66g_slice R t a y) :=
    (b66g_forms_spec R t m hq).1 a _ (b66g_slice_domain R t a y ha)
  have hs := (b66g_slice_contMDiffAt R t a y ha).continuousAt.tendsto
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · left
    filter_upwards [hs.eventually h0, (b66g_open_source R t a).mem_nhds ha] with y' h1 h2
    rw [← b66g_form_zero_iff R t hq a y' h2]
    simpa only [b66g_inv_slice R t a y' h2] using h1
  · right
    refine ⟨b66g_slice R t a ⁻¹' {z | z ≠ b66g_slice R t a y →
        q a ((R.atlas.A a).symm (t.val, z)).2 ≠ 0} ∩
        {y' | y'.val ∈ (R.atlas.A a).source}, inter_mem
        (hs.eventually (eventually_nhdsWithin_iff.mp h1))
        ((b66g_open_source R t a).mem_nhds ha), fun y' hy' hne => ?_⟩
    have hsl : b66g_slice R t a y' ≠ b66g_slice R t a y := by
      intro heq
      apply hne
      apply Subtype.ext
      apply (R.atlas.A a).injOn hy'.2 ha
      rw [b66g_slice_value R t a y' hy'.2, b66g_slice_value R t a y ha]
      exact congrArg (fun z => (t.val, z)) heq
    have h := hy'.1 hsl
    rw [b66g_inv_slice R t a y' hy'.2] at h
    exact fun hz => h ((b66g_form_zero_iff R t hq a y' hy'.2).mpr hz)

theorem b66g_form_isolated (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0) (y : rf8_fibre R.C t) :
    ∃ W ∈ 𝓝 y, ∀ y' ∈ W, y' ≠ y → q y'.val y'.val.2 ≠ 0 := by
  let A : Set (rf8_fibre R.C t) := {y | ∀ᶠ y' in 𝓝 y, q y'.val y'.val.2 = 0}
  have hopen : IsOpen A := isOpen_iff_mem_nhds.mpr fun y hy => hy.eventually_nhds
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    rcases b66g_form_dichotomy R t hq y with h | ⟨W, hW, hiso⟩
    · exact absurd h hy
    filter_upwards [hW] with y' hy' hA'
    by_cases he : y' = y
    · exact hy (he ▸ hA')
    · exact hiso y' hy' he hA'.self_of_nhds
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with hA | hA
  · rcases b66g_form_dichotomy R t hq y with h | h
    · have : y ∈ A := h
      rw [hA] at this
      exact absurd this (notMem_empty y)
    · exact h
  · exfalso
    apply hq0
    funext a x
    by_cases hax : (t, x) ∈ (R.atlas.A a).source
    · have hy : b66g_pt R t x ∈ A := hA ▸ mem_univ _
      exact (b66g_form_zero_iff R t hq a (b66g_pt R t x) hax).mpr hy.self_of_nhds
    · exact (b66g_forms_spec R t m hq).2.2 a x hax

theorem b66g_form_zeros_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0) :
    ∃ T : Finset R.C, ∀ x, q (t, x) x = 0 → x ∈ T := by
  choose W hW hiso using b66g_form_isolated R t hq hq0
  obtain ⟨T, hT⟩ := isCompact_univ.elim_nhds_subcover W (fun y _ => hW y)
  refine ⟨T.image fun y => y.val.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hT.2 (mem_univ (b66g_pt R t x)))
  by_cases he : b66g_pt R t x = y
  · exact Finset.mem_image.mpr ⟨y, hy, by rw [← he]; rfl⟩
  · exact absurd hx (hiso y _ hxy he)

theorem b66g_meromorphic_splitting_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R)
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)) :
    ∃ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
      ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x := by
  obtain ⟨q, hq, hq0⟩ := b66g_form_exists R t
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 1 hq
  obtain ⟨T, hT⟩ := b66g_form_zeros_finite R t hq hq0
  obtain ⟨x₀, h, hmero, hreg, hsplit⟩ := b66g_scalar_split R t (b66g_contract_mem R t hq hu)
  have hnz : ∀ a x, x ∉ T → (t, x) ∈ (R.atlas.A a).source → q a x ≠ 0 := by
    intro a x hx hax hz
    exact hx (hT x ((b66g_form_zero_iff R t hq a (b66g_pt R t x) hax).mp hz))
  refine ⟨insert x₀ T, fun a z => h a z / q a ((R.atlas.A a).symm (t.val, z)).2,
    fun a z hz => (hmero a z hz).div (hqa a z hz).meromorphicAt,
    fun a z hz hS => ?_, fun a b x hS ha hb => ?_⟩
  · rw [Finset.mem_insert, not_or] at hS
    have hax : (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source := by
      rw [b66k_inverse_slice R t a z hz]
      exact (R.atlas.A a).map_target hz
    exact (hreg a z hz hS.1).div (hqa a z hz) (hnz a _ hS.2 hax)
  · rw [Finset.mem_insert, not_or] at hS
    have hs := hsplit a b x ha hb
    simp only [b66g_contract] at hs
    simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A b).source from ⟨ha, hb⟩)]
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
      hql a b x ha hb, pow_one]
    have hqb := hnz b x hS.2 hb
    have hV := b66g_vertical_ne R t a b x ha hb
    field_simp
    linear_combination hs

end B66gSmoothing

section B66gCoefficientForms

/-- The fibre one-form with given retained-chart coefficients, read in the own chart. -/
def b66g_cform (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (C : b66k_Index R → ℂ → ℂ) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ := fun q =>
  C q.proj.val (R.atlas.A q.proj.val q.proj.val).2 * b66g_sliceD R t q.proj.val q.proj q.2

theorem b66g_cform_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (p : rf8_fibre R.C t) (hp : p.val.2 ∉ S) (a : b66k_Index R)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66g_cform R t C ⟨p, w⟩ = C a (R.atlas.A a p.val).2 * b66g_sliceD R t a p w := by
  have hc : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hl := hlaw a p.val p.val.2 hp ((b66g_mem_source R t a p).mp ha)
    ((b66g_mem_source R t p.val p).mp hc)
  rw [← b66g_fibre_val R t p] at hl
  change C p.val (R.atlas.A p.val p.val).2 * b66g_sliceD R t p.val p w = _
  rw [b66g_slice_change R t a p.val p ha hc w, hl]
  ring

theorem b66g_cform_lin (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (C : b66k_Index R → ℂ → ℂ) (x : rf8_fibre R.C t) (c u w : ℂ) :
    b66g_cform R t C ⟨x, c * u + w⟩ =
      c * b66g_cform R t C ⟨x, u⟩ + b66g_cform R t C ⟨x, w⟩ := by
  unfold b66g_cform
  simp only
  rw [b66g_clm_apply (b66g_sliceD R t x.val x) (c * u + w),
    b66g_clm_apply (b66g_sliceD R t x.val x) u, b66g_clm_apply (b66g_sliceD R t x.val x) w]
  ring

theorem b66g_cform_loc (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (x₀ : rf8_fibre R.C t) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_cform R t C) x₀ =ᶠ[𝓝[≠] 0]
      fun τ => C x₀.val
        ((b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) *
        deriv (fun σ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + σ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) τ := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set a₀ := x₀.val
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t a₀ ∘ e.symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have hx₀e : x₀ ∈ e.source := mem_extChartAt_source x₀
  have hex : e x₀ ∈ e.target := e.map_source hx₀e
  have ha₀ : x₀.val ∈ (R.atlas.A a₀).source := (R.atlas.hA a₀).1
  have hopen := b66g_open_source R t a₀
  set B : Set (rf8_fibre R.C t) :=
    (fun x : R.C => (⟨(t, x), rfl⟩ : rf8_fibre R.C t)) '' (↑S : Set R.C) \ {x₀}
  have hBf : B.Finite := (S.finite_toSet.image _).sdiff
  have hBc : Bᶜ ∈ 𝓝 x₀ := by
    refine (hBf.isClosed.isOpen_compl).mem_nhds ?_
    intro hx
    exact hx.2 rfl
  have hsc : Tendsto (fun τ : ℂ => e x₀ + τ * c₀) (𝓝 0) (𝓝 (e x₀)) := by
    have : Continuous (fun τ : ℂ => e x₀ + τ * c₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e x₀ + τ * c₀)) (𝓝 0) (𝓝 x₀) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  have hev1 : ∀ᶠ τ in 𝓝 (0 : ℂ), e x₀ + τ * c₀ ∈ e.target :=
    hsc.eventually (extChartAt_target_mem_nhds' hex)
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈
      {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a₀).source} :=
    hsymc.eventually (hopen.mem_nhds ha₀)
  have hev3 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * c₀) ∈ Bᶜ :=
    hsymc.eventually hBc
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with τ h1 h2 h3 h4
  set y := e.symm (e x₀ + τ * c₀)
  have hy : y ∈ e.source := e.map_target h1
  have hyx : y ≠ x₀ := by
    intro hyx
    have := e.right_inv h1
    rw [show e.symm (e x₀ + τ * c₀) = y from rfl, hyx] at this
    have h5 : τ * c₀ = 0 := by linear_combination -this
    exact h4 (mul_eq_zero.mp h5 |>.resolve_right hc₀)
  have hyS : y.val.2 ∉ S := fun hS => h3 ⟨⟨y.val.2, hS, b66g_fibre_mk R t y⟩, hyx⟩
  obtain ⟨hyan, _, hD⟩ := b66g_slice_chart R t a₀ x₀ y hy h2
  have hey : e y = e x₀ + τ * c₀ := e.right_inv h1
  have hdΦ : deriv (fun σ => hh (e x₀ + σ * c₀)) τ = deriv hh (e x₀ + τ * c₀) * c₀ := by
    rw [hey] at hyan
    have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ τ := by
      simpa using ((hasDerivAt_id τ).mul_const c₀).const_add (e x₀)
    exact (hyan.differentiableAt.hasDerivAt.comp τ hs).deriv
  change b4cov_coef (b66g_cform R t C) x₀ c₀
    (e x₀ + b4cov_lineEquiv (Module.finrank_self ℂ) τ) = _
  rw [b66g_lineEquiv_apply τ]
  unfold b4cov_coef
  change b66g_cform R t C ⟨y, b4cov_vec x₀ y c₀⟩ = _
  refine (b66g_cform_apply R t S C hlaw y hyS a₀ h2 (b4cov_vec x₀ y c₀)).trans ?_
  have hk : b66g_sliceD R t a₀ y (b4cov_vec x₀ y c₀) = deriv hh (e x₀ + τ * c₀) * c₀ := by
    refine (hD _).trans ?_
    rw [b66g_chartD_vec R t x₀ y hy, hey]
  rw [hk, hdΦ]
  rfl

theorem b66g_own_domain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x : R.C) :
    (R.atlas.A (t, x) (t, x)).2 ∈ b66k_domain R t (t, x) := by
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
  rw [← (b66g_chart_slice R t (t, x) x hxa).1]
  exact (R.atlas.A (t, x)).map_source hxa

theorem b66g_cform_res (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (x₀ : rf8_fibre R.C t) :
    MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_cform R t C) x₀) 0 ∧
    TauCeti.Contour.residue
      (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_cform R t C) x₀) 0 =
      TauCeti.Contour.residue (C x₀.val) (R.atlas.A x₀.val x₀.val).2 := by
  have hloc := b66g_cform_loc R t S C hlaw x₀
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t x₀.val ∘ e.symm
  set Φ : ℂ → ℂ := fun σ => hh (e x₀ + σ * c₀)
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have ha₀ : x₀.val ∈ (R.atlas.A x₀.val).source := (R.atlas.hA x₀.val).1
  obtain ⟨hhan, hhd, _⟩ := b66g_slice_chart R t x₀.val x₀ x₀ (mem_extChartAt_source x₀) ha₀
  have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c₀).const_add (e x₀)
  have hsa : AnalyticAt ℂ (fun σ : ℂ => e x₀ + σ * c₀) 0 := by fun_prop
  have hh0 : (fun σ : ℂ => e x₀ + σ * c₀) 0 = e x₀ := by simp
  have hhan' : AnalyticAt ℂ hh ((fun σ : ℂ => e x₀ + σ * c₀) 0) := by
    rw [hh0]
    exact hhan
  have hΦ : AnalyticAt ℂ Φ 0 := AnalyticAt.comp (f := fun σ : ℂ => e x₀ + σ * c₀) hhan' hsa
  have hΦd : deriv Φ 0 ≠ 0 := by
    change deriv (hh ∘ fun σ : ℂ => e x₀ + σ * c₀) 0 ≠ 0
    rw [(hhan'.differentiableAt.hasDerivAt.comp 0 hs).deriv]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero hhd hc₀
  have hΦ0 : Φ 0 = (R.atlas.A x₀.val x₀.val).2 := by
    simp only [Φ, hh, zero_mul, add_zero, Function.comp_apply,
      e.left_inv (mem_extChartAt_source x₀)]
    rfl
  have hm := hmero x₀.val _ (b66g_slice_domain R t x₀.val x₀ ha₀)
  change MeromorphicAt (C x₀.val) (R.atlas.A x₀.val x₀.val).2 at hm
  rw [← hΦ0] at hm
  have hcm : MeromorphicAt (fun τ => C x₀.val (Φ τ) * deriv Φ τ) 0 :=
    (hm.comp_analyticAt hΦ).mul hΦ.deriv.meromorphicAt
  refine ⟨hcm.congr hloc.symm, ?_⟩
  rw [TauCeti.Contour.residue_congr_nhdsNE hloc, ← hΦ0]
  exact b66g_residue_comp hΦ hΦd hm

theorem b66g_cform_residue_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2) :
    ∑ x ∈ S, TauCeti.Contour.residue (C (t, x)) (R.atlas.A (t, x) (t, x)).2 = 0 := by
  set θ := b66g_cform R t C
  have hres := b66g_cform_res R t S C hmero hlaw
  have hlin : HurwitzPrymRR_IsLinear θ := fun x c u w => b66g_cform_lin R t C x c u w
  let w : b4c_MeroForm ℂ (rf8_fibre R.C t) (Module.finrank_self ℂ) :=
    ⟨θ, hlin, fun x => (hres x).1⟩
  have hsum := b4c_residue_sum (Module.finrank_self ℂ) w
  have hsupp : Function.support (fun x => b4c_res (hE := Module.finrank_self ℂ)
      (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) x) ⊆ ↑(S.map (b66g_pt R t)) := by
    intro p hp
    by_contra hnot
    apply hp
    have hpS : p.val.2 ∉ S := by
      intro hm
      apply hnot
      refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨p.val.2, hm, ?_⟩)
      exact b66g_fibre_mk R t p
    change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 0
    rw [(hres p).2]
    apply TauCeti.Contour.residue_eq_zero_of_analyticAt
    have ha : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
    apply hreg p.val _ (b66g_slice_domain R t p.val p ha)
    rw [b66g_inv_slice R t p.val p ha]
    exact hpS
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map] at hsum
  refine Eq.trans ?_ hsum
  refine Finset.sum_congr rfl fun x _ => ?_
  exact ((hres (b66g_pt R t x)).2).symm

theorem b66g_residueSum_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    b66g_residueSum R t S v q - b66g_residueSum R t S v' q =
      ∑ x ∈ S, TauCeti.Contour.residue
        (fun z => (v (t, x) z - v' (t, x) z) * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
        (R.atlas.A (t, x) (t, x)).2 := by
  obtain ⟨hqa, _, _⟩ := b66g_forms_spec R t m hq
  unfold b66g_residueSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdom := b66g_own_domain R t x
  have hq' := (hqa (t, x) _ hdom).meromorphicAt
  have h1 : MeromorphicAt (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul hq'
  have h2 : MeromorphicAt (fun z => v' (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero' _ _ hdom).mul hq'
  rw [← TauCeti.Contour.residue_sub h1 h2]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring

theorem b66g_split_unique (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (S S' : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    (hreg' : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S' → AnalyticAt ℂ (v' a) z)
    (hv' : ∀ a b x, x ∉ S' → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v' a b x)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    b66g_residueSum R t S v q = b66g_residueSum R t S' v' q := by
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 2 hq
  set T := S ∪ S'
  rw [← b66g_residueSum_extend R t S T v hreg hq Finset.subset_union_left,
    ← b66g_residueSum_extend R t S' T v' hreg' hq Finset.subset_union_right,
    ← sub_eq_zero, b66g_residueSum_sub R t T v v' hmero hmero' hq]
  apply b66g_cform_residue_sum R t T
    (fun a z => (v a z - v' a z) * q a ((R.atlas.A a).symm (t.val, z)).2)
  · intro a z hz
    exact ((hmero a z hz).sub (hmero' a z hz)).mul (hqa a z hz).meromorphicAt
  · intro a z hz hT
    have h1 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S := fun h => hT (Finset.mem_union_left _ h)
    have h2 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S' := fun h => hT (Finset.mem_union_right _ h)
    exact ((hreg a z hz h1).sub (hreg' a z hz h2)).mul (hqa a z hz)
  · intro a b x hx ha hb
    have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
    have hxS' : x ∉ S' := fun h => hx (Finset.mem_union_right _ h)
    have e1 := hv a b x hxS ha hb
    have e2 := hv' a b x hxS' ha hb
    simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A b).source from ⟨ha, hb⟩)] at e1 e2
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2, hql a b x ha hb]
    linear_combination (b66k_vertical R t a b x * q b x) * (e2 - e1)

theorem b66g_residueSum_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v v' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v' a) z)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) :
    b66g_residueSum R t S (v + v') q =
      b66g_residueSum R t S v q + b66g_residueSum R t S v' q := by
  obtain ⟨hqa, _, _⟩ := b66g_forms_spec R t m hq
  unfold b66g_residueSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdom := b66g_own_domain R t x
  have hq' := (hqa (t, x) _ hdom).meromorphicAt
  have h1 : MeromorphicAt (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero _ _ hdom).mul hq'
  have h2 : MeromorphicAt (fun z => v' (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2 := (hmero' _ _ hdom).mul hq'
  rw [← TauCeti.Contour.residue_add h1 h2]
  congr 1
  funext z
  simp only [Pi.add_apply]
  ring

theorem b66g_residueSum_vsmul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (c : ℂ) (q : b66g_Coeff R) :
    b66g_residueSum R t S (c • v) q = c * b66g_residueSum R t S v q := by
  unfold b66g_residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TauCeti.Contour.residue_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem b66g_residueSum_qadd (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    {q r : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) (hr : r ∈ b66g_forms R t 2) :
    b66g_residueSum R t S v (q + r) =
      b66g_residueSum R t S v q + b66g_residueSum R t S v r := by
  have h := b66g_residueSum_sum R t S v hmero (Finset.univ : Finset (Fin 2)) ![q, r]
    (fun i => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

theorem b66g_boundary_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v w : b66k_Index R → ℂ → ℂ) :
    b66k_boundary R t (v + w) = b66k_boundary R t v + b66k_boundary R t w := by
  funext a b x
  simp only [b66k_boundary, Pi.add_apply]
  split_ifs <;> ring

theorem b66g_boundary_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (c : ℂ) (v : b66k_Index R → ℂ → ℂ) :
    b66k_boundary R t (c • v) = c • b66k_boundary R t v := by
  funext a b x
  simp only [b66k_boundary, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Residue pairing of a holomorphic tangent cocycle, through a chosen splitting. -/
def b66g_resPair (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)))
    (q : b66g_Coeff R) : ℂ :=
  b66g_residueSum R t (Classical.choose (b66g_meromorphic_splitting_aux R t u.val u.property))
    (Classical.choose (Classical.choose_spec
      (b66g_meromorphic_splitting_aux R t u.val u.property))) q

theorem b66g_resPair_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)))
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u.val a b x = b66k_boundary R t v a b x)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    b66g_resPair R t u q = b66g_residueSum R t S v q := by
  have h := Classical.choose_spec (Classical.choose_spec
    (b66g_meromorphic_splitting_aux R t u.val u.property))
  exact b66g_split_unique R t u.val _ S _ v h.1 h.2.1 h.2.2 hmero hreg hv hq

theorem b66g_resPair_split (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))) :
    ∃ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
      (∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u.val a b x = b66k_boundary R t v a b x) :=
  b66g_meromorphic_splitting_aux R t u.val u.property

theorem b66g_resPair_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u w : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)))
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    b66g_resPair R t (u + w) q = b66g_resPair R t u q + b66g_resPair R t w q := by
  obtain ⟨S, v, h1, h2, h3⟩ := b66g_resPair_split R t u
  obtain ⟨S', v', h1', h2', h3'⟩ := b66g_resPair_split R t w
  rw [b66g_resPair_eq R t u S v h1 h2 h3 hq, b66g_resPair_eq R t w S' v' h1' h2' h3' hq,
    ← b66g_residueSum_extend R t S (S ∪ S') v h2 hq Finset.subset_union_left,
    ← b66g_residueSum_extend R t S' (S ∪ S') v' h2' hq Finset.subset_union_right,
    ← b66g_residueSum_add R t _ v v' h1 h1' hq]
  apply b66g_resPair_eq R t (u + w) (S ∪ S') (v + v')
    (fun a z hz => (h1 a z hz).add (h1' a z hz))
    (fun a z hz hS => (h2 a z hz fun h => hS (Finset.mem_union_left _ h)).add
      (h2' a z hz fun h => hS (Finset.mem_union_right _ h)))
    (fun a b x hx ha hb => ?_) hq
  rw [b66g_boundary_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
    ← h3 a b x (fun h => hx (Finset.mem_union_left _ h)) ha hb,
    ← h3' a b x (fun h => hx (Finset.mem_union_right _ h)) ha hb]
  rfl

theorem b66g_resPair_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (c : ℂ)
    (u : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)))
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    b66g_resPair R t (c • u) q = c * b66g_resPair R t u q := by
  obtain ⟨S, v, h1, h2, h3⟩ := b66g_resPair_split R t u
  rw [b66g_resPair_eq R t u S v h1 h2 h3 hq, ← b66g_residueSum_vsmul]
  apply b66g_resPair_eq R t (c • u) S (c • v)
    (fun a z hz => (h1 a z hz).const_smul c)
    (fun a z hz hS => (h2 a z hz hS).const_smul (c := c))
    (fun a b x hx ha hb => ?_) hq
  rw [b66g_boundary_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    ← h3 a b x hx ha hb]
  rfl

theorem b66g_resPair_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : ↥(b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)))
    (hb : u.val ∈ b66k_boundaries R t) {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    b66g_resPair R t u q = 0 := by
  obtain ⟨v, hv, hu⟩ := b66k_boundary_representation R t u.val hb
  rw [b66g_resPair_eq R t u ∅ v (fun a z hz => (hv a z hz).meromorphicAt)
    (fun a z hz _ => hv a z hz) (fun a b x _ _ _ => by rw [hu]) hq]
  simp [b66g_residueSum]

theorem b66g_serre_functional (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ E : b66k_cechH1 R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      E c q = b66g_residueSum R t S v q.val := by
  let Z := b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)
  let Φ : Z →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2) :=
    LinearMap.mk₂ ℂ (fun (u : Z) (q : b66g_forms R t 2) => b66g_resPair R t u q.val)
      (fun u w q => b66g_resPair_add R t u w q.property)
      (fun c u q => b66g_resPair_smul R t c u q.property)
      (fun u q r => by
        obtain ⟨S, v, h1, h2, h3⟩ := b66g_resPair_split R t u
        change b66g_resPair R t u (q.val + r.val) = _
        rw [b66g_resPair_eq R t u S v h1 h2 h3 (add_mem q.property r.property),
          b66g_resPair_eq R t u S v h1 h2 h3 q.property,
          b66g_resPair_eq R t u S v h1 h2 h3 r.property]
        exact b66g_residueSum_qadd R t S v h1 q.property r.property)
      (fun c u q => by
        obtain ⟨S, v, h1, h2, h3⟩ := b66g_resPair_split R t u
        change b66g_resPair R t u (c • q.val) = c * _
        rw [b66g_resPair_eq R t u S v h1 h2 h3 (Submodule.smul_mem _ c q.property),
          b66g_resPair_eq R t u S v h1 h2 h3 q.property]
        exact b66g_residueSum_smul R t S v c q.val)
  let f : Z →ₗ[ℂ] b66k_Quotient R t := (b66k_boundaries R t).mkQ ∘ₗ Z.subtype
  have hker : LinearMap.ker f ≤ LinearMap.ker Φ := by
    intro u hu
    have hb : u.val ∈ b66k_boundaries R t :=
      (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hu)
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro q
    exact b66g_resPair_boundary R t u hb q.property
  have hrange : LinearMap.range f = b66k_cechH1 R t := by
    simp only [f, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  refine ⟨(LinearMap.ker f).liftQ Φ hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap, ?_⟩
  intro u hu c hc S v hmero hreg hv q
  have he : f.quotKerEquivRange.symm (LinearEquiv.ofEq _ _ hrange.symm c) =
      (LinearMap.ker f).mkQ ⟨u, hu⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply, Submodule.mkQ_apply,
      LinearMap.quotKerEquivRange_apply_mk]
    exact hc
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
    Submodule.liftQ_apply, Submodule.mkQ_apply]
  exact b66g_resPair_eq R t ⟨u, hu⟩ S v hmero hreg hv q.property

end B66gCoefficientForms
section B66gOrders

/-- Coefficient of a retained differential in the chart coordinate. -/
def b66g_coef (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q : b66g_Coeff R)
    (a : b66k_Index R) : ℂ → ℂ := fun z => q a ((R.atlas.A a).symm (t.val, z)).2

theorem b66g_chartPhi (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x₀ : rf8_fibre R.C t) :
    AnalyticAt ℂ (fun τ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 ∧
    deriv (fun τ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 ≠ 0 ∧
    (fun τ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 =
      (R.atlas.A x₀.val x₀.val).2 := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t x₀.val ∘ e.symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have ha₀ : x₀.val ∈ (R.atlas.A x₀.val).source := (R.atlas.hA x₀.val).1
  obtain ⟨hhan, hhd, _⟩ := b66g_slice_chart R t x₀.val x₀ x₀ (mem_extChartAt_source x₀) ha₀
  have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * c₀) c₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c₀).const_add (e x₀)
  have hsa : AnalyticAt ℂ (fun σ : ℂ => e x₀ + σ * c₀) 0 := by fun_prop
  have hh0 : (fun σ : ℂ => e x₀ + σ * c₀) 0 = e x₀ := by simp
  have hhan' : AnalyticAt ℂ hh ((fun σ : ℂ => e x₀ + σ * c₀) 0) := by
    rw [hh0]
    exact hhan
  refine ⟨AnalyticAt.comp (f := fun σ : ℂ => e x₀ + σ * c₀) hhan' hsa, ?_, ?_⟩
  · change deriv (hh ∘ fun σ : ℂ => e x₀ + σ * c₀) 0 ≠ 0
    rw [(hhan'.differentiableAt.hasDerivAt.comp 0 hs).deriv]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero hhd hc₀
  · simp only [hh, zero_mul, add_zero, Function.comp_apply,
      e.left_inv (mem_extChartAt_source x₀)]
    rfl

theorem b66g_cform_order (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2)
    (x₀ : rf8_fibre R.C t) :
    meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_cform R t C) x₀) 0 =
      meromorphicOrderAt (C x₀.val) (R.atlas.A x₀.val x₀.val).2 := by
  obtain ⟨hΦ, hΦd, hΦ0⟩ := b66g_chartPhi R t x₀
  rw [meromorphicOrderAt_congr (b66g_cform_loc R t S C hlaw x₀)]
  set Φ := fun τ => (b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)
  have he : (fun τ => C x₀.val (Φ τ) * deriv Φ τ) = deriv Φ * (C x₀.val ∘ Φ) := by
    funext τ
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  rw [he, meromorphicOrderAt_mul_of_ne_zero hΦ.deriv hΦd,
    meromorphicOrderAt_comp_of_deriv_ne_zero hΦ hΦd, hΦ0]

theorem b66g_deg_eq_sum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hfin : (Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w)).Finite)
    (F : Finset (rf8_fibre R.C t))
    (hF : Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w) ⊆ F) :
    b4c_deg (b4c_divForm (hE := Module.finrank_self ℂ) w) =
      ∑ x ∈ F, b4c_ordForm (hE := Module.finrank_self ℂ) w x := by
  unfold b4c_divForm b4c_deg
  simp only [hfin, ↓reduceDIte]
  rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  apply Finset.sum_subset
  · intro x hx
    exact hF ((Set.Finite.mem_toFinset hfin).mp hx)
  · intro x _ hx
    by_contra h
    exact hx ((Set.Finite.mem_toFinset hfin).mpr h)

theorem b66g_coef_analytic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (x : R.C) :
    AnalyticAt ℂ (b66g_coef R t q (t, x)) (R.atlas.A (t, x) (t, x)).2 :=
  (b66g_forms_spec R t m hq).1 _ _ (b66g_own_domain R t x)

theorem b66g_coef_order_ne_top (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0) (x : R.C) :
    meromorphicOrderAt (b66g_coef R t q (t, x)) (R.atlas.A (t, x) (t, x)).2 ≠ ⊤ := by
  set a : b66k_Index R := (t, x)
  set z₀ := (R.atlas.A a (t, x)).2
  have hz₀ : z₀ ∈ b66k_domain R t a := b66g_own_domain R t x
  have hxa : (t, x) ∈ (R.atlas.A a).source := (R.atlas.hA _).1
  obtain ⟨W, hW, hiso⟩ := b66g_form_isolated R t hq hq0 (b66g_pt R t x)
  have hpt0 : b66g_pt R t ((R.atlas.A a).symm (t.val, z₀)).2 = b66g_pt R t x := by
    rw [(b66g_chart_slice R t a x hxa).2]
  have htend := (b66g_pt_continuous R t a z₀ hz₀).tendsto
  rw [hpt0] at htend
  have hopen : IsOpen (b66k_domain R t a) :=
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, b66g_coef R t q a z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (htend.eventually hW),
      nhdsWithin_le_nhds (hopen.mem_nhds hz₀), self_mem_nhdsWithin] with z h1 h2 h3
    have hsrc : (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A a).source := by
      change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
      rw [b66k_inverse_slice R t a z h2]
      exact (R.atlas.A a).map_target h2
    have hneq : b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2 ≠ b66g_pt R t x := by
      intro heq
      apply h3
      have hx : ((R.atlas.A a).symm (t.val, z)).2 = x := (b66g_pt R t).injective heq
      have := congrArg (fun y => (R.atlas.A a y).2) (b66k_inverse_slice R t a z h2)
      simp only [(R.atlas.A a).right_inv h2] at this
      rw [hx] at this
      exact this.symm
    have h4 := hiso _ h1 hneq
    intro hz
    apply h4
    exact (b66g_form_zero_iff R t hq a _ hsrc).mp hz
  intro htop
  have h0 := meromorphicOrderAt_eq_top_iff.mp htop
  obtain ⟨z, hz1, hz2⟩ := (h0.and hne).exists
  exact hz2 hz1

theorem b66g_cform_mero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2) :
    b4c_IsMeroForm (Module.finrank_self ℂ) (b66g_cform R t C) :=
  ⟨fun x c u w => b66g_cform_lin R t C x c u w, fun x => (b66g_cform_res R t S C hmero hlaw x).1⟩

/-- Order of a retained coefficient at the own chart of a fibre point. -/
def b66g_ord (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q : b66g_Coeff R)
    (y : rf8_fibre R.C t) : ℤ :=
  (meromorphicOrderAt (b66g_coef R t q y.val) (R.atlas.A y.val y.val).2).untop₀

theorem b66g_coef_order_ne_top' (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0)
    (y : rf8_fibre R.C t) :
    meromorphicOrderAt (b66g_coef R t q y.val) (R.atlas.A y.val y.val).2 ≠ ⊤ := by
  have h := b66g_coef_order_ne_top R t hq hq0 y.val.2
  rwa [← b66g_fibre_val R t y] at h

theorem b66g_coef_analytic' (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (y : rf8_fibre R.C t) :
    AnalyticAt ℂ (b66g_coef R t q y.val) (R.atlas.A y.val y.val).2 := by
  have h := b66g_coef_analytic R t hq y.val.2
  rwa [← b66g_fibre_val R t y] at h

theorem b66g_ord_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0)
    (y : rf8_fibre R.C t) :
    meromorphicOrderAt (b66g_coef R t q y.val) (R.atlas.A y.val y.val).2 =
      (b66g_ord R t q y : WithTop ℤ) :=
  (WithTop.coe_untop₀_of_ne_top (b66g_coef_order_ne_top' R t hq hq0 y)).symm

theorem b66g_ord_nonneg (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {m : ℕ} {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq0 : q ≠ 0)
    (y : rf8_fibre R.C t) : 0 ≤ b66g_ord R t q y := by
  have h := (b66g_coef_analytic' R t hq y).meromorphicOrderAt_nonneg
  rw [b66g_ord_eq R t hq hq0 y] at h
  exact_mod_cast h

theorem b66g_order_bound (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) (hq0 : q ≠ 0) (y₁ : rf8_fibre R.C t) :
    b66g_ord R t q y₁ ≤ 4 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 4 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨q₀, hq₀, hq₀0⟩ := b66g_form_exists R t
  obtain ⟨hqa₀, hql₀, _⟩ := b66g_forms_spec R t 1 hq₀
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 2 hq
  obtain ⟨T, hT⟩ := b66g_form_zeros_finite R t hq₀ hq₀0
  have hnz : ∀ a x, x ∉ T → (t, x) ∈ (R.atlas.A a).source → q₀ a x ≠ 0 := by
    intro a x hx hax hz
    exact hx (hT x ((b66g_form_zero_iff R t hq₀ a (b66g_pt R t x) hax).mp hz))
  set C : b66k_Index R → ℂ → ℂ := fun a z => b66g_coef R t q a z / b66g_coef R t q₀ a z
  have hlawC : ∀ a b x, x ∉ T → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x * C b (R.atlas.A b (t, x)).2 := by
    intro a b x hx ha hb
    simp only [C, b66g_coef]
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
      hql a b x ha hb, hql₀ a b x ha hb, pow_one]
    have h1 := hnz b x hx hb
    have h2 := b66g_vertical_ne R t a b x ha hb
    field_simp
  have hlaw₀ : ∀ a b x, x ∉ (∅ : Finset R.C) → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66g_coef R t q₀ a (R.atlas.A a (t, x)).2 =
        b66k_vertical R t a b x * b66g_coef R t q₀ b (R.atlas.A b (t, x)).2 := by
    intro a b x _ ha hb
    simp only [b66g_coef]
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
      hql₀ a b x ha hb, pow_one]
  have hmeroC : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z := fun a z hz =>
    (hqa a z hz).meromorphicAt.div (hqa₀ a z hz).meromorphicAt
  have hmero₀ : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (b66g_coef R t q₀ a) z :=
    fun a z hz => (hqa₀ a z hz).meromorphicAt
  let wC : b4c_MeroForm ℂ (rf8_fibre R.C t) hE :=
    ⟨b66g_cform R t C, b66g_cform_mero R t T C hmeroC hlawC⟩
  let w₀ : b4c_MeroForm ℂ (rf8_fibre R.C t) hE :=
    ⟨b66g_cform R t (b66g_coef R t q₀), b66g_cform_mero R t ∅ _ hmero₀ hlaw₀⟩
  have hordC : ∀ y, b4c_ordForm (hE := hE) (wC : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) y =
      b66g_ord R t q y - b66g_ord R t q₀ y := by
    intro y
    change (meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_cform R t C) y) 0).untop₀ = _
    rw [b66g_cform_order R t T C hlawC y]
    simp only [C]
    rw [fun_meromorphicOrderAt_div (b66g_coef_analytic' R t hq y).meromorphicAt
      (b66g_coef_analytic' R t hq₀ y).meromorphicAt,
      b66g_ord_eq R t hq hq0 y, b66g_ord_eq R t hq₀ hq₀0 y]
    exact WithTop.untop₀_coe (b66g_ord R t q y - b66g_ord R t q₀ y)
  have hord₀ : ∀ y, b4c_ordForm (hE := hE) (w₀ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) y =
      b66g_ord R t q₀ y := by
    intro y
    change (meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_cform R t (b66g_coef R t q₀)) y) 0).untop₀ = _
    rw [b66g_cform_order R t ∅ _ hlaw₀ y]
    rfl
  have hfin : ∀ (w : b4c_MeroForm ℂ (rf8_fibre R.C t) hE) (y : rf8_fibre R.C t),
      meromorphicOrderAt (HurwitzPrymRR_loc hE w y) 0 ≠ ⊤ →
      (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) ≠ 0 := by
    intro w y hy h
    apply hy
    rw [h]
    exact meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun _ => rfl)
  have hgC : meromorphicOrderAt (HurwitzPrymRR_loc hE wC y₁) 0 ≠ ⊤ := by
    change meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_cform R t C) y₁) 0 ≠ ⊤
    rw [b66g_cform_order R t T C hlawC y₁]
    simp only [C]
    rw [fun_meromorphicOrderAt_div (b66g_coef_analytic' R t hq y₁).meromorphicAt
      (b66g_coef_analytic' R t hq₀ y₁).meromorphicAt,
      b66g_ord_eq R t hq hq0 y₁, b66g_ord_eq R t hq₀ hq₀0 y₁]
    exact WithTop.coe_ne_top (a := b66g_ord R t q y₁ - b66g_ord R t q₀ y₁)
  have hg₀ : meromorphicOrderAt (HurwitzPrymRR_loc hE w₀ y₁) 0 ≠ ⊤ := by
    change meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_cform R t (b66g_coef R t q₀)) y₁) 0 ≠ ⊤
    rw [b66g_cform_order R t ∅ _ hlaw₀ y₁, b66g_ord_eq R t hq₀ hq₀0 y₁]
    exact WithTop.coe_ne_top
  have hdC := b4c_deg_canonical hE wC (hfin wC y₁ hgC) ⟨y₁, hgC⟩
  have hd₀ := b4c_deg_canonical hE w₀ (hfin w₀ y₁ hg₀) ⟨y₁, hg₀⟩
  have hsC := b4c_meroForm_orderSupport_finite hE wC
  have hs₀ := b4c_meroForm_orderSupport_finite hE w₀
  set F : Finset (rf8_fibre R.C t) := hsC.toFinset ∪ hs₀.toFinset ∪ {y₁}
  have hFC : Function.support (b4c_ordForm (hE := hE)
      (wC : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)) ⊆ F := fun y hy =>
    Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _
      ((Set.Finite.mem_toFinset hsC).mpr hy)))
  have hF₀ : Function.support (b4c_ordForm (hE := hE)
      (w₀ : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)) ⊆ F := fun y hy =>
    Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _
      ((Set.Finite.mem_toFinset hs₀).mpr hy)))
  rw [b66g_deg_eq_sum R t _ hsC F hFC] at hdC
  rw [b66g_deg_eq_sum R t _ hs₀ F hF₀] at hd₀
  simp only [hordC] at hdC
  simp only [hord₀] at hd₀
  have hsum : ∑ y ∈ F, b66g_ord R t q y =
      4 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 4 := by
    have := congrArg₂ (· + ·) hdC hd₀
    simp only [← Finset.sum_add_distrib, sub_add_cancel] at this
    rw [this]
    ring
  rw [← hsum]
  exact Finset.single_le_sum (fun y _ => b66g_ord_nonneg R t hq hq0 y)
    (Finset.mem_union_right _ (Finset.mem_singleton_self y₁))

/-- Laurent jet functionals of quadratic differentials at a fibre point. -/
def b66g_jet (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (y₁ : rf8_fibre R.C t)
    (N : ℕ) : b66g_forms R t 2 →ₗ[ℂ] (Fin N → ℂ) where
  toFun q k := TauCeti.Contour.residue (fun z => b66g_coef R t q.val y₁.val z /
    (z - (R.atlas.A y₁.val y₁.val).2) ^ ((k : ℕ) + 1)) (R.atlas.A y₁.val y₁.val).2
  map_add' q r := by
    funext k
    have hq := (b66g_coef_analytic' R t q.property y₁).meromorphicAt
    have hr := (b66g_coef_analytic' R t r.property y₁).meromorphicAt
    have hp : MeromorphicAt (fun z : ℂ => (z - (R.atlas.A y₁.val y₁.val).2) ^ ((k : ℕ) + 1))
        (R.atlas.A y₁.val y₁.val).2 := by fun_prop
    have h1 : MeromorphicAt (fun z => b66g_coef R t q.val y₁.val z /
        (z - (R.atlas.A y₁.val y₁.val).2) ^ ((k : ℕ) + 1)) (R.atlas.A y₁.val y₁.val).2 := hq.div hp
    have h2 : MeromorphicAt (fun z => b66g_coef R t r.val y₁.val z /
        (z - (R.atlas.A y₁.val y₁.val).2) ^ ((k : ℕ) + 1)) (R.atlas.A y₁.val y₁.val).2 := hr.div hp
    simp only [Pi.add_apply]
    rw [← TauCeti.Contour.residue_add h1 h2]
    congr 1
    funext z
    simp only [b66g_coef, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c q := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← TauCeti.Contour.residue_const_mul]
    congr 1
    funext z
    simp only [b66g_coef, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem b66g_jet_injective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (y₁ : rf8_fibre R.C t) :
    Function.Injective (b66g_jet R t y₁
      ((4 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 4).toNat + 1)) := by
  set M : ℤ := 4 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 4
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  by_contra hq0
  have hq0' : q.val ≠ 0 := fun h => hq0 (Subtype.ext h)
  have han := b66g_coef_analytic' R t q.property y₁
  have hder : ∀ i < M.toNat + 1, iteratedDeriv i (b66g_coef R t q.val y₁.val)
      (R.atlas.A y₁.val y₁.val).2 = 0 := by
    intro i hi
    have h := congrFun hq ⟨i, hi⟩
    change TauCeti.Contour.residue (fun z => b66g_coef R t q.val y₁.val z /
      (z - (R.atlas.A y₁.val y₁.val).2) ^ (i + 1)) (R.atlas.A y₁.val y₁.val).2 = 0 at h
    rw [TauCeti.Contour.residue_div_sub_pow_of_analyticAt han i] at h
    exact (div_eq_zero_iff.mp h).resolve_right (by exact_mod_cast Nat.factorial_ne_zero i)
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mpr hder
  have hbound := b66g_order_bound R t q.property hq0' y₁
  have hord := b66g_ord_eq R t q.property hq0' y₁
  rw [han.meromorphicOrderAt_eq] at hord
  have hfin : analyticOrderAt (b66g_coef R t q.val y₁.val) (R.atlas.A y₁.val y₁.val).2 ≠ ⊤ := by
    intro htop
    rw [htop] at hord
    exact WithTop.top_ne_coe hord
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hle hord
  have hn' : (n : ℤ) = b66g_ord R t q.val y₁ := by
    have : ((n : ℕ∞).map (Nat.cast : ℕ → ℤ)) = ((n : ℤ) : WithTop ℤ) := rfl
    rw [this] at hord
    exact_mod_cast hord
  have : M.toNat + 1 ≤ n := by exact_mod_cast hle
  omega

theorem b66g_forms_two_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Module.Finite ℂ (b66g_forms R t 2) := by
  obtain ⟨y⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  exact Module.Finite.of_injective _ (b66g_jet_injective R t y)

end B66gOrders
section B66gPrincipalCocycles

theorem b66g_boundary_cocycle (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) (a b c : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66k_boundary R t v a c x =
      b66k_boundary R t v b c x + b66k_vertical R t b c x * b66k_boundary R t v a b x := by
  simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A c).source from ⟨ha, hc⟩), ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩
      (R.atlas.A c).source from ⟨hb, hc⟩), ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A b).source from ⟨ha, hb⟩)]
  rw [b66g_vertical_comp R t a b c x ha hb hc]
  ring

theorem b66g_inv_point (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t a) :
    (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source ∧
      R.atlas.A a (t, ((R.atlas.A a).symm (t.val, w)).2) = (t.val, w) := by
  rw [b66k_inverse_slice R t a w hw]
  exact ⟨(R.atlas.A a).map_target hw, (R.atlas.A a).right_inv hw⟩

theorem b66g_vertical_eq_D (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t a) :
    b66k_vertical R t a b ((R.atlas.A a).symm (t.val, w)).2 =
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) := by
  unfold b66k_vertical
  rw [(b66g_inv_point R t a w hw).2]

theorem b66g_trans_point (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t a) :
    b66k_transition R a b (t.val, w) = (R.atlas.A b (t, ((R.atlas.A a).symm (t.val, w)).2)).2 := by
  unfold b66k_transition
  rw [b66k_inverse_slice R t a w hw]

theorem b66g_trans_inv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t a)
    (hb : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source) :
    b66k_transition R a b (t.val, w) ∈ b66k_domain R t b ∧
    ((R.atlas.A b).symm (t.val, b66k_transition R a b (t.val, w))).2 =
      ((R.atlas.A a).symm (t.val, w)).2 := by
  rw [b66g_trans_point R t a b w hw]
  set x := ((R.atlas.A a).symm (t.val, w)).2
  refine ⟨?_, (b66g_chart_slice R t b x hb).2⟩
  change (t.val, (R.atlas.A b (t, x)).2) ∈ (R.atlas.A b).target
  rw [← (b66g_chart_slice R t b x hb).1]
  exact (R.atlas.A b).map_source hb

theorem b66g_polar_analytic {M : ℕ} (cf : Fin M → ℂ) (w₀ z : ℂ) (h : z ≠ w₀) :
    AnalyticAt ℂ (fun w => ∑ k : Fin M, cf k / (w - w₀) ^ (k.val + 1)) z := by
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr h))

theorem b66g_polar_mero {M : ℕ} (cf : Fin M → ℂ) (w₀ z : ℂ) :
    MeromorphicAt (fun w => ∑ k : Fin M, cf k / (w - w₀) ^ (k.val + 1)) z := by
  apply MeromorphicAt.fun_sum
  intro k _
  exact (MeromorphicAt.const _ z).div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.pow _)

theorem b66g_G_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (f : ℂ → ℂ)
    (a b c : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t a)
    (ha : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source)
    (hb : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source)
    (hc : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A c).source) :
    fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) *
      (f (b66k_transition R a c (t.val, w)) / fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1)) =
    f (b66k_transition R b c (t.val, b66k_transition R a b (t.val, w))) /
      fderiv ℂ (b66k_transition R b c) (t.val, b66k_transition R a b (t.val, w)) (0, 1) := by
  set x := ((R.atlas.A a).symm (t.val, w)).2
  obtain ⟨hTd, hTx⟩ := b66g_trans_inv R t a b w hw hb
  have e1 : b66k_transition R b c (t.val, b66k_transition R a b (t.val, w)) =
      b66k_transition R a c (t.val, w) := by
    rw [b66g_trans_point R t b c _ hTd, hTx, ← b66g_trans_point R t a c w hw]
  have e2 : fderiv ℂ (b66k_transition R b c) (t.val, b66k_transition R a b (t.val, w)) (0, 1) =
      b66k_vertical R t b c x := by
    rw [← b66g_vertical_eq_D R t b c _ hTd, hTx]
  rw [e1, e2, ← b66g_vertical_eq_D R t a b w hw, ← b66g_vertical_eq_D R t a c w hw,
    b66g_vertical_comp R t a b c x ha hb hc]
  have hab := b66g_vertical_ne R t a b x ha hb
  have hbc := b66g_vertical_ne R t b c x hb hc
  field_simp
  ring

theorem b66g_boundary_near (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (F : b66k_Index R → ℂ → ℂ) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    ∀ᶠ w in 𝓝 z, b66k_boundary R t F a b ((R.atlas.A a).symm (t.val, w)).2 =
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) * F a w -
        F b (b66k_transition R a b (t.val, w)) := by
  filter_upwards [b66g_overlap_eventually R t a b z hz] with w ⟨hmem, h1, h2⟩
  simp only [b66k_boundary, ite_eq_left hmem]
  rw [h1, h2]
  unfold b66k_vertical
  rw [h1]

theorem b66g_piecewise_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x₁ : R.C)
    (G v ρ : b66k_Index R → ℂ → ℂ)
    (hG : ∀ a b w, w ∈ b66k_domain R t a →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A (t, x₁)).source →
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) * G a w =
        G b (b66k_transition R a b (t.val, w)))
    (hv : ∀ a, (t, x₁) ∈ (R.atlas.A a).source →
      ∀ᶠ w in 𝓝[≠] (R.atlas.A a (t, x₁)).2, v a w = G a w - ρ a w)
    (hρ : ∀ a, (t, x₁) ∈ (R.atlas.A a).source → AnalyticAt ℂ (ρ a) (R.atlas.A a (t, x₁)).2)
    (hva : ∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ x₁ →
      AnalyticAt ℂ (v a) z) :
    (fun a b x => if x = x₁ then b66k_boundary R t (fun a w => -ρ a w) a b x
      else b66k_boundary R t v a b x) ∈
      b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t) := by
  set u : b66k_Cochain R := fun a b x => if x = x₁ then b66k_boundary R t (fun a w => -ρ a w) a b x
      else b66k_boundary R t v a b x
  have hc₁ : (t, x₁) ∈ (R.atlas.A (t, x₁)).source := (R.atlas.hA _).1
  refine Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨fun a b z hz => ?_, fun a b x hx => ?_⟩, ?_⟩
  · -- analyticity on the refinement domain
    set x := ((R.atlas.A a).symm (t.val, z)).2
    obtain ⟨hTm, hTd, hTa, hDa⟩ := b66g_transition_mem R t a b z hz
    have hxa : (t, x) ∈ (R.atlas.A a).source := (b66g_inv_point R t a z hz.1).1
    have hxb : (t, x) ∈ (R.atlas.A b).source := by
      have := hz.2
      rwa [one_smul] at this
    have hza : (R.atlas.A a (t, x)).2 = z := by rw [(b66g_inv_point R t a z hz.1).2]
    have hTz : b66k_transition R a b (t.val, z) = (R.atlas.A b (t, x)).2 :=
      b66g_trans_point R t a b z hz.1
    have hopen : IsOpen (b66k_domain R t a) :=
      (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
    have hxcont : ContinuousAt (fun w => ((R.atlas.A a).symm (t.val, w)).2) z :=
      continuous_snd.continuousAt.comp (((R.atlas.A a).continuousAt_symm hz.1).comp
        (continuous_const.prodMk continuous_id).continuousAt)
    -- injectivity of the chart coordinate near z
    have hinj : ∀ᶠ w in 𝓝 z, ((R.atlas.A a).symm (t.val, w)).2 = x → w = z := by
      filter_upwards [hopen.mem_nhds hz.1] with w hw hwx
      have h1 := (b66g_inv_point R t a w hw).2
      rw [hwx] at h1
      exact (congrArg Prod.snd h1).symm.trans hza
    by_cases hx1 : x = x₁
    · have ha1 : (t, x₁) ∈ (R.atlas.A a).source := hx1 ▸ hxa
      have hb1 : (t, x₁) ∈ (R.atlas.A b).source := hx1 ▸ hxb
      have hza1 : (R.atlas.A a (t, x₁)).2 = z := hx1 ▸ hza
      have hTz1 : b66k_transition R a b (t.val, z) = (R.atlas.A b (t, x₁)).2 := hx1 ▸ hTz
      have hρa := hρ a ha1
      rw [hza1] at hρa
      have hρb := hρ b hb1
      rw [← hTz1] at hρb
      have hcomp : AnalyticAt ℂ (fun w => ρ b (b66k_transition R a b (t.val, w))) z :=
        AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) hρb hTa
      have hK : AnalyticAt ℂ (fun w => -(fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) *
          ρ a w) + ρ b (b66k_transition R a b (t.val, w))) z :=
        (hDa.mul hρa).neg.add hcomp
      apply hK.congr
      -- the transition tends to its value, avoiding it off z
      have hTcont : ContinuousAt (fun w => b66k_transition R a b (t.val, w)) z := hTa.continuousAt
      have hTinj : ∀ᶠ w in 𝓝 z, b66k_transition R a b (t.val, w) =
          (R.atlas.A b (t, x₁)).2 → w = z := by
        filter_upwards [b66g_overlap_eventually R t a b z hz, hinj] with w ⟨hmem, _, h2⟩ hi hT
        apply hi
        rw [← h2] at hT
        rw [hx1]
        have hpar1 := b66g_chart_slice R t b _ hmem.2
        have hpar2 := b66g_chart_slice R t b x₁ hb1
        have := (R.atlas.A b).injOn hmem.2 hb1 (by rw [hpar1.1, hpar2.1, hT])
        exact congrArg Prod.snd this
      have hvb := hv b hb1
      have htend : Tendsto (fun w => b66k_transition R a b (t.val, w)) (𝓝[≠] z)
          (𝓝[≠] (R.atlas.A b (t, x₁)).2) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · rw [← hTz1]
          exact hTcont.tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds hTinj, self_mem_nhdsWithin] with w h1 h2
          exact fun h => h2 (h1 h)
      have hva1 := hv a ha1
      rw [hza1] at hva1
      have hcmem : ∀ᶠ w in 𝓝 z, (t, ((R.atlas.A a).symm (t.val, w)).2) ∈
          (R.atlas.A (t, x₁)).source := by
        have hO : IsOpen {y : R.C | (t, y) ∈ (R.atlas.A (t, x₁)).source} :=
          (R.atlas.A (t, x₁)).open_source.preimage (continuous_const.prodMk continuous_id)
        refine hxcont.eventually (hO.mem_nhds ?_)
        change (t, x) ∈ (R.atlas.A (t, x₁)).source
        rw [hx1]
        exact hc₁
      filter_upwards [b66g_boundary_near R t v a b z hz,
        b66g_boundary_near R t (fun a w => -ρ a w) a b z hz, hcmem, hinj,
        b66g_overlap_eventually R t a b z hz, hopen.mem_nhds hz.1,
        eventually_nhdsWithin_iff.mp hva1, eventually_nhdsWithin_iff.mp (htend.eventually hvb)]
        with w hbv hbρ hwc hwi ⟨hmem, _, _⟩ hwd hva' hvb'
      by_cases hwz : w = z
      · rw [hwz] at hbρ ⊢
        have hx1' : ((R.atlas.A a).symm (t.val, z)).2 = x₁ := hx1
        simp only [u, ite_eq_left hx1']
        rw [hbρ]
        ring
      · have hne : ((R.atlas.A a).symm (t.val, w)).2 ≠ x₁ := fun h => hwz (hwi (h.trans hx1.symm))
        simp only [u, ite_eq_right hne]
        rw [hbv, hva' hwz, hvb' hwz]
        have hGl := hG a b w hwd hmem.1 hmem.2 hwc
        linear_combination -hGl
    · have hxc : ∀ᶠ w in 𝓝 z, ((R.atlas.A a).symm (t.val, w)).2 ≠ x₁ :=
        hxcont.eventually (isOpen_compl_singleton.mem_nhds hx1)
      have hvb : AnalyticAt ℂ (v b) (b66k_transition R a b (t.val, z)) := by
        apply hva b _ hTd
        rw [(b66g_trans_inv R t a b z hz.1 hxb).2]
        exact hx1
      have hK : AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) *
          v a w - v b (b66k_transition R a b (t.val, w))) z :=
        (hDa.mul (hva a z hz.1 hx1)).sub
          (AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) hvb hTa)
      apply hK.congr
      filter_upwards [b66g_boundary_near R t v a b z hz, hxc] with w hbv hne
      simp only [u, ite_eq_right hne]
      rw [hbv]
  · simp only [u]
    split_ifs <;> simp [b66k_boundary, hx]
  · rw [LinearMap.mem_ker]
    funext a b c x
    simp only [b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs with hm
    · obtain ⟨⟨ha, hb⟩, hc⟩ := hm
      simp only [u]
      split_ifs
      · rw [b66g_boundary_cocycle R t _ a b c x ha hb hc]
        ring
      · rw [b66g_boundary_cocycle R t _ a b c x ha hb hc]
        ring
    · rfl

theorem b66g_trans_self (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (c : b66k_Index R) (w : ℂ) (hw : w ∈ b66k_domain R t c) :
    b66k_transition R c c (t.val, w) = w ∧
      fderiv ℂ (b66k_transition R c c) (t.val, w) (0, 1) = 1 := by
  have hp := b66g_inv_point R t c w hw
  refine ⟨?_, ?_⟩
  · rw [b66g_trans_point R t c c w hw, hp.2]
  · rw [← b66g_vertical_eq_D R t c c w hw]
    exact b66g_vertical_self R t c _ hp.1

theorem b66g_principal_cocycle (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x₁ : R.C)
    (N : ℕ) (α : Fin N → ℂ) :
    ∃ (u : b66k_Cochain R)
      (_ : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ ({x₁} : Finset R.C) → AnalyticAt ℂ (v a) z) ∧
      (∀ a b x, x ∉ ({x₁} : Finset R.C) → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x) ∧
      ∀ q : b66g_forms R t 2, b66g_residueSum R t {x₁} v q.val =
        ∑ k, α k * b66g_jet R t (b66g_pt R t x₁) N q k := by
  set c : b66k_Index R := (t, x₁)
  have hc : (t, x₁) ∈ (R.atlas.A c).source := (R.atlas.hA c).1
  set z₁ := (R.atlas.A c (t, x₁)).2
  set ξ : ℂ → ℂ := fun z => ∑ k : Fin N, α k / (z - z₁) ^ (k.val + 1)
  set G : b66k_Index R → ℂ → ℂ := fun a w =>
    ξ (b66k_transition R a c (t.val, w)) / fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1)
  have hGm : ∀ a, (t, x₁) ∈ (R.atlas.A a).source → MeromorphicAt (G a) (R.atlas.A a (t, x₁)).2 := by
    intro a ha
    have hz := b66g_refinement_point R t 1 a c x₁ ha (by rwa [one_smul])
    obtain ⟨_, _, hT, hD⟩ := b66g_transition_mem R t a c _ hz
    exact ((b66g_polar_mero α z₁ _).comp_analyticAt hT).div hD.meromorphicAt
  have hpp : ∀ a, ∃ (M : ℕ) (cf : Fin M → ℂ) (ρ : ℂ → ℂ), (t, x₁) ∈ (R.atlas.A a).source →
      AnalyticAt ℂ ρ (R.atlas.A a (t, x₁)).2 ∧ ∀ᶠ w in 𝓝[≠] (R.atlas.A a (t, x₁)).2,
        G a w = ρ w + ∑ k : Fin M, cf k / (w - (R.atlas.A a (t, x₁)).2) ^ (k.val + 1) := by
    intro a
    by_cases ha : (t, x₁) ∈ (R.atlas.A a).source
    · obtain ⟨M, cf, ρ, h1, h2⟩ := b66g_principal_part (hGm a ha)
      exact ⟨M, cf, ρ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, Fin.elim0, 0, fun h => absurd h ha⟩
  choose M cf ρ hρ using hpp
  set v : b66k_Index R → ℂ → ℂ := fun a w => if (t, x₁) ∈ (R.atlas.A a).source then
    ∑ k : Fin (M a), cf a k / (w - (R.atlas.A a (t, x₁)).2) ^ (k.val + 1) else 0
  have hvG : ∀ a, (t, x₁) ∈ (R.atlas.A a).source →
      ∀ᶠ w in 𝓝[≠] (R.atlas.A a (t, x₁)).2, v a w = G a w - ρ a w := by
    intro a ha
    filter_upwards [(hρ a ha).2] with w hw
    simp only [v, ite_eq_left ha]
    rw [hw]
    ring
  have hva : ∀ a z, z ∈ b66k_domain R t a → ((R.atlas.A a).symm (t.val, z)).2 ≠ x₁ →
      AnalyticAt ℂ (v a) z := by
    intro a z hz hne
    by_cases ha : (t, x₁) ∈ (R.atlas.A a).source
    · simp only [v, ite_eq_left ha]
      apply b66g_polar_analytic
      intro hzeq
      apply hne
      rw [hzeq]
      exact (b66g_chart_slice R t a x₁ ha).2
    · simp only [v, ite_eq_right ha]
      exact analyticAt_const
  have hGlaw : ∀ a b w, w ∈ b66k_domain R t a →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source →
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A (t, x₁)).source →
      fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) * G a w =
        G b (b66k_transition R a b (t.val, w)) :=
    fun a b w hw ha hb hc => b66g_G_law R t ξ a b c w hw ha hb hc
  refine ⟨_, b66g_piecewise_mem R t x₁ G v ρ hGlaw hvG (fun a ha => (hρ a ha).1) hva, v,
    fun a z hz => ?_, fun a z hz hS => hva a z hz (fun h => hS (Finset.mem_singleton.mpr h)),
    fun a b x hx _ _ => ?_, fun q => ?_⟩
  · by_cases ha : (t, x₁) ∈ (R.atlas.A a).source
    · simp only [v, ite_eq_left ha]
      exact b66g_polar_mero _ _ _
    · simp only [v, ite_eq_right ha]
      exact MeromorphicAt.const 0 z
  · have hx' : x ≠ x₁ := fun h => hx (Finset.mem_singleton.mpr h)
    simp only [ite_eq_right hx']
  · set Q : ℂ → ℂ := fun z => q.val c ((R.atlas.A c).symm (t.val, z)).2
    have hQ : AnalyticAt ℂ Q z₁ := b66g_coef_analytic R t q.property x₁
    have hdom : z₁ ∈ b66k_domain R t c := b66g_own_domain R t x₁
    have hopen : IsOpen (b66k_domain R t c) :=
      (R.atlas.A c).open_target.preimage (continuous_const.prodMk continuous_id)
    have hρc := (hρ c hc).1
    have hev : (fun z => v c z * Q z) =ᶠ[𝓝[≠] z₁] fun z => ξ z * Q z - ρ c z * Q z := by
      filter_upwards [hvG c hc, nhdsWithin_le_nhds (hopen.mem_nhds hdom)] with w h1 h2
      rw [h1]
      have hs := b66g_trans_self R t c w h2
      simp only [G, hs.1, hs.2, div_one]
      ring
    have hm1 : MeromorphicAt (fun z => ξ z * Q z) z₁ :=
      (b66g_polar_mero α z₁ z₁).mul hQ.meromorphicAt
    have hm2 : MeromorphicAt (fun z => ρ c z * Q z) z₁ := (hρc.mul hQ).meromorphicAt
    rw [show b66g_residueSum R t {x₁} v q.val = TauCeti.Contour.residue
      (fun z => v c z * Q z) z₁ from Finset.sum_singleton _ _,
      TauCeti.Contour.residue_congr_nhdsNE hev,
      show (fun z => ξ z * Q z - ρ c z * Q z) = (fun z => ξ z * Q z) - (fun z => ρ c z * Q z)
        from rfl, TauCeti.Contour.residue_sub hm1 hm2,
      TauCeti.Contour.residue_eq_zero_of_analyticAt (f := fun z => ρ c z * Q z) (hρc.mul hQ),
      sub_zero]
    have hξQ : (fun z => ξ z * Q z) =
        ∑ k : Fin N, fun z => α k * (Q z / (z - z₁) ^ (k.val + 1)) := by
      funext z
      simp only [ξ, Finset.sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hmk : ∀ k ∈ (Finset.univ : Finset (Fin N)),
        MeromorphicAt (fun z => α k * (Q z / (z - z₁) ^ (k.val + 1))) z₁ := fun k _ =>
      (MeromorphicAt.const _ z₁).mul (hQ.meromorphicAt.div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.pow _))
    rw [hξQ, TauCeti.Contour.residue_sum _ hmk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TauCeti.Contour.residue_const_mul]
    rfl

theorem b66g_serre_surjective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (E : b66k_cechH1 R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2))
    (hE : ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      E c q = b66g_residueSum R t S v q.val) :
    Function.Surjective E := by
  intro lam
  obtain ⟨y₁⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  set x₁ := y₁.val.2
  set N := (4 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 4).toNat + 1
  have hJ := b66g_jet_injective R t (b66g_pt R t x₁)
  obtain ⟨μ, hμ⟩ := LinearMap.dualMap_surjective_of_injective hJ lam
  set α : Fin N → ℂ := fun k => μ (fun j => if k = j then 1 else 0)
  obtain ⟨u, hu, v, hmero, hreg, hv, hres⟩ := b66g_principal_cocycle R t x₁ N α
  refine ⟨⟨(b66k_boundaries R t).mkQ u, Submodule.mem_map_of_mem hu⟩, ?_⟩
  apply LinearMap.ext
  intro q
  rw [hE u hu _ rfl {x₁} v hmero hreg hv q, hres q, ← hμ, LinearMap.dualMap_apply,
    LinearMap.pi_apply_eq_sum_univ μ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]
  ring

end B66gPrincipalCocycles
section B66gScalarDualityAll
attribute [local instance] b3Forms_isManifold_real

section B66gMLDual
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]

theorem b66g_mittagLeffler_dual [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (γ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (hγ : γ ∈ b4c_Smooth01 ℂ C) (x₀ : C) :
    ∃ F P : C → ℂ, ∃ N : ℕ, ∃ c : Fin N → ℂ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y) ∧
      (∀ y, y ≠ x₀ → ∀ v : ℂ, b4c_dbar ℂ C (F + P) ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      (∀ᶠ y in 𝓝 x₀, ∀ v : ℂ, b4c_dbar ℂ C F ⟨y, v⟩ = γ ⟨y, v⟩) ∧
      (P =ᶠ[𝓝 x₀] fun y => ∑ n, c n /
        RiemannRochAna_coordinate (Module.finrank_self ℂ) x₀ y ^ ((n : ℕ) + 1)) ∧
      ((∀ θ : b3_HolForm ℂ C, ∑ n, c n * TauCeti.Contour.residue (fun τ =>
          HurwitzPrymRR_loc (Module.finrank_self ℂ) θ x₀ τ / τ ^ ((n : ℕ) + 1)) 0 = 0) →
        ∃ G : C → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G ∧
          ∀ q, b4c_dbar ℂ C (F + G) q = γ q) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨m, hm⟩ := b66g_principalClass_top (C := C) x₀
  set D : C →₀ ℤ := Finsupp.single x₀ (m : ℤ)
  let g : b4c_Smooth01 ℂ C := ⟨γ, hγ⟩
  have hg : (Submodule.mkQ _ g : b4c_Dolbeault01 ℂ C) ∈
      LinearMap.range (RiemannRochAna_principalClassLinear hE D) := by
    rw [hm]
    trivial
  obtain ⟨c', hc'⟩ := hg
  have hdiff : g - RiemannRochAna_principalObstructionLinear hE D c' ∈
      (Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
        (b4c_Smooth01 ℂ C).subtype := by
    rw [← Submodule.Quotient.eq]
    exact hc'.symm
  have hmem : γ - (RiemannRochAna_principalObstructionLinear hE D c').1 ∈
      b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) := by
    rw [← b4c_dbar_image_eq hE]
    exact hdiff
  obtain ⟨F, hF, hFd⟩ := hmem
  have hsupp : ∀ i : D.support, i.1 = x₀ := by
    intro i
    have := Finsupp.support_single_subset i.2
    simpa using this
  refine ⟨F, RiemannRochAna_principalScalar hE D c', ?_⟩
  have hoff : ∀ y, y ≠ x₀ → y ∉ D.support := fun y hy hyD => hy (hsupp ⟨y, hyD⟩)
  have hP : ∀ y, y ≠ x₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (RiemannRochAna_principalScalar hE D c') y := fun y hy =>
    RiemannRochAna_principalScalar_smooth_off_support hE D c' y (hoff y hy)
  have hdF : ∀ q, b4c_dbar ℂ C F q = γ q - (RiemannRochAna_principalObstructionLinear hE D c').1 q :=
    fun q => congrFun hFd q
  have hnear : ∀ᶠ y in 𝓝 x₀, ∀ v : ℂ,
      (RiemannRochAna_principalObstructionLinear hE D c').1 ⟨y, v⟩ = 0 := by
    have hall : ∀ᶠ y in 𝓝 x₀, ∀ (i : D.support) (n : Fin (Int.toNat (D i.1))) (v : ℂ),
        RiemannRochAna_principalObstructionPow hE i.1
          (RiemannRochAna_divisorCutoff hE D i) n ⟨y, v⟩ = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro n
      have h := RiemannRochAna_principalObstructionPow_zero_germ hE i.1
        (RiemannRochAna_divisorCutoff hE D i) n (RiemannRochAna_divisorCutoff_spec hE D i).2.1
      have hx : (i : C) = x₀ := hsupp i
      exact hx ▸ h
    filter_upwards [hall] with y hy v
    rw [RiemannRochAna_principalObstructionLinear_apply]
    simp only [hy, mul_zero, Finset.sum_const_zero]
  by_cases hx : x₀ ∈ D.support
  · let i : D.support := ⟨x₀, hx⟩
    refine ⟨Int.toNat (D x₀), c' i, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · have hFm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y := (hF y).mdifferentiableAt (by simp)
      have hPm := (hP y hy).mdifferentiableAt (by simp)
      rw [RiemannRochAna_dbar_add_at _ _ y hFm hPm v, hdF,
        RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v]
      ring
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · refine ⟨RiemannRochAna_principalScalar_germ hE D c' i, fun hθ => ?_⟩
      have hker : c' ∈ LinearMap.ker (RiemannRochAna_principalResidueLinear hE D) := by
        rw [LinearMap.mem_ker]
        apply LinearMap.ext
        intro θ
        change RiemannRochAna_principalResiduePairing hE D c' θ = 0
        unfold RiemannRochAna_principalResiduePairing
        rw [Finset.sum_eq_single i (fun j _ hji => absurd (Subtype.ext ((hsupp j).trans
          (hsupp i).symm)) hji) (fun h => absurd (Finset.mem_univ i) h)]
        exact hθ θ
      have hD : ∀ y, 0 ≤ D y := by
        intro y
        simp only [D, Finsupp.single_apply]
        split_ifs <;> positivity
      rw [← RiemannRochAna_principalClass_kernel_eq_residueKernel_effective hE D hD x₀,
        LinearMap.mem_ker] at hker
      have hob : RiemannRochAna_principalObstructionLinear hE D c' ∈
          (Submodule.span ℂ (b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)))).comap
            (b4c_Smooth01 ℂ C).subtype :=
        (Submodule.Quotient.mk_eq_zero _).mp hker
      have hmem2 : (RiemannRochAna_principalObstructionLinear hE D c').1 ∈
          b4c_dbar ℂ C '' (b4c_SmoothFun ℂ C : Set (C → ℂ)) := by
        rw [← b4c_dbar_image_eq hE]
        exact hob
      obtain ⟨G, hG, hGd⟩ := hmem2
      refine ⟨G, hG, fun q => ?_⟩
      obtain ⟨y, v⟩ := q
      rw [RiemannRochAna_dbar_add_at _ _ y ((hF y).mdifferentiableAt (by simp))
        ((hG y).mdifferentiableAt (by simp)) v, hdF, congrFun hGd]
      ring
  · have hzero : RiemannRochAna_principalScalar hE D c' = 0 := by
      funext y
      apply Finset.sum_eq_zero
      intro i _
      exact absurd (hsupp i ▸ i.2) hx
    refine ⟨0, Fin.elim0, hF, hP, fun y hy v => ?_, ?_, ?_⟩
    · rw [hzero, add_zero, hdF]
      have := RiemannRochAna_principalScalar_dbar hE D c' y (hoff y hy) v
      rw [hzero] at this
      rw [← this]
      have h0 := RiemannRochAna_dbar_const_germ (E := ℂ) (C := C) (u := (0 : C → ℂ)) (x := y)
        (a := 0) (Filter.EventuallyEq.refl _ _) v
      rw [h0, sub_zero]
    · filter_upwards [hnear] with y hy v
      rw [hdF, hy v, sub_zero]
    · refine ⟨by rw [hzero]; exact Filter.Eventually.of_forall fun y => by simp, fun _ => ?_⟩
      refine ⟨0, contMDiff_const, fun q => ?_⟩
      obtain ⟨y, v⟩ := q
      rw [add_zero, hdF]
      have h0 : (RiemannRochAna_principalObstructionLinear hE D c').1 ⟨y, v⟩ = 0 := by
        rw [RiemannRochAna_principalObstructionLinear_apply]
        apply Finset.sum_eq_zero
        intro i _
        exact absurd (hsupp i ▸ i.2) hx
      rw [h0, sub_zero]

end B66gMLDual

section B66gScalarDuality

theorem b66g_cform_coef (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (η : b66g_Coeff R) :
    b66g_cform R t (b66g_coef R t η) = b66g_toForm R t η := by
  funext P
  obtain ⟨p, v⟩ := P
  change η p.val ((R.atlas.A p.val).symm (t.val, b66g_slice R t p.val p)).2 *
    b66g_sliceD R t p.val p v = η p.val p.val.2 * b66g_sliceD R t p.val p v
  rw [b66g_inv_slice R t p.val p (R.atlas.hA p.val).1]

theorem b66g_coef_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {η : b66g_Coeff R}
    (hη : η ∈ b66g_forms R t 1) :
    ∀ a b x, x ∉ (∅ : Finset R.C) → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66g_coef R t η a (R.atlas.A a (t, x)).2 =
        b66k_vertical R t a b x * b66g_coef R t η b (R.atlas.A b (t, x)).2 := by
  intro a b x _ ha hb
  simp only [b66g_coef]
  rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
    (b66g_forms_spec R t 1 hη).2.1 a b x ha hb, pow_one]

theorem b66g_tauF_holo (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (y₀ : rf8_fibre R.C t)
    (F : rf8_fibre R.C t → ℂ) (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F)
    (hFnear : ∀ᶠ y in 𝓝 y₀, ∀ v : ℂ,
      b4c_dbar ℂ (rf8_fibre R.C t) F ⟨y, v⟩ = b66g_gamma R t ρ s ⟨y, v⟩)
    (a : b66k_Index R) (hya : y₀.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_tau R t ρ s a - F) y₀ := by
  apply RiemannRochAna_analyticAt_of_dbar_germ (Module.finrank_self ℂ) _ y₀
  filter_upwards [(b66g_open_source R t a).mem_nhds hya, hFnear,
    b66g_gamma_local R t ρ hρ hs a y₀ hya] with y' h1 h2 h3
  have hτ := b66g_tau_smooth R t ρ hρ hs a y' h1
  refine ⟨hτ.sub (hF y'), fun v => ?_⟩
  rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
    ((hF y').mdifferentiableAt (by simp)) v, h2 v, h3 v, sub_self]

theorem b66g_residue_at_pole (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (y₀ : rf8_fibre R.C t)
    (F P : rf8_fibre R.C t → ℂ) (N : ℕ) (c : Fin N → ℂ)
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F)
    (hP : ∀ y, y ≠ y₀ → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ P y)
    (hFP : ∀ y, y ≠ y₀ → ∀ v : ℂ,
      b4c_dbar ℂ (rf8_fibre R.C t) (F + P) ⟨y, v⟩ = b66g_gamma R t ρ s ⟨y, v⟩)
    (hFnear : ∀ᶠ y in 𝓝 y₀, ∀ v : ℂ,
      b4c_dbar ℂ (rf8_fibre R.C t) F ⟨y, v⟩ = b66g_gamma R t ρ s ⟨y, v⟩)
    (hPg : P =ᶠ[𝓝 y₀] fun y => ∑ n, c n /
        RiemannRochAna_coordinate (Module.finrank_self ℂ) y₀ y ^ ((n : ℕ) + 1))
    {η : b66g_Coeff R} (hη : η ∈ b66g_forms R t 1) :
    TauCeti.Contour.residue (fun z =>
      (b66g_tau R t ρ s y₀.val - (F + P)) (b66g_pt R t ((R.atlas.A y₀.val).symm (t.val, z)).2) *
        b66g_coef R t η y₀.val z) (R.atlas.A y₀.val y₀.val).2 =
      -∑ n, c n * TauCeti.Contour.residue (fun τ =>
        HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66g_toForm R t η) y₀ τ / τ ^ ((n : ℕ) + 1)) 0 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  set a := y₀.val
  have ha : y₀.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  obtain ⟨hΦ, hΦd, hΦ0⟩ := b66g_chartPhi R t y₀
  set e := extChartAt 𝓘(ℂ, ℂ) y₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set Φ := fun τ => (b66g_slice R t a ∘ e.symm) (e y₀ + τ * c₀)
  have hsm := b66g_split_of_ml R t ρ hρ hs y₀ F P N c hF hP hFP hFnear hPg
  have hdom := b66g_slice_domain R t a y₀ ha
  have hm := hsm.1 a _ hdom
  have hQ := (b66g_forms_spec R t 1 hη).1 a _ hdom
  have hf : MeromorphicAt (fun z => (b66g_tau R t ρ s a - (F + P))
      (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2) * b66g_coef R t η a z) (Φ 0) := by
    rw [hΦ0]
    exact hm.mul hQ.meromorphicAt
  rw [← hΦ0, ← b66g_residue_comp hΦ hΦd hf]
  set L := HurwitzPrymRR_loc hE (b66g_toForm R t η) y₀
  have hL : AnalyticAt ℂ L 0 :=
    RiemannRochAna_hol_loc_analytic hE ⟨b66g_toForm R t η, b66g_toForm_mem R t hη⟩ y₀
  have hLeq : L =ᶠ[𝓝[≠] 0] fun τ => b66g_coef R t η a (Φ τ) * deriv Φ τ := by
    have h := b66g_cform_loc R t ∅ (b66g_coef R t η) (b66g_coef_law R t hη) y₀
    rwa [b66g_cform_coef] at h
  have hx₀e : y₀ ∈ e.source := mem_extChartAt_source y₀
  have hex : e y₀ ∈ e.target := e.map_source hx₀e
  have hsc : Tendsto (fun τ : ℂ => e y₀ + τ * c₀) (𝓝 0) (𝓝 (e y₀)) := by
    have : Continuous (fun τ : ℂ => e y₀ + τ * c₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e y₀ + τ * c₀)) (𝓝 0) (𝓝 y₀) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  have hAτ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_tau R t ρ s a - F) y₀ :=
    b66g_tauF_holo R t ρ hρ hs y₀ F hF hFnear a ha
  have hA : AnalyticAt ℂ (fun τ => (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀))) 0 := by
    have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y₀) :=
      (contMDiffOn_extChartAt_symm y₀ (e y₀) hex).contMDiffAt (extChartAt_target_mem_nhds' hex)
    have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66g_tau R t ρ s a - F) (e.symm (e y₀)) := by
      rw [e.left_inv hx₀e]
      exact hAτ
    have h2 := (h1.comp (e y₀) hsym)
    have h3 : AnalyticAt ℂ ((b66g_tau R t ρ s a - F) ∘ e.symm) (e y₀) :=
      (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
    have hsa : AnalyticAt ℂ (fun σ : ℂ => e y₀ + σ * c₀) 0 := by fun_prop
    have h4 : AnalyticAt ℂ ((b66g_tau R t ρ s a - F) ∘ e.symm) ((fun σ : ℂ => e y₀ + σ * c₀) 0) := by
      simpa using h3
    exact AnalyticAt.comp (f := fun σ : ℂ => e y₀ + σ * c₀) h4 hsa
  have hcl : ∀ᶠ τ in 𝓝 (0 : ℂ), e y₀ + τ * c₀ ∈ e.target ∧
      e.symm (e y₀ + τ * c₀) ∈ {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} ∧
      P (e.symm (e y₀ + τ * c₀)) = ∑ n, c n / RiemannRochAna_coordinate hE y₀
        (e.symm (e y₀ + τ * c₀)) ^ ((n : ℕ) + 1) :=
    (hsc.eventually (extChartAt_target_mem_nhds' hex)).and
      ((hsymc.eventually ((b66g_open_source R t a).mem_nhds ha)).and (hsymc.eventually hPg))
  have hclaim : (fun τ => (b66g_tau R t ρ s a - (F + P))
      (b66g_pt R t ((R.atlas.A a).symm (t.val, Φ τ)).2) * b66g_coef R t η a (Φ τ) * deriv Φ τ)
      =ᶠ[𝓝[≠] 0] fun τ => (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀)) * L τ -
        ∑ n, c n * (L τ / τ ^ ((n : ℕ) + 1)) := by
    filter_upwards [hLeq, nhdsWithin_le_nhds hcl] with τ h1 ⟨h2, h3, h4⟩
    have hpt : b66g_pt R t ((R.atlas.A a).symm (t.val, Φ τ)).2 = e.symm (e y₀ + τ * c₀) := by
      simp only [Φ, Function.comp_apply]
      rw [b66g_inv_slice R t a _ h3]
      exact b66g_fibre_mk R t _
    have hco : RiemannRochAna_coordinate hE y₀ (e.symm (e y₀ + τ * c₀)) = τ := by
      unfold RiemannRochAna_coordinate
      rw [e.right_inv h2, add_sub_cancel_left, ← b66g_lineEquiv_apply τ]
      exact LinearEquiv.symm_apply_apply _ τ
    rw [hpt, h1]
    simp only [Pi.sub_apply, Pi.add_apply, h4, hco]
    set K := b66g_coef R t η a (Φ τ) * deriv Φ τ
    have hsum : ∑ x, c x * (K / τ ^ ((x : ℕ) + 1)) = (∑ x, c x / τ ^ ((x : ℕ) + 1)) * K := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [mul_assoc, hsum]
    ring
  rw [TauCeti.Contour.residue_congr_nhdsNE hclaim]
  have hm1 : MeromorphicAt (fun τ => (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀)) * L τ) 0 :=
    (hA.mul hL).meromorphicAt
  have hmk : ∀ n ∈ (Finset.univ : Finset (Fin N)),
      MeromorphicAt (fun τ => c n * (L τ / τ ^ ((n : ℕ) + 1))) 0 := fun n _ =>
    (MeromorphicAt.const _ 0).mul (hL.meromorphicAt.div (analyticAt_id.meromorphicAt.pow _))
  have hm2 : MeromorphicAt (fun τ => ∑ n, c n * (L τ / τ ^ ((n : ℕ) + 1))) 0 :=
    MeromorphicAt.fun_sum hmk
  rw [show (fun τ => (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀)) * L τ -
      ∑ n, c n * (L τ / τ ^ ((n : ℕ) + 1))) =
      (fun τ => (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀)) * L τ) -
      (fun τ => ∑ n, c n * (L τ / τ ^ ((n : ℕ) + 1))) from rfl,
    TauCeti.Contour.residue_sub hm1 hm2,
    TauCeti.Contour.residue_eq_zero_of_analyticAt (f := fun τ =>
      (b66g_tau R t ρ s a - F) (e.symm (e y₀ + τ * c₀)) * L τ) (hA.mul hL), zero_sub,
    show (fun τ => ∑ n, c n * (L τ / τ ^ ((n : ℕ) + 1))) =
      ∑ n, (fun τ => c n * (L τ / τ ^ ((n : ℕ) + 1))) by
        funext τ
        rw [Finset.sum_apply],
    TauCeti.Contour.residue_sum _ hmk]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [TauCeti.Contour.residue_const_mul]

theorem b66g_scalar_split_unique (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (s : b66k_Cochain R) (S S' : Finset R.C) (h h' : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (h a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (h a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      s a b x = h a (R.atlas.A a (t, x)).2 - h b (R.atlas.A b (t, x)).2)
    (hmero' : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (h' a) z)
    (hreg' : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S' → AnalyticAt ℂ (h' a) z)
    (hv' : ∀ a b x, x ∉ S' → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      s a b x = h' a (R.atlas.A a (t, x)).2 - h' b (R.atlas.A b (t, x)).2)
    {η : b66g_Coeff R} (hη : η ∈ b66g_forms R t 1) :
    b66g_residueSum R t S h η = b66g_residueSum R t S' h' η := by
  obtain ⟨hqa, hql, _⟩ := b66g_forms_spec R t 1 hη
  set T := S ∪ S'
  rw [← b66g_residueSum_extend R t S T h hreg hη Finset.subset_union_left,
    ← b66g_residueSum_extend R t S' T h' hreg' hη Finset.subset_union_right,
    ← sub_eq_zero, b66g_residueSum_sub R t T h h' hmero hmero' hη]
  apply b66g_cform_residue_sum R t T
    (fun a z => (h a z - h' a z) * η a ((R.atlas.A a).symm (t.val, z)).2)
  · intro a z hz
    exact ((hmero a z hz).sub (hmero' a z hz)).mul (hqa a z hz).meromorphicAt
  · intro a z hz hT
    have h1 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S := fun h => hT (Finset.mem_union_left _ h)
    have h2 : ((R.atlas.A a).symm (t.val, z)).2 ∉ S' := fun h => hT (Finset.mem_union_right _ h)
    exact ((hreg a z hz h1).sub (hreg' a z hz h2)).mul (hqa a z hz)
  · intro a b x hx ha hb
    have e1 := hv a b x (fun h => hx (Finset.mem_union_left _ h)) ha hb
    have e2 := hv' a b x (fun h => hx (Finset.mem_union_right _ h)) ha hb
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2, hql a b x ha hb, pow_one]
    linear_combination (b66k_vertical R t a b x * η b x) * (e2 - e1)

theorem b66g_scalar_dual (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (S : Finset R.C)
    (h : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (h a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (h a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      s a b x = h a (R.atlas.A a (t, x)).2 - h b (R.atlas.A b (t, x)).2)
    (hpair : ∀ η, η ∈ b66g_forms R t 1 → b66g_residueSum R t S h η = 0) :
    ∃ h' : b66k_Index R → ℂ → ℂ, (∀ a, AnalyticOnNhd ℂ (h' a) (b66k_domain R t a)) ∧
      ∀ a b x, (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
        s a b x = h' a (R.atlas.A a (t, x)).2 - h' b (R.atlas.A b (t, x)).2 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (M := rf8_fibre R.C t) isClosed_univ
    (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
    (fun c => b66g_open_source R t c)
    (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
  obtain ⟨y'⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  set x₀ := y'.val.2
  set y₀ := b66g_pt R t x₀
  obtain ⟨F, P, N, c, hF, hP, hFP, hFnear, hPg, hdual⟩ :=
    b66g_mittagLeffler_dual (b66g_gamma R t ρ s) (b66g_gamma_mem R t ρ hρ hs) y₀
  obtain ⟨hm, han, hsp⟩ := b66g_split_of_ml R t ρ hρ hs y₀ F P N c hF hP hFP hFnear hPg
  have hθ : ∀ θ : b3_HolForm ℂ (rf8_fibre R.C t), ∑ n, c n * TauCeti.Contour.residue (fun τ =>
      HurwitzPrymRR_loc hE θ y₀ τ / τ ^ ((n : ℕ) + 1)) 0 = 0 := by
    intro θ
    set η := b66g_ofForm R t θ.1
    have hη : η ∈ b66g_forms R t 1 := b66g_ofForm_mem R t θ.2
    have hθη : b66g_toForm R t η = θ.1 := b66g_toForm_ofForm R t θ.2.2
    have h1 := hpair η hη
    rw [b66g_scalar_split_unique R t s S {x₀} h _ hmero hreg hv (hm)
      (fun a z hz hS => han a z hz (fun h => hS (Finset.mem_singleton.mpr h))) (fun a b x _ ha hb => hsp a b x ha hb) hη] at h1
    have h2 := b66g_residue_at_pole R t ρ hρ hs y₀ F P N c hF hP hFP hFnear hPg hη
    rw [hθη] at h2
    have h3 : b66g_residueSum R t {x₀} (fun a w =>
        (b66g_tau R t ρ s a - (F + P)) (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) η =
        TauCeti.Contour.residue (fun z =>
          (b66g_tau R t ρ s y₀.val - (F + P)) (b66g_pt R t ((R.atlas.A y₀.val).symm (t.val, z)).2) *
          b66g_coef R t η y₀.val z) (R.atlas.A y₀.val y₀.val).2 := Finset.sum_singleton _ _
    rw [h3, h2, neg_eq_zero] at h1
    exact h1
  obtain ⟨G, hG, hFG⟩ := hdual hθ
  set H : b66k_Index R → rf8_fibre R.C t → ℂ := fun a => b66g_tau R t ρ s a - (F + G)
  have hH : ∀ a y, y.val ∈ (R.atlas.A a).source → ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (H a) y := by
    intro a y hy
    apply RiemannRochAna_analyticAt_of_dbar_germ hE _ y
    filter_upwards [(b66g_open_source R t a).mem_nhds hy] with y' h1
    have hτ := b66g_tau_smooth R t ρ hρ hs a y' h1
    have hFG' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (F + G) y' := (hF y').add (hG y')
    refine ⟨hτ.sub hFG', fun v => ?_⟩
    rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
      (hFG'.mdifferentiableAt (by simp)) v, hFG,
      ← (b66g_gamma_local R t ρ hρ hs a y' h1).self_of_nhds v, sub_self]
  refine ⟨fun a w => H a (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2), fun a z hz => ?_,
    fun a b x ha hb => ?_⟩
  · apply b66g_coord_analytic R t (H a) a z hz
    apply hH a
    change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
    rw [b66k_inverse_slice R t a z hz]
    exact (R.atlas.A a).map_target hz
  · simp only
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2]
    have := b66g_tau_sub R t ρ hρ hs a b (b66g_pt R t x) ha hb
    simp only [H, Pi.sub_apply, Pi.add_apply]
    change _ = s a b x at this
    linear_combination -this

end B66gScalarDuality
end B66gScalarDualityAll

section B66gNormalForms

/-- Pointwise removal of removable singularities. -/
def b66g_nf (f : ℂ → ℂ) : ℂ → ℂ := fun z => toMeromorphicNFAt f z z

theorem b66g_nf_eq {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) : b66g_nf f z = f z := by
  unfold b66g_nf
  rw [toMeromorphicNFAt_eq_self.mpr hf.meromorphicNFAt]

theorem b66g_nf_analytic {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀)
    (hnn : 0 ≤ meromorphicOrderAt f z₀) : AnalyticAt ℂ (b66g_nf f) z₀ := by
  have hg := hf.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hnn
  apply hg.congr
  have hev : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ f z := hf.eventually_analyticAt
  filter_upwards [eventually_nhdsWithin_iff.mp hev] with z hz
  by_cases hzz : z = z₀
  · subst hzz
    rfl
  · rw [b66g_nf_eq (hz hzz)]
    exact (hf.eqOn_compl_singleton_toMeromorphicNFAt hzz).symm

theorem b66g_nf_eventually {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    ∀ᶠ z in 𝓝[≠] z₀, b66g_nf f z = f z := by
  filter_upwards [hf.eventually_analyticAt] with z hz
  exact b66g_nf_eq hz

theorem b66g_eq_of_nhdsNE {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (h : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

theorem b66g_xa_inj (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) :
    ∀ᶠ w in 𝓝 z, ((R.atlas.A a).symm (t.val, w)).2 = ((R.atlas.A a).symm (t.val, z)).2 → w = z := by
  have hopen : IsOpen (b66k_domain R t a) :=
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  filter_upwards [hopen.mem_nhds hz] with w hw hwx
  have h1 := (b66g_inv_point R t a w hw).2
  have h2 := (b66g_inv_point R t a z hz).2
  rw [hwx, h2] at h1
  exact (congrArg Prod.snd h1).symm

theorem b66g_xa_continuous (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) :
    ContinuousAt (fun w => ((R.atlas.A a).symm (t.val, w)).2) z :=
  continuous_snd.continuousAt.comp (((R.atlas.A a).continuousAt_symm hz).comp
    (continuous_const.prodMk continuous_id).continuousAt)

theorem b66g_avoid (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) (S : Finset R.C) :
    ∀ᶠ w in 𝓝[≠] z, ((R.atlas.A a).symm (t.val, w)).2 ∉ S := by
  set x := ((R.atlas.A a).symm (t.val, z)).2
  have hcl : IsClosed (↑(S.erase x) : Set R.C) := (S.erase x).finite_toSet.isClosed
  have h1 : ∀ᶠ w in 𝓝 z, ((R.atlas.A a).symm (t.val, w)).2 ∉ (↑(S.erase x) : Set R.C) :=
    (b66g_xa_continuous R t a z hz).eventually
      (hcl.isOpen_compl.mem_nhds (by
        intro h
        exact (Finset.mem_erase.mp (Finset.mem_coe.mp h)).1 rfl))
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds (b66g_xa_inj R t a z hz),
    self_mem_nhdsWithin] with w hw1 hw2 hw3 hS
  by_cases hwx : ((R.atlas.A a).symm (t.val, w)).2 = x
  · exact hw3 (hw2 hwx)
  · exact hw1 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwx, hS⟩))

theorem b66g_trans_tendsto (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_refinementDomain R t 1 a b) :
    Tendsto (fun w => b66k_transition R a b (t.val, w)) (𝓝[≠] z)
      (𝓝[≠] (b66k_transition R a b (t.val, z))) := by
  obtain ⟨_, _, hTa, _⟩ := b66g_transition_mem R t a b z hz
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact hTa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hxb : (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A b).source := by
      have := hz.2
      rwa [one_smul] at this
    filter_upwards [nhdsWithin_le_nhds (b66g_overlap_eventually R t a b z hz),
      nhdsWithin_le_nhds (b66g_xa_inj R t a z hz.1), self_mem_nhdsWithin]
      with w ⟨hmem, _, h2⟩ hi hwz hT
    apply hwz
    apply hi
    rw [← h2, b66g_trans_point R t a b z hz.1] at hT
    have hpar1 := b66g_chart_slice R t b _ hmem.2
    have hpar2 := b66g_chart_slice R t b _ hxb
    have := (R.atlas.A b).injOn hmem.2 hxb (by rw [hpar1.1, hpar2.1, hT])
    exact (Prod.ext_iff.mp this).2

theorem b66g_forms_ext (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {m : ℕ}
    {q q' : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (hq' : q' ∈ b66g_forms R t m)
    (h : ∀ a z, z ∈ b66k_domain R t a → b66g_coef R t q a =ᶠ[𝓝[≠] z] b66g_coef R t q' a) :
    q = q' := by
  funext a x
  by_cases hx : (t, x) ∈ (R.atlas.A a).source
  · have hdom : (R.atlas.A a (t, x)).2 ∈ b66k_domain R t a := by
      change (t.val, (R.atlas.A a (t, x)).2) ∈ (R.atlas.A a).target
      rw [← (b66g_chart_slice R t a x hx).1]
      exact (R.atlas.A a).map_source hx
    have e := b66g_eq_of_nhdsNE ((b66g_forms_spec R t m hq).1 a _ hdom).continuousAt
      ((b66g_forms_spec R t m hq').1 a _ hdom).continuousAt (h a _ hdom)
    change q a ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2 =
      q' a ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2 at e
    rwa [(b66g_chart_slice R t a x hx).2] at e
  · rw [(b66g_forms_spec R t m hq).2.2 a x hx, (b66g_forms_spec R t m hq').2.2 a x hx]

theorem b66g_normalize_form (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ)
    (S : Finset R.C) (C : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (C a) z)
    (hnn : ∀ a z, z ∈ b66k_domain R t a → 0 ≤ meromorphicOrderAt (C a) z)
    (hlaw : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      C a (R.atlas.A a (t, x)).2 = b66k_vertical R t a b x ^ m * C b (R.atlas.A b (t, x)).2) :
    ∃ q ∈ b66g_forms R t m, ∀ a z, z ∈ b66k_domain R t a → b66g_coef R t q a z = b66g_nf (C a) z := by
  set q : b66g_Coeff R := fun a x =>
    if (t, x) ∈ (R.atlas.A a).source then b66g_nf (C a) (R.atlas.A a (t, x)).2 else 0
  have hcoef : ∀ a z, z ∈ b66k_domain R t a → b66g_coef R t q a z = b66g_nf (C a) z := by
    intro a z hz
    have hp := b66g_inv_point R t a z hz
    simp only [b66g_coef, q, ite_eq_left hp.1, hp.2]
  have hopen : ∀ a, IsOpen (b66k_domain R t a) := fun a =>
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  refine ⟨q, Submodule.subset_span ⟨fun a z hz => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩,
    hcoef⟩
  · apply (b66g_nf_analytic (hmero a z hz) (hnn a z hz)).congr
    filter_upwards [(hopen a).mem_nhds hz] with w hw
    exact (hcoef a w hw).symm
  · set z := (R.atlas.A a (t, x)).2
    have hz : z ∈ b66k_refinementDomain R t 1 a b :=
      b66g_refinement_point R t 1 a b x ha (by rwa [one_smul])
    obtain ⟨_, hTd, hTa, hDa⟩ := b66g_transition_mem R t a b z hz
    have hxz : ((R.atlas.A a).symm (t.val, z)).2 = x := (b66g_chart_slice R t a x ha).2
    have hTz : b66k_transition R a b (t.val, z) = (R.atlas.A b (t, x)).2 := by
      rw [b66g_trans_point R t a b z hz.1, hxz]
    have hDz : fderiv ℂ (b66k_transition R a b) (t.val, z) (0, 1) = b66k_vertical R t a b x := by
      rw [← b66g_vertical_eq_D R t a b z hz.1, hxz]
    have hFa := b66g_nf_analytic (hmero a z hz.1) (hnn a z hz.1)
    have hnb := b66g_nf_analytic (hmero b _ hTd) (hnn b _ hTd)
    have hFb : AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) ^ m *
        b66g_nf (C b) (b66k_transition R a b (t.val, w))) z :=
      (hDa.pow m).mul (AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) hnb hTa)
    have he := b66g_eq_of_nhdsNE hFa.continuousAt hFb.continuousAt (by
      filter_upwards [b66g_nf_eventually (hmero a z hz.1),
        (b66g_trans_tendsto R t a b z hz).eventually (b66g_nf_eventually (hmero b _ hTd)),
        b66g_avoid R t a z hz.1 S,
        nhdsWithin_le_nhds (b66g_overlap_eventually R t a b z hz)] with w h1 h2 h3 ⟨hmem, h4, h5⟩
      rw [h1, h2]
      have hl := hlaw a b _ h3 hmem.1 hmem.2
      rw [h4, h5] at hl
      rw [hl]
      unfold b66k_vertical
      rw [h4])
    simp only [q, ite_eq_left ha, ite_eq_left hb]
    rw [he, hDz, hTz]
  · simp only [q, ite_eq_right hx]

end B66gNormalForms
section B66gRiemannRochBridge

theorem b66g_chartPhiA (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (y : rf8_fibre R.C t) (a : b66k_Index R) (hya : y.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (fun τ => (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      (extChartAt 𝓘(ℂ, ℂ) y y + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 ∧
    deriv (fun τ => (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      (extChartAt 𝓘(ℂ, ℂ) y y + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 ≠ 0 ∧
    (fun τ => (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      (extChartAt 𝓘(ℂ, ℂ) y y + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) 0 =
      (R.atlas.A a y.val).2 := by
  set e := extChartAt 𝓘(ℂ, ℂ) y
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66g_slice R t a ∘ e.symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  obtain ⟨hhan, hhd, _⟩ := b66g_slice_chart R t a y y (mem_extChartAt_source y) hya
  have hs : HasDerivAt (fun σ : ℂ => e y + σ * c₀) c₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c₀).const_add (e y)
  have hsa : AnalyticAt ℂ (fun σ : ℂ => e y + σ * c₀) 0 := by fun_prop
  have hh0 : (fun σ : ℂ => e y + σ * c₀) 0 = e y := by simp
  have hhan' : AnalyticAt ℂ hh ((fun σ : ℂ => e y + σ * c₀) 0) := by
    rw [hh0]
    exact hhan
  refine ⟨AnalyticAt.comp (f := fun σ : ℂ => e y + σ * c₀) hhan' hsa, ?_, ?_⟩
  · change deriv (hh ∘ fun σ : ℂ => e y + σ * c₀) 0 ≠ 0
    rw [(hhan'.differentiableAt.hasDerivAt.comp 0 hs).deriv]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero hhd hc₀
  · simp only [hh, zero_mul, add_zero, Function.comp_apply,
      e.left_inv (mem_extChartAt_source y)]
    rfl

theorem b66g_centred_retained (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (H : rf8_fibre R.C t → ℂ) (y : rf8_fibre R.C t) (a : b66k_Index R)
    (hya : y.val ∈ (R.atlas.A a).source) :
    (fun τ => H ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y +
        b4cov_lineEquiv (Module.finrank_self ℂ) τ))) =ᶠ[𝓝 0]
      (fun w => H (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) ∘
        (fun τ => (b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
          (extChartAt 𝓘(ℂ, ℂ) y y + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) := by
  set e := extChartAt 𝓘(ℂ, ℂ) y
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  have hx₀e : y ∈ e.source := mem_extChartAt_source y
  have hex : e y ∈ e.target := e.map_source hx₀e
  have hsc : Tendsto (fun τ : ℂ => e y + τ * c₀) (𝓝 0) (𝓝 (e y)) := by
    have : Continuous (fun τ : ℂ => e y + τ * c₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e y + τ * c₀)) (𝓝 0) (𝓝 y) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  filter_upwards [hsymc.eventually ((b66g_open_source R t a).mem_nhds hya)] with τ hτ
  simp only [Function.comp_apply]
  rw [b66g_lineEquiv_apply τ, b66g_inv_slice R t a _ hτ]
  exact congrArg H (b66g_fibre_mk R t _).symm

theorem b66g_scalar_mero_order (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (H : rf8_fibre R.C t → ℂ) (y : rf8_fibre R.C t)
    (hmer : MeromorphicAt (fun τ => H ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y +
        b4cov_lineEquiv (Module.finrank_self ℂ) τ))) 0)
    (a : b66k_Index R) (hya : y.val ∈ (R.atlas.A a).source) :
    MeromorphicAt (fun w => H (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2))
        (R.atlas.A a y.val).2 ∧
      meromorphicOrderAt (fun w => H (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2))
        (R.atlas.A a y.val).2 =
      meromorphicOrderAt (fun τ => H ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y +
        b4cov_lineEquiv (Module.finrank_self ℂ) τ))) 0 := by
  obtain ⟨hΦ, hΦd, hΦ0⟩ := b66g_chartPhiA R t y a hya
  have he := b66g_centred_retained R t H y a hya
  rw [← hΦ0]
  refine ⟨(meromorphicAt_comp_iff_of_deriv_ne_zero hΦ hΦd).mp
    (hmer.congr (he.filter_mono nhdsWithin_le_nhds)), ?_⟩
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_comp_of_deriv_ne_zero hΦ hΦd]

theorem b66g_coef_order_chart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {m : ℕ}
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t m) (a : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_domain R t a) :
    meromorphicOrderAt (b66g_coef R t q a) z =
      meromorphicOrderAt (b66g_coef R t q (t, ((R.atlas.A a).symm (t.val, z)).2))
        (R.atlas.A (t, ((R.atlas.A a).symm (t.val, z)).2)
          (t, ((R.atlas.A a).symm (t.val, z)).2)).2 := by
  set x := ((R.atlas.A a).symm (t.val, z)).2
  set c : b66k_Index R := (t, x)
  have hc : (t, x) ∈ (R.atlas.A c).source := (R.atlas.hA c).1
  have hxa := (b66g_inv_point R t a z hz).1
  have hz' : z ∈ b66k_refinementDomain R t 1 a c := ⟨hz, by rw [one_smul]; exact hc⟩
  obtain ⟨hTm, hTd, hTa, hDa⟩ := b66g_transition_mem R t a c z hz'
  have hopen : IsOpen (b66k_domain R t a) :=
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  have hev : b66g_coef R t q a =ᶠ[𝓝 z] fun w =>
      fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1) ^ m *
        b66g_coef R t q c (b66k_transition R a c (t.val, w)) := by
    filter_upwards [b66g_overlap_eventually R t a c z hz', hopen.mem_nhds hz] with w ⟨hmem, _, _⟩ hw
    simp only [b66g_coef]
    rw [(b66g_trans_inv R t a c w hw hmem.2).2, ← b66g_vertical_eq_D R t a c w hw]
    exact (b66g_forms_spec R t m hq).2.1 a c _ hmem.1 hmem.2
  have hD0 : fderiv ℂ (b66k_transition R a c) (t.val, z) (0, 1) ≠ 0 := by
    rw [← b66g_vertical_eq_D R t a c z hz]
    exact b66g_vertical_ne R t a c x hxa hc
  have hTd' : deriv (fun w => b66k_transition R a c (t.val, w)) z ≠ 0 := by
    rw [(b66g_transition_hasDerivAt R t a c z hTm).deriv]
    exact hD0
  have hDm : AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1) ^ m) z :=
    hDa.pow m
  rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds),
    show (fun w => fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1) ^ m *
        b66g_coef R t q c (b66k_transition R a c (t.val, w))) =
      (fun w => fderiv ℂ (b66k_transition R a c) (t.val, w) (0, 1) ^ m) *
        (b66g_coef R t q c ∘ fun w => b66k_transition R a c (t.val, w)) from rfl,
    meromorphicOrderAt_mul_of_ne_zero hDm (pow_ne_zero m hD0),
    meromorphicOrderAt_comp_of_deriv_ne_zero hTa hTd', b66g_trans_point R t a c z hz]

theorem b66g_divForm_apply (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)
    (hfin : (Function.support (b4c_ordForm (hE := Module.finrank_self ℂ) w)).Finite)
    (y : rf8_fibre R.C t) :
    b4c_divForm (hE := Module.finrank_self ℂ) w y = b4c_ordForm (hE := Module.finrank_self ℂ) w y := by
  unfold b4c_divForm
  simp only [hfin, ↓reduceDIte]
  rfl

/-- Quadratic coefficients `f · q₀²` of a Riemann–Roch section. -/
def b66g_rrCoef (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q₀ : b66g_Coeff R)
    (D : rf8_fibre R.C t →₀ ℤ) (g : b4c_L (E := ℂ) D) (a : b66k_Index R) (z : ℂ) : ℂ :=
  RiemannRochAna_L_scalarLinear D g (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2) *
    b66g_coef R t q₀ a z ^ 2

theorem b66g_ordForm_toForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1) (y : rf8_fibre R.C t) :
    b4c_ordForm (hE := Module.finrank_self ℂ) (b66g_toForm R t q₀) y = b66g_ord R t q₀ y := by
  change (meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_self ℂ)
    (b66g_toForm R t q₀) y) 0).untop₀ = _
  rw [← b66g_cform_coef, b66g_cform_order R t ∅ _ (b66g_coef_law R t hq₀) y]
  rfl

theorem b66g_toForm_mero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1) :
    b4c_IsMeroForm (Module.finrank_self ℂ) (b66g_toForm R t q₀) := by
  rw [← b66g_cform_coef]
  exact b66g_cform_mero R t ∅ _ (fun a z hz => ((b66g_forms_spec R t 1 hq₀).1 a z hz).meromorphicAt)
    (b66g_coef_law R t hq₀)

theorem b66g_rrCoef_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0)
    (D : rf8_fibre R.C t →₀ ℤ) (hD : ∀ y, D y = 2 * b66g_ord R t q₀ y)
    (g : b4c_L (E := ℂ) D) (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a) :
    MeromorphicAt (b66g_rrCoef R t q₀ D g a) z ∧
      0 ≤ meromorphicOrderAt (b66g_rrCoef R t q₀ D g a) z := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hp := b66g_inv_point R t a z hz
  have hya : (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A a).source := hp.1
  have hyz : (R.atlas.A a (b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2).val).2 = z := by
    change (R.atlas.A a (t, ((R.atlas.A a).symm (t.val, z)).2)).2 = z
    rw [hp.2]
  set y := b66g_pt R t ((R.atlas.A a).symm (t.val, z)).2
  obtain ⟨hm, hord⟩ := b66g_scalar_mero_order R t (RiemannRochAna_L_scalarLinear D g) y
    (RiemannRochAna_L_scalar_meromorphic hE D g y) a hya
  have hbound := RiemannRochAna_L_scalar_order_bound hE D g y
  rw [hyz] at hm hord
  have hQ := (b66g_forms_spec R t 1 hq₀).1 a z hz
  have hQord : meromorphicOrderAt (b66g_coef R t q₀ a) z = (b66g_ord R t q₀ y : WithTop ℤ) := by
    rw [b66g_coef_order_chart R t hq₀ a z hz]
    exact b66g_ord_eq R t hq₀ hq₀0 y
  have hprod : b66g_rrCoef R t q₀ D g a = (fun w => RiemannRochAna_L_scalarLinear D g
      (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) * b66g_coef R t q₀ a ^ 2 := by
    funext w
    simp only [b66g_rrCoef, Pi.mul_apply, Pi.pow_apply]
  have hQm : MeromorphicAt (b66g_coef R t q₀ a) z := hQ.meromorphicAt
  rw [hprod]
  refine ⟨hm.mul (hQm.pow 2), ?_⟩
  rw [meromorphicOrderAt_mul hm (hQm.pow 2), meromorphicOrderAt_pow hQm, hQord, hord]
  rw [hD y] at hbound
  rcases eq_or_ne (meromorphicOrderAt (fun τ => RiemannRochAna_L_scalarLinear D g
      ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y +
        b4cov_lineEquiv (Module.finrank_self ℂ) τ))) 0) ⊤ with htop | htop
  · rw [htop, WithTop.top_add]
    exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hn] at hbound ⊢
    have h1 : -(2 * b66g_ord R t q₀ y) ≤ n := by exact_mod_cast hbound
    have h2 : ((2 : ℕ) : WithTop ℤ) * (b66g_ord R t q₀ y : WithTop ℤ) =
        ((2 * b66g_ord R t q₀ y : ℤ) : WithTop ℤ) := by norm_cast
    rw [h2, ← WithTop.coe_add]
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + 2 * b66g_ord R t q₀ y)

theorem b66g_rrCoef_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1)
    (D : rf8_fibre R.C t →₀ ℤ) (g : b4c_L (E := ℂ) D) :
    ∀ a b x, x ∉ (∅ : Finset R.C) → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66g_rrCoef R t q₀ D g a (R.atlas.A a (t, x)).2 =
        b66k_vertical R t a b x ^ 2 * b66g_rrCoef R t q₀ D g b (R.atlas.A b (t, x)).2 := by
  intro a b x _ ha hb
  simp only [b66g_rrCoef, b66g_coef]
  rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
    (b66g_forms_spec R t 1 hq₀).2.1 a b x ha hb, pow_one]
  ring

theorem b66g_zero_off_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (H : rf8_fibre R.C t → ℂ) (h : ∀ y, ∀ᶠ y' in 𝓝[≠] y, H y' = 0) :
    ∃ F : Finset (rf8_fibre R.C t), ∀ y, y ∉ F → H y = 0 := by
  have h' : ∀ y, ∃ W ∈ 𝓝 y, ∀ y' ∈ W, y' ≠ y → H y' = 0 := by
    intro y
    have := eventually_nhdsWithin_iff.mp (h y)
    exact ⟨_, this, fun y' hy' hne => hy' hne⟩
  choose W hW hz using h'
  obtain ⟨T, hT⟩ := isCompact_univ.elim_nhds_subcover W (fun y _ => hW y)
  refine ⟨T, fun y hy => ?_⟩
  obtain ⟨y₁, hy₁, hyW⟩ := mem_iUnion₂.mp (hT.2 (mem_univ y))
  exact hz y₁ y hyW (fun h => hy (h ▸ hy₁))

theorem b66g_rr_map (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0)
    (D : rf8_fibre R.C t →₀ ℤ) (hD : ∀ y, D y = 2 * b66g_ord R t q₀ y) :
    ∃ Ψ : b4c_L (E := ℂ) D →ₗ[ℂ] b66g_forms R t 2, Function.Injective Ψ := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hn : ∀ g : b4c_L (E := ℂ) D, ∃ q ∈ b66g_forms R t 2, ∀ a z, z ∈ b66k_domain R t a →
      b66g_coef R t q a z = b66g_nf (b66g_rrCoef R t q₀ D g a) z := fun g =>
    b66g_normalize_form R t 2 ∅ _ (fun a z hz => (b66g_rrCoef_spec R t hq₀ hq₀0 D hD g a z hz).1)
      (fun a z hz => (b66g_rrCoef_spec R t hq₀ hq₀0 D hD g a z hz).2) (b66g_rrCoef_law R t hq₀ D g)
  choose Q hQm hQc using hn
  have hopen : ∀ a, IsOpen (b66k_domain R t a) := fun a =>
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  have hloc : ∀ g a z, z ∈ b66k_domain R t a →
      b66g_coef R t (Q g) a =ᶠ[𝓝[≠] z] b66g_rrCoef R t q₀ D g a := by
    intro g a z hz
    filter_upwards [nhdsWithin_le_nhds ((hopen a).mem_nhds hz),
      b66g_nf_eventually (b66g_rrCoef_spec R t hq₀ hq₀0 D hD g a z hz).1] with w hw h2
    rw [hQc g a w hw, h2]
  refine ⟨⟨⟨fun g => ⟨Q g, hQm g⟩, fun g g' => ?_⟩, fun c g => ?_⟩, fun g g' hgg => ?_⟩
  · apply Subtype.ext
    apply b66g_forms_ext R t (hQm (g + g')) (add_mem (hQm g) (hQm g'))
    intro a z hz
    filter_upwards [hloc (g + g') a z hz, hloc g a z hz, hloc g' a z hz] with w h1 h2 h3
    change _ = b66g_coef R t (Q g) a w + b66g_coef R t (Q g') a w
    rw [h1, h2, h3]
    simp only [b66g_rrCoef, map_add, Pi.add_apply]
    ring
  · apply Subtype.ext
    apply b66g_forms_ext R t (hQm (c • g)) (Submodule.smul_mem _ c (hQm g))
    intro a z hz
    filter_upwards [hloc (c • g) a z hz, hloc g a z hz] with w h1 h2
    change _ = c * b66g_coef R t (Q g) a w
    rw [h1, h2]
    simp only [b66g_rrCoef, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · have hQeq : Q g = Q g' := congrArg Subtype.val hgg
    set H := RiemannRochAna_L_scalarLinear D (g - g')
    have hval : ∀ a z, z ∈ b66k_domain R t a →
        ∀ᶠ w in 𝓝[≠] z, H (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) = 0 := by
      intro a z hz
      have hQ := (b66g_forms_spec R t 1 hq₀).1 a z hz
      have hne : ∀ᶠ w in 𝓝[≠] z, b66g_coef R t q₀ a w ≠ 0 := by
        rcases hQ.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
        · exfalso
          have htop : meromorphicOrderAt (b66g_coef R t q₀ a) z = ⊤ :=
            meromorphicOrderAt_eq_top_iff.mpr (h0.filter_mono nhdsWithin_le_nhds)
          rw [b66g_coef_order_chart R t hq₀ a z hz] at htop
          exact b66g_coef_order_ne_top R t hq₀ hq₀0 _ htop
        · exact h0
      filter_upwards [hloc g a z hz, hloc g' a z hz, hne] with w h1 h2 h3
      have h4 : b66g_coef R t (Q g) a w = b66g_coef R t (Q g') a w := by rw [hQeq]
      rw [h1, h2] at h4
      simp only [b66g_rrCoef] at h4
      have h5 : (RiemannRochAna_L_scalarLinear D g (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2) -
          RiemannRochAna_L_scalarLinear D g' (b66g_pt R t ((R.atlas.A a).symm (t.val, w)).2)) *
          b66g_coef R t q₀ a w ^ 2 = 0 := by rw [sub_mul, h4, sub_self]
      have h6 := (mul_eq_zero.mp h5).resolve_right (pow_ne_zero 2 h3)
      simp only [H, map_sub]
      exact sub_eq_zero.mpr (sub_eq_zero.mp h6)
    have hglob : ∀ y, ∀ᶠ y' in 𝓝[≠] y, H y' = 0 := by
      intro y
      set a := y.val
      have ha : y.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
      have hz := b66g_slice_domain R t a y ha
      have hcont := (b66g_slice_contMDiffAt R t a y ha).continuousAt
      have htend : Tendsto (b66g_slice R t a) (𝓝[≠] y) (𝓝[≠] (b66g_slice R t a y)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds ((b66g_open_source R t a).mem_nhds ha),
            self_mem_nhdsWithin] with y' hy' hne heq
          apply hne
          apply Subtype.ext
          apply (R.atlas.A a).injOn hy' ha
          rw [b66g_slice_value R t a y' hy', b66g_slice_value R t a y ha]
          exact congrArg (fun z => (t.val, z)) heq
      filter_upwards [htend.eventually (hval a _ hz),
        nhdsWithin_le_nhds ((b66g_open_source R t a).mem_nhds ha)] with y' h1 h2
      rw [b66g_inv_slice R t a y' h2] at h1
      have hpt : b66g_pt R t y'.val.2 = y' := b66g_fibre_mk R t y'
      rwa [hpt] at h1
    obtain ⟨F, hF⟩ := b66g_zero_off_finite R t H hglob
    have hsub : D.support ⊆ F ∪ D.support := Finset.subset_union_right
    have hinj := RiemannRochAna_L_restrictOffFinset_injective hE D (F ∪ D.support) hsub
    have hzero : RiemannRochAna_L_restrictOffFinset D (F ∪ D.support) hsub (g - g') = 0 := by
      funext x
      obtain ⟨x, hx⟩ := x
      have hxF : x ∉ F := fun h => hx (Finset.mem_union_left _ h)
      have hxD : x ∉ D.support := fun h => hx (Finset.mem_union_right _ h)
      have := hF x hxF
      simp only [H, RiemannRochAna_L_scalarLinear, LinearMap.coe_mk, AddHom.coe_mk] at this
      change (g - g').1 ⟨x, hxD⟩ = 0
      simpa [hxD] using this
    have := hinj (hzero.trans (map_zero _).symm)
    exact sub_eq_zero.mp this

theorem b66g_forms_two_finrank (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    3 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 3 ≤
      Module.finrank ℂ (b66g_forms R t 2) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  obtain ⟨q₀, hq₀, hq₀0⟩ := b66g_form_exists R t
  let w : b4c_MeroForm ℂ (rf8_fibre R.C t) hE := ⟨b66g_toForm R t q₀, b66g_toForm_mero R t hq₀⟩
  have hfin := b4c_meroForm_orderSupport_finite hE w
  set D := b4c_divForm (hE := hE) (b66g_toForm R t q₀) + b4c_divForm (hE := hE) (b66g_toForm R t q₀)
  have hD : ∀ y, D y = 2 * b66g_ord R t q₀ y := by
    intro y
    simp only [D, Finsupp.add_apply]
    rw [b66g_divForm_apply R t _ hfin y, b66g_ordForm_toForm R t hq₀ y]
    ring
  obtain ⟨Ψ, hΨ⟩ := b66g_rr_map R t hq₀ hq₀0 D hD
  have : FiniteDimensional ℂ (b66g_forms R t 2) := b66g_forms_two_finite R t
  have hle := LinearMap.finrank_le_finrank_of_injective hΨ
  obtain ⟨y⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  have hgw : meromorphicOrderAt (HurwitzPrymRR_loc hE w y) 0 ≠ ⊤ := by
    change meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_toForm R t q₀) y) 0 ≠ ⊤
    rw [← b66g_cform_coef, b66g_cform_order R t ∅ _ (b66g_coef_law R t hq₀) y,
      b66g_ord_eq R t hq₀ hq₀0 y]
    exact WithTop.coe_ne_top
  have hw : (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) ≠ 0 := by
    intro h
    apply hgw
    rw [h]
    exact meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun _ => rfl)
  have hrr := b4c_riemannRoch hE D w hw ⟨y, hgw⟩
  have hcan := b4c_deg_canonical hE w hw ⟨y, hgw⟩
  have hdeg : b4c_deg D = 2 * b4c_deg (b4c_divForm (hE := hE) (b66g_toForm R t q₀)) := by
    unfold b4c_deg
    simp only [D]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    ring
  change b4c_deg (b4c_divForm (hE := hE) (b66g_toForm R t q₀)) = _ at hcan
  rw [hdeg, hcan] at hrr
  have h0 : (0 : ℤ) ≤ Module.finrank ℂ
      (b4c_L (E := ℂ) (b4c_divForm (hE := hE) (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) - D)) :=
    Nat.cast_nonneg _
  have hle' : (Module.finrank ℂ (b4c_L (E := ℂ) D) : ℤ) ≤ Module.finrank ℂ (b66g_forms R t 2) := by
    exact_mod_cast hle
  linarith

end B66gRiemannRochBridge
section B66gSerreInjective

theorem b66g_order_nonneg_of_residues {r : ℂ → ℂ} {ζ : ℂ} (k : ℕ) (hr : MeromorphicAt r ζ)
    (hk : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt r ζ)
    (hres : ∀ i < k, TauCeti.Contour.residue (fun w => (w - ζ) ^ i * r w) ζ = 0) :
    0 ≤ meromorphicOrderAt r ζ := by
  by_contra hneg
  push Not at hneg
  have hne : meromorphicOrderAt r ζ ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hn] at hneg hk
  have hn0 : n < 0 := by exact_mod_cast hneg
  have hnk : -(k : ℤ) ≤ n := by exact_mod_cast hk
  set i := (-n - 1).toNat
  have hi : (i : ℤ) = -n - 1 := Int.toNat_of_nonneg (by omega)
  have hik : i < k := by omega
  have hpow : MeromorphicAt (fun w => (w - ζ) ^ i) ζ := by fun_prop
  have hord : meromorphicOrderAt (fun w => (w - ζ) ^ i * r w) ζ = -1 := by
    rw [fun_meromorphicOrderAt_mul hpow hr, ← hn]
    have : meromorphicOrderAt (fun w => (w - ζ) ^ i) ζ = (i : WithTop ℤ) :=
      meromorphicOrderAt_pow_id_sub_const (x := ζ) (n := i)
    rw [this]
    have h2 : ((i : ℕ) : WithTop ℤ) + (n : WithTop ℤ) = ((i + n : ℤ) : WithTop ℤ) := by norm_cast
    rw [h2]
    have : (i : ℤ) + n = -1 := by omega
    rw [this]
    rfl
  have h0 := hres i hik
  rw [TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord] at h0
  have hm : MeromorphicAt (fun w => (w - ζ) ^ i * r w) ζ := hpow.mul hr
  exact hm.meromorphicTrailingCoeffAt_ne_zero (by rw [hord]; decide) h0

/-- Jet orders along a finite set containing the zeros of a one-form. -/
def b66g_k (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q₀ : b66g_Coeff R) (x : R.C) : ℕ :=
  (b66g_ord R t q₀ (b66g_pt R t x)).toNat

/-- Centre of the own chart of a point. -/
def b66g_ζ (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x : R.C) : ℂ :=
  (R.atlas.A (t, x) (t, x)).2

theorem b66g_ratio_mero (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) (x : R.C) :
    MeromorphicAt (fun w => b66g_coef R t q (t, x) w / b66g_coef R t q₀ (t, x) w) (b66g_ζ R t x) :=
  (b66g_coef_analytic R t hq x).meromorphicAt.div (b66g_coef_analytic R t hq₀ x).meromorphicAt

/-- Residue pairing of jets along `T` with quadratic differentials divided by `q₀`. -/
def b66g_beta (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (T : Finset R.C) :
    ((x : T) → Fin (b66g_k R t q₀ x.1) → ℂ) →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2) :=
  LinearMap.mk₂ ℂ (fun j q => ∑ x : T, ∑ i, j x i * TauCeti.Contour.residue (fun w =>
      (w - b66g_ζ R t x.1) ^ (i : ℕ) * (b66g_coef R t q.val (t, x.1) w /
        b66g_coef R t q₀ (t, x.1) w)) (b66g_ζ R t x.1))
    (fun j j' q => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c j q => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun j q r => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hp : MeromorphicAt (fun w => (w - b66g_ζ R t x.1) ^ (i : ℕ)) (b66g_ζ R t x.1) := by
        fun_prop
      have h1 : MeromorphicAt (fun w => (w - b66g_ζ R t x.1) ^ (i : ℕ) *
          (b66g_coef R t q.val (t, x.1) w / b66g_coef R t q₀ (t, x.1) w)) (b66g_ζ R t x.1) :=
        hp.mul (b66g_ratio_mero R t hq₀ q.property x.1)
      have h2 : MeromorphicAt (fun w => (w - b66g_ζ R t x.1) ^ (i : ℕ) *
          (b66g_coef R t r.val (t, x.1) w / b66g_coef R t q₀ (t, x.1) w)) (b66g_ζ R t x.1) :=
        hp.mul (b66g_ratio_mero R t hq₀ r.property x.1)
      rw [← mul_add, ← TauCeti.Contour.residue_add h1 h2]
      congr 2
      funext w
      simp only [b66g_coef, Submodule.coe_add, Pi.add_apply]
      ring)
    (fun c j q => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hf : (fun w => (w - b66g_ζ R t x.1) ^ (i : ℕ) * (b66g_coef R t (c • q).val (t, x.1) w /
          b66g_coef R t q₀ (t, x.1) w)) = fun w => c * ((w - b66g_ζ R t x.1) ^ (i : ℕ) *
          (b66g_coef R t q.val (t, x.1) w / b66g_coef R t q₀ (t, x.1) w)) := by
        funext w
        simp only [b66g_coef, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hf, TauCeti.Contour.residue_const_mul]
      ring)

theorem b66g_beta_single (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (T : Finset R.C) (x : T) (i : Fin (b66g_k R t q₀ x.1))
    (q : b66g_forms R t 2) :
    b66g_beta R t hq₀ T (Pi.single x (Pi.single i 1)) q = TauCeti.Contour.residue (fun w =>
      (w - b66g_ζ R t x.1) ^ (i : ℕ) * (b66g_coef R t q.val (t, x.1) w /
        b66g_coef R t q₀ (t, x.1) w)) (b66g_ζ R t x.1) := by
  classical
  simp only [b66g_beta, LinearMap.mk₂_apply]
  rw [Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul]
    · intro m _ hm
      rw [Pi.single_eq_of_ne hm, zero_mul]
    · simp
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy]
    simp
  · simp

theorem b66g_coef_at_ζ (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q : b66g_Coeff R)
    (x : R.C) : b66g_coef R t q (t, x) (b66g_ζ R t x) = q (t, x) x :=
  congrArg (q (t, x)) (b66g_chart_slice R t (t, x) x (R.atlas.hA _).1).2

theorem b66g_betaT_order (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (T : Finset R.C)
    (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T) {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2)
    (hq0 : q ≠ 0) (hker : ∀ j, b66g_beta R t hq₀ T j ⟨q, hq⟩ = 0) (y : rf8_fibre R.C t) :
    b66g_ord R t q₀ y ≤ b66g_ord R t q y := by
  have hy : y = b66g_pt R t y.val.2 := (b66g_fibre_mk R t y).symm
  rw [hy]
  set x := y.val.2
  have h0 := b66g_ord_nonneg R t hq₀ hq₀0 (b66g_pt R t x)
  have h1 := b66g_ord_nonneg R t hq hq0 (b66g_pt R t x)
  by_cases hx : x ∈ T
  · have hres : ∀ i < b66g_k R t q₀ x, TauCeti.Contour.residue (fun w =>
        (w - b66g_ζ R t x) ^ i * (b66g_coef R t q (t, x) w / b66g_coef R t q₀ (t, x) w))
        (b66g_ζ R t x) = 0 := by
      intro i hi
      have := hker (Pi.single ⟨x, hx⟩ (Pi.single ⟨i, hi⟩ 1))
      rwa [b66g_beta_single R t hq₀ T ⟨x, hx⟩ ⟨i, hi⟩ ⟨q, hq⟩] at this
    have hr := b66g_ratio_mero R t hq₀ hq x
    have hordr : meromorphicOrderAt (fun w => b66g_coef R t q (t, x) w /
        b66g_coef R t q₀ (t, x) w) (b66g_ζ R t x) =
        ((b66g_ord R t q (b66g_pt R t x) - b66g_ord R t q₀ (b66g_pt R t x) : ℤ) : WithTop ℤ) := by
      unfold b66g_ζ
      rw [fun_meromorphicOrderAt_div (b66g_coef_analytic R t hq x).meromorphicAt
        (b66g_coef_analytic R t hq₀ x).meromorphicAt]
      have e1 : meromorphicOrderAt (b66g_coef R t q (t, x)) (R.atlas.A (t, x) (t, x)).2 =
          (b66g_ord R t q (b66g_pt R t x) : WithTop ℤ) := b66g_ord_eq R t hq hq0 (b66g_pt R t x)
      have e2 : meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (R.atlas.A (t, x) (t, x)).2 =
          (b66g_ord R t q₀ (b66g_pt R t x) : WithTop ℤ) := b66g_ord_eq R t hq₀ hq₀0 (b66g_pt R t x)
      rw [e1, e2]
      rfl
    have hk : ((b66g_k R t q₀ x : ℕ) : ℤ) = b66g_ord R t q₀ (b66g_pt R t x) :=
      Int.toNat_of_nonneg h0
    have hnn := b66g_order_nonneg_of_residues (b66g_k R t q₀ x) hr (by
      rw [hordr]
      exact_mod_cast (by omega : -((b66g_k R t q₀ x : ℕ) : ℤ) ≤
        b66g_ord R t q (b66g_pt R t x) - b66g_ord R t q₀ (b66g_pt R t x))) hres
    rw [hordr] at hnn
    have : (0 : ℤ) ≤ b66g_ord R t q (b66g_pt R t x) - b66g_ord R t q₀ (b66g_pt R t x) := by
      exact_mod_cast hnn
    omega
  · have hne : b66g_coef R t q₀ (t, x) (b66g_ζ R t x) ≠ 0 := by
      rw [b66g_coef_at_ζ]
      exact fun h => hx (hT x h)
    have hz : meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (b66g_ζ R t x) = 0 := by
      unfold b66g_ζ at hne ⊢
      rw [(b66g_coef_analytic R t hq₀ x).meromorphicOrderAt_eq,
        (b66g_coef_analytic R t hq₀ x).analyticOrderAt_eq_zero.mpr hne]
      rfl
    have := b66g_ord_eq R t hq₀ hq₀0 (b66g_pt R t x)
    change meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (b66g_ζ R t x) = _ at this
    rw [hz] at this
    have h2 : b66g_ord R t q₀ (b66g_pt R t x) = 0 := by exact_mod_cast this.symm
    omega

theorem b66g_ratio_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (T : Finset R.C) (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T)
    {q : b66g_Coeff R} (hq : q ∈ b66g_forms R t 2) :
    ∀ a b x, x ∉ T → (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
      (fun a z => b66g_coef R t q a z / b66g_coef R t q₀ a z) a (R.atlas.A a (t, x)).2 =
        b66k_vertical R t a b x *
          (fun a z => b66g_coef R t q a z / b66g_coef R t q₀ a z) b (R.atlas.A b (t, x)).2 := by
  intro a b x hx ha hb
  have hnz : q₀ b x ≠ 0 := fun hz =>
    hx (hT x ((b66g_form_zero_iff R t hq₀ b (b66g_pt R t x) hb).mp hz))
  simp only [b66g_coef]
  rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2,
    (b66g_forms_spec R t 2 hq).2.1 a b x ha hb, (b66g_forms_spec R t 1 hq₀).2.1 a b x ha hb, pow_one]
  have h2 := b66g_vertical_ne R t a b x ha hb
  field_simp

theorem b66g_betaT_finrank (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (T : Finset R.C)
    (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T) :
    Module.finrank ℂ (LinearMap.ker (b66g_beta R t hq₀ T).flip) ≤
      Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  set V := LinearMap.ker (b66g_beta R t hq₀ T).flip
  let F : V →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) :=
    ⟨⟨fun v => b66g_cform R t (fun a z => b66g_coef R t v.1.1 a z / b66g_coef R t q₀ a z),
      fun v w => by
        funext p
        simp only [b66g_cform, b66g_coef, Submodule.coe_add, Pi.add_apply]
        ring⟩, fun c v => by
        funext p
        simp only [b66g_cform, b66g_coef, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring⟩
  have hmeroC : ∀ v : V, ∀ a z, z ∈ b66k_domain R t a →
      MeromorphicAt ((fun a z => b66g_coef R t v.1.1 a z / b66g_coef R t q₀ a z) a) z :=
    fun v a z hz => ((b66g_forms_spec R t 2 v.1.2).1 a z hz).meromorphicAt.div
      ((b66g_forms_spec R t 1 hq₀).1 a z hz).meromorphicAt
  have hF : ∀ v, b4c_IsMeroForm hE (F v) := fun v =>
    b66g_cform_mero R t T _ (hmeroC v) (b66g_ratio_law R t hq₀ T hT v.1.2)
  have hord : ∀ (v : V) (p : rf8_fibre R.C t),
      meromorphicOrderAt (HurwitzPrymRR_loc hE (F v) p) 0 =
        meromorphicOrderAt (fun z => b66g_coef R t v.1.1 p.val z / b66g_coef R t q₀ p.val z)
          (R.atlas.A p.val p.val).2 := fun v p =>
    b66g_cform_order R t T _ (b66g_ratio_law R t hq₀ T hT v.1.2) p
  have hker : ∀ v : V, ∀ j, b66g_beta R t hq₀ T j v.1 = 0 := by
    intro v j
    have h := LinearMap.mem_ker.mp v.2
    have := LinearMap.congr_fun h j
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
  apply RiemannRochEichler_no_poles_finrank_le hE F hF
  · intro v p
    rw [hord v p]
    by_cases hv : v.1.1 = 0
    · have h0 : (fun z => b66g_coef R t v.1.1 p.val z / b66g_coef R t q₀ p.val z) = 0 := by
        funext z
        simp [b66g_coef, hv]
      rw [h0]
      exact le_of_le_of_eq le_top
        (meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun _ => rfl)).symm
    · rw [fun_meromorphicOrderAt_div (b66g_coef_analytic' R t v.1.2 p).meromorphicAt
        (b66g_coef_analytic' R t hq₀ p).meromorphicAt, b66g_ord_eq R t v.1.2 hv p,
        b66g_ord_eq R t hq₀ hq₀0 p]
      have := b66g_betaT_order R t hq₀ hq₀0 T hT v.1.2 hv (hker v) p
      exact_mod_cast (by omega : (0 : ℤ) ≤ b66g_ord R t v.1.1 p - b66g_ord R t q₀ p)
  · intro v hv0
    by_contra hne
    have hv : v.1.1 ≠ 0 := fun h => hne (Subtype.ext (Subtype.ext h))
    obtain ⟨p⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
    have htop : meromorphicOrderAt (HurwitzPrymRR_loc hE (F v) p) 0 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (hv0 p)
    rw [hord v p, fun_meromorphicOrderAt_div (b66g_coef_analytic' R t v.1.2 p).meromorphicAt
      (b66g_coef_analytic' R t hq₀ p).meromorphicAt, b66g_ord_eq R t v.1.2 hv p,
      b66g_ord_eq R t hq₀ hq₀0 p] at htop
    exact WithTop.coe_ne_top (a := b66g_ord R t v.1.1 p - b66g_ord R t q₀ p) htop

theorem b66g_ord_zero_of_ne (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    {q₀ : b66g_Coeff R} (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (x : R.C)
    (h : q₀ (t, x) x ≠ 0) : b66g_ord R t q₀ (b66g_pt R t x) = 0 := by
  have hne : b66g_coef R t q₀ (t, x) (b66g_ζ R t x) ≠ 0 := by rwa [b66g_coef_at_ζ]
  unfold b66g_ζ at hne
  have hz : meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (R.atlas.A (t, x) (t, x)).2 = 0 := by
    rw [(b66g_coef_analytic R t hq₀ x).meromorphicOrderAt_eq,
      (b66g_coef_analytic R t hq₀ x).analyticOrderAt_eq_zero.mpr hne]
    rfl
  have := b66g_ord_eq R t hq₀ hq₀0 (b66g_pt R t x)
  change meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (R.atlas.A (t, x) (t, x)).2 = _ at this
  rw [hz] at this
  exact_mod_cast this.symm

theorem b66g_sum_k (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (T : Finset R.C)
    (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T) :
    ∑ x ∈ T, (b66g_k R t q₀ x : ℤ) =
      2 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 2 := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  let w : b4c_MeroForm ℂ (rf8_fibre R.C t) hE := ⟨b66g_toForm R t q₀, b66g_toForm_mero R t hq₀⟩
  have hfin := b4c_meroForm_orderSupport_finite hE w
  obtain ⟨y⟩ : Nonempty (rf8_fibre R.C t) := inferInstance
  have hgw : meromorphicOrderAt (HurwitzPrymRR_loc hE w y) 0 ≠ ⊤ := by
    change meromorphicOrderAt (HurwitzPrymRR_loc hE (b66g_toForm R t q₀) y) 0 ≠ ⊤
    rw [← b66g_cform_coef, b66g_cform_order R t ∅ _ (b66g_coef_law R t hq₀) y,
      b66g_ord_eq R t hq₀ hq₀0 y]
    exact WithTop.coe_ne_top
  have hw : (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ) ≠ 0 := by
    intro h
    apply hgw
    rw [h]
    exact meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.of_forall fun _ => rfl)
  have hcan := b4c_deg_canonical hE w hw ⟨y, hgw⟩
  have hsupp : Function.support (b4c_ordForm (hE := hE)
      (w : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ)) ⊆ ↑(T.map (b66g_pt R t)) := by
    intro p hp
    have hp' : b66g_ord R t q₀ p ≠ 0 := by
      rwa [Function.mem_support, show b4c_ordForm (hE := hE) (w : TangentBundle 𝓘(ℂ, ℂ)
        (rf8_fibre R.C t) → ℂ) p = b66g_ord R t q₀ p from b66g_ordForm_toForm R t hq₀ p] at hp
    have hpt : b66g_pt R t p.val.2 = p := b66g_fibre_mk R t p
    refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨p.val.2, ?_, hpt⟩)
    by_contra hx
    apply hp'
    rw [← hpt]
    exact b66g_ord_zero_of_ne R t hq₀ hq₀0 p.val.2 (fun h => hx (hT _ h))
  rw [b66g_deg_eq_sum R t _ hfin _ hsupp, Finset.sum_map] at hcan
  rw [← hcan]
  refine Finset.sum_congr rfl fun x _ => ?_
  change ((b66g_ord R t q₀ (b66g_pt R t x)).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (b66g_ord_nonneg R t hq₀ hq₀0 _)]
  exact (b66g_ordForm_toForm R t hq₀ _).symm

/-- The jet of the constant function one. -/
def b66g_j1 (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (q₀ : b66g_Coeff R)
    (T : Finset R.C) : (x : T) → Fin (b66g_k R t q₀ x.1) → ℂ :=
  fun _ i => if (i : ℕ) = 0 then 1 else 0

theorem b66g_beta_j1 (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (T : Finset R.C)
    (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T) (q : b66g_forms R t 2) :
    b66g_beta R t hq₀ T (b66g_j1 R t q₀ T) q = 0 := by
  have hterm : ∀ x : T, ∑ i : Fin (b66g_k R t q₀ x.1), b66g_j1 R t q₀ T x i *
      TauCeti.Contour.residue (fun w => (w - b66g_ζ R t x.1) ^ (i : ℕ) *
        (b66g_coef R t q.val (t, x.1) w / b66g_coef R t q₀ (t, x.1) w)) (b66g_ζ R t x.1) =
      TauCeti.Contour.residue (fun w => b66g_coef R t q.val (t, x.1) w /
        b66g_coef R t q₀ (t, x.1) w) (b66g_ζ R t x.1) := by
    intro x
    by_cases hk : 0 < b66g_k R t q₀ x.1
    · rw [Finset.sum_eq_single ⟨0, hk⟩]
      · simp only [b66g_j1, ite_true, one_mul, pow_zero]
      · intro i _ hi
        have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        simp [b66g_j1, this]
      · simp
    · have hk0 : b66g_k R t q₀ x.1 = 0 := by omega
      rw [Finset.sum_eq_zero (fun i _ => absurd i.2 (by omega))]
      symm
      apply TauCeti.Contour.residue_eq_zero_of_analyticAt
      have hord : b66g_ord R t q₀ (b66g_pt R t x.1) = 0 := by
        have h0 := b66g_ord_nonneg R t hq₀ hq₀0 (b66g_pt R t x.1)
        unfold b66g_k at hk0
        omega
      have hne : b66g_coef R t q₀ (t, x.1) (b66g_ζ R t x.1) ≠ 0 := by
        have han := b66g_coef_analytic R t hq₀ x.1
        have e : meromorphicOrderAt (b66g_coef R t q₀ (t, x.1)) (R.atlas.A (t, x.1) (t, x.1)).2 =
            (b66g_ord R t q₀ (b66g_pt R t x.1) : WithTop ℤ) := b66g_ord_eq R t hq₀ hq₀0 (b66g_pt R t x.1)
        rw [hord] at e
        have e0 : meromorphicOrderAt (b66g_coef R t q₀ (t, x.1))
            (R.atlas.A (t, x.1) (t, x.1)).2 = 0 := by
          rw [e]
          rfl
        unfold b66g_ζ
        exact han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp e0
      exact (b66g_coef_analytic R t q.property x.1).div (b66g_coef_analytic R t hq₀ x.1) hne
  simp only [b66g_beta, LinearMap.mk₂_apply]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [Finset.sum_coe_sort T (fun x => TauCeti.Contour.residue (fun w =>
    b66g_coef R t q.val (t, x) w / b66g_coef R t q₀ (t, x) w) (b66g_ζ R t x))]
  apply b66g_cform_residue_sum R t T (fun a z => b66g_coef R t q.val a z / b66g_coef R t q₀ a z)
  · intro a z hz
    exact ((b66g_forms_spec R t 2 q.property).1 a z hz).meromorphicAt.div
      ((b66g_forms_spec R t 1 hq₀).1 a z hz).meromorphicAt
  · intro a z hz hxT
    apply ((b66g_forms_spec R t 2 q.property).1 a z hz).div ((b66g_forms_spec R t 1 hq₀).1 a z hz)
    intro h0
    apply hxT
    apply hT
    have hp := b66g_inv_point R t a z hz
    exact (b66g_form_zero_iff R t hq₀ a (b66g_pt R t _) hp.1).mp h0
  · exact b66g_ratio_law R t hq₀ T hT q.property

theorem b66g_beta_ker (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {q₀ : b66g_Coeff R}
    (hq₀ : q₀ ∈ b66g_forms R t 1) (hq₀0 : q₀ ≠ 0) (T : Finset R.C)
    (hT : ∀ x, q₀ (t, x) x = 0 → x ∈ T) :
    LinearMap.ker (b66g_beta R t hq₀ T) ≤ Submodule.span ℂ {b66g_j1 R t q₀ T} := by
  have : FiniteDimensional ℂ (b66g_forms R t 2) := b66g_forms_two_finite R t
  set β := b66g_beta R t hq₀ T
  have hJ : Module.finrank ℂ ((x : T) → Fin (b66g_k R t q₀ x.1) → ℂ) =
      ∑ x : T, b66g_k R t q₀ x.1 := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun x _ => Module.finrank_fin_fun ℂ
  have hJZ : (Module.finrank ℂ ((x : T) → Fin (b66g_k R t q₀ x.1) → ℂ) : ℤ) =
      2 * (Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) : ℤ) - 2 := by
    rw [hJ, ← b66g_sum_k R t hq₀ hq₀0 T hT]
    push_cast
    exact Finset.sum_coe_sort T (fun x => (b66g_k R t q₀ x : ℤ))
  have hβ : β = β.flip.dualMap ∘ₗ
      (Module.evalEquiv ℂ ((x : T) → Fin (b66g_k R t q₀ x.1) → ℂ)).toLinearMap := by
    apply LinearMap.ext
    intro j
    apply LinearMap.ext
    intro q
    rfl
  have hrange : Module.finrank ℂ (LinearMap.range β) =
      Module.finrank ℂ (LinearMap.range β.flip) := by
    have hr : LinearMap.range β = LinearMap.range β.flip.dualMap := by
      conv_lhs => rw [hβ]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)
    rw [hr, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h1 := β.finrank_range_add_finrank_ker
  have h2 := β.flip.finrank_range_add_finrank_ker
  have h3 := b66g_betaT_finrank R t hq₀ hq₀0 T hT
  have h4 := b66g_forms_two_finrank R t
  have hk1 : Module.finrank ℂ (LinearMap.ker β) ≤ 1 := by
    have : (Module.finrank ℂ (LinearMap.ker β) : ℤ) ≤ 1 := by
      have e1 : (Module.finrank ℂ (LinearMap.range β) : ℤ) +
          Module.finrank ℂ (LinearMap.ker β) =
          Module.finrank ℂ ((x : T) → Fin (b66g_k R t q₀ x.1) → ℂ) := by exact_mod_cast h1
      have e2 : (Module.finrank ℂ (LinearMap.range β.flip) : ℤ) +
          Module.finrank ℂ (LinearMap.ker β.flip) = Module.finrank ℂ (b66g_forms R t 2) := by
        exact_mod_cast h2
      have e3 : (Module.finrank ℂ (LinearMap.ker β.flip) : ℤ) ≤
          Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by exact_mod_cast h3
      have e4 : (Module.finrank ℂ (LinearMap.range β) : ℤ) =
          Module.finrank ℂ (LinearMap.range β.flip) := by exact_mod_cast hrange
      linarith
    exact_mod_cast this
  have hj1 : b66g_j1 R t q₀ T ∈ LinearMap.ker β := by
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro q
    exact b66g_beta_j1 R t hq₀ hq₀0 T hT q
  by_cases hz : b66g_j1 R t q₀ T = 0
  · intro j _
    have hj : j = 0 := by
      funext x i
      exfalso
      have hk : 0 < b66g_k R t q₀ x.1 := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
      have := congrFun (congrFun hz x) ⟨0, hk⟩
      simp [b66g_j1] at this
    rw [hj]
    exact Submodule.zero_mem _
  · have hle : Submodule.span ℂ {b66g_j1 R t q₀ T} ≤ LinearMap.ker β :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr hj1
    have heq := Submodule.eq_of_le_of_finrank_le hle (by
      rw [finrank_span_singleton hz]
      exact hk1)
    rw [heq]

end B66gSerreInjective
section B66gSerreFinal

theorem b66g_res_taylor {φ Q Q₀ ρ : ℂ → ℂ} {ζ : ℂ} {k : ℕ} (α : Fin k → ℂ)
    (hexp : ∀ z, φ z = ∑ i : Fin k, α i * (z - ζ) ^ (i : ℕ) + (z - ζ) ^ k * ρ z)
    (hρ : AnalyticAt ℂ ρ ζ) (hQ : AnalyticAt ℂ Q ζ) (hQ₀ : AnalyticAt ℂ Q₀ ζ)
    (hord : meromorphicOrderAt Q₀ ζ = (k : WithTop ℤ)) :
    TauCeti.Contour.residue (fun z => φ z * (Q z / Q₀ z)) ζ =
      ∑ i : Fin k, α i * TauCeti.Contour.residue (fun z => (z - ζ) ^ (i : ℕ) * (Q z / Q₀ z)) ζ := by
  have hr : MeromorphicAt (fun z => Q z / Q₀ z) ζ := hQ.meromorphicAt.div hQ₀.meromorphicAt
  have hmk : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      MeromorphicAt (fun z => α i * ((z - ζ) ^ (i : ℕ) * (Q z / Q₀ z))) ζ := fun i _ =>
    (MeromorphicAt.const _ ζ).mul (((analyticAt_id.sub analyticAt_const).pow _).meromorphicAt.mul hr)
  have hm1 : MeromorphicAt (fun z => ∑ i : Fin k, α i * ((z - ζ) ^ (i : ℕ) * (Q z / Q₀ z))) ζ :=
    MeromorphicAt.fun_sum hmk
  have hm2 : MeromorphicAt (fun z => (z - ζ) ^ k * ρ z * (Q z / Q₀ z)) ζ :=
    ((((analyticAt_id.sub analyticAt_const).pow _).mul hρ).meromorphicAt).mul hr
  have he : (fun z => φ z * (Q z / Q₀ z)) =
      (fun z => ∑ i : Fin k, α i * ((z - ζ) ^ (i : ℕ) * (Q z / Q₀ z))) +
        (fun z => (z - ζ) ^ k * ρ z * (Q z / Q₀ z)) := by
    funext z
    simp only [Pi.add_apply, hexp z, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : TauCeti.Contour.residue (fun z => (z - ζ) ^ k * ρ z * (Q z / Q₀ z)) ζ = 0 := by
    apply TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg
    have hp : MeromorphicAt (fun z => (z - ζ) ^ k * ρ z) ζ :=
      (((analyticAt_id.sub analyticAt_const).pow _).mul hρ).meromorphicAt
    have hpk' : MeromorphicAt (fun z => (z - ζ) ^ k) ζ :=
      ((analyticAt_id.sub analyticAt_const).pow k).meromorphicAt
    rw [fun_meromorphicOrderAt_mul hp hr, fun_meromorphicOrderAt_mul hpk' hρ.meromorphicAt,
      fun_meromorphicOrderAt_div hQ.meromorphicAt hQ₀.meromorphicAt, hord]
    have hpk : meromorphicOrderAt (fun z => (z - ζ) ^ k) ζ = (k : WithTop ℤ) :=
      meromorphicOrderAt_pow_id_sub_const (x := ζ) (n := k)
    rw [hpk]
    have hρn := hρ.meromorphicOrderAt_nonneg
    have hQn := hQ.meromorphicOrderAt_nonneg
    rcases eq_or_ne (meromorphicOrderAt ρ ζ) ⊤ with h1 | h1
    · rw [h1]
      simp
    rcases eq_or_ne (meromorphicOrderAt Q ζ) ⊤ with h2 | h2
    · rw [h2]
      simp
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h1
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp h2
    rw [← ha] at hρn ⊢
    rw [← hb] at hQn ⊢
    have ha0 : 0 ≤ a := by exact_mod_cast hρn
    have hb0 : 0 ≤ b := by exact_mod_cast hQn
    have : ((k : ℕ) : WithTop ℤ) + (a : WithTop ℤ) + ((b : WithTop ℤ) - ((k : ℕ) : WithTop ℤ)) =
        (((k : ℤ) + a + (b - k) : ℤ) : WithTop ℤ) := by norm_cast
    rw [this]
    exact_mod_cast (by omega : (0 : ℤ) ≤ (k : ℤ) + a + (b - k))
  rw [he, TauCeti.Contour.residue_add hm1 hm2, h0, add_zero,
    show (fun z => ∑ i : Fin k, α i * ((z - ζ) ^ (i : ℕ) * (Q z / Q₀ z))) =
      ∑ i : Fin k, (fun z => α i * ((z - ζ) ^ (i : ℕ) * (Q z / Q₀ z))) by
        funext z
        rw [Finset.sum_apply],
    TauCeti.Contour.residue_sum _ hmk]
  exact Finset.sum_congr rfl fun i _ => TauCeti.Contour.residue_const_mul _

theorem b66g_serre_injective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (E : b66k_cechH1 R t →ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2))
    (hE : ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      E c q = b66g_residueSum R t S v q.val) :
    Function.Injective E := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc0
  obtain ⟨u, hu, hcu⟩ := Submodule.mem_map.mp c.property
  apply Subtype.ext
  change c.val = 0
  rw [← hcu, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hEz : ∀ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      b66g_residueSum R t S v q.val = 0 := by
    intro S v h1 h2 h3 q
    rw [← hE u hu c hcu.symm S v h1 h2 h3 q, hc0]
    rfl
  obtain ⟨S, v, hmero, hreg, hv⟩ := b66g_meromorphic_splitting_aux R t u hu
  obtain ⟨q₀, hq₀, hq₀0⟩ := b66g_form_exists R t
  obtain ⟨hqa₀, hql₀, _⟩ := b66g_forms_spec R t 1 hq₀
  obtain ⟨T, hT⟩ := b66g_form_zeros_finite R t hq₀ hq₀0
  have hnz : ∀ a x, x ∉ T → (t, x) ∈ (R.atlas.A a).source → q₀ a x ≠ 0 := by
    intro a x hx hax hz
    exact hx (hT x ((b66g_form_zero_iff R t hq₀ a (b66g_pt R t x) hax).mp hz))
  -- the scalar cocycle and its splitting
  have hs := b66g_contract_mem R t hq₀ hu
  obtain ⟨h', hh'a, hh's⟩ := b66g_scalar_dual R t hs S
    (fun a z => b66g_coef R t q₀ a z * v a z)
    (fun a z hz => (hqa₀ a z hz).meromorphicAt.mul (hmero a z hz))
    (fun a z hz hS => (hqa₀ a z hz).mul (hreg a z hz hS))
    (fun a b x hx ha hb => by
      have e := hv a b x hx ha hb
      simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
        (R.atlas.A b).source from ⟨ha, hb⟩)] at e
      simp only [b66g_contract, b66g_coef]
      rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2, e,
        hql₀ a b x ha hb, pow_one]
      ring)
    (fun η hη => by
      have hprod := (b66g_cup_aux R t).2 ⟨q₀, hq₀⟩ ⟨η, hη⟩
      have := hEz S v hmero hreg hv ⟨b66g_product R q₀ η, hprod⟩
      rw [← this]
      unfold b66g_residueSum
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      funext z
      simp only [b66g_coef, b66g_product]
      ring)
  -- the splitting h'/q₀, holomorphic off T
  set w : b66k_Index R → ℂ → ℂ := fun a z => h' a z / b66g_coef R t q₀ a z
  have hwv : ∀ a b x, x ∉ T → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t w a b x := by
    intro a b x hx ha hb
    have e := hh's a b x ha hb
    simp only [b66g_contract] at e
    simp only [b66k_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A b).source from ⟨ha, hb⟩), w, b66g_coef]
    rw [(b66g_chart_slice R t a x ha).2, (b66g_chart_slice R t b x hb).2, hql₀ a b x ha hb, pow_one]
    have h1 := hnz b x hx hb
    have h2 := b66g_vertical_ne R t a b x ha hb
    field_simp
    linear_combination e
  have hwm : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (w a) z := fun a z hz =>
    (hh'a a z hz).meromorphicAt.div (hqa₀ a z hz).meromorphicAt
  have hwr : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ T → AnalyticAt ℂ (w a) z := by
    intro a z hz hxT
    exact (hh'a a z hz).div (hqa₀ a z hz) (hnz a _ hxT (b66g_inv_point R t a z hz).1)
  have hE' := hEz T w hwm hwr hwv
  -- Taylor jets of h' along T
  have hkord : ∀ x : R.C, meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (b66g_ζ R t x) =
      ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) := by
    intro x
    have e : meromorphicOrderAt (b66g_coef R t q₀ (t, x)) (R.atlas.A (t, x) (t, x)).2 =
        (b66g_ord R t q₀ (b66g_pt R t x) : WithTop ℤ) := b66g_ord_eq R t hq₀ hq₀0 (b66g_pt R t x)
    unfold b66g_ζ b66g_k
    rw [e]
    have h := Int.toNat_of_nonneg (b66g_ord_nonneg R t hq₀ hq₀0 (b66g_pt R t x))
    conv_lhs => rw [← h]
    rfl
  choose α ρ hρ hexp using fun x : T =>
    b66g_taylor ((hh'a (t, x.1)) _ (b66g_own_domain R t x.1)) (b66g_k R t q₀ x.1)
  have hβ0 : b66g_beta R t hq₀ T (fun x i => α x i) = 0 := by
    apply LinearMap.ext
    intro q
    rw [LinearMap.zero_apply, ← hE' q]
    simp only [b66g_beta, LinearMap.mk₂_apply]
    unfold b66g_residueSum
    rw [← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [b66g_ζ]
    rw [← b66g_res_taylor (α x) (hexp x) (hρ x) (b66g_coef_analytic R t q.property x.1)
      (b66g_coef_analytic R t hq₀ x.1) (hkord x.1)]
    congr 1
    funext z
    simp only [w, b66g_coef]
    ring
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp
    (b66g_beta_ker R t hq₀ hq₀0 T hT (LinearMap.mem_ker.mpr hβ0))
  have hα : ∀ x i, α x i = if (i : ℕ) = 0 then κ else 0 := by
    intro x i
    have := congrFun (congrFun hκ x) i
    simp only [b66g_j1, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
    exact this.symm
  have hvan : ∀ x : T, ((b66g_k R t q₀ x.1 : ℕ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => h' (t, x.1) z - κ) (b66g_ζ R t x.1) := by
    intro x
    by_cases hk : b66g_k R t q₀ x.1 = 0
    · rw [hk]
      exact (((hh'a (t, x.1)) _ (b66g_own_domain R t x.1)).sub analyticAt_const).meromorphicOrderAt_nonneg
    · have hk' : 0 < b66g_k R t q₀ x.1 := Nat.pos_of_ne_zero hk
      have he : (fun z => h' (t, x.1) z - κ) =
          fun z => (z - b66g_ζ R t x.1) ^ (b66g_k R t q₀ x.1) * ρ x z := by
        funext z
        rw [hexp x z, Finset.sum_eq_single ⟨0, hk'⟩]
        · simp only [hα, ite_true, pow_zero, mul_one, b66g_ζ]
          ring
        · intro i _ hi
          have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          simp [hα, this]
        · simp
      rw [he]
      have hpk : MeromorphicAt (fun z => (z - b66g_ζ R t x.1) ^ (b66g_k R t q₀ x.1))
          (b66g_ζ R t x.1) := ((analyticAt_id.sub analyticAt_const).pow _).meromorphicAt
      rw [fun_meromorphicOrderAt_mul hpk (hρ x).meromorphicAt,
        show meromorphicOrderAt (fun z => (z - b66g_ζ R t x.1) ^ (b66g_k R t q₀ x.1))
          (b66g_ζ R t x.1) = ((b66g_k R t q₀ x.1 : ℕ) : WithTop ℤ) from
          meromorphicOrderAt_pow_id_sub_const (x := b66g_ζ R t x.1) (n := b66g_k R t q₀ x.1)]
      exact le_add_of_nonneg_right (hρ x).meromorphicOrderAt_nonneg
  have hopen : ∀ a, IsOpen (b66k_domain R t a) := fun a =>
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  have hnn : ∀ a z, z ∈ b66k_domain R t a →
      0 ≤ meromorphicOrderAt (fun w => (h' a w - κ) / b66g_coef R t q₀ a w) z := by
    intro a z hz
    have hp := b66g_inv_point R t a z hz
    by_cases hq : b66g_coef R t q₀ a z ≠ 0
    · exact (((hh'a a z hz).sub analyticAt_const).div (hqa₀ a z hz) hq).meromorphicOrderAt_nonneg
    push Not at hq
    set x := ((R.atlas.A a).symm (t.val, z)).2
    have hxT : x ∈ T := hT x ((b66g_form_zero_iff R t hq₀ a (b66g_pt R t x) hp.1).mp hq)
    set c : b66k_Index R := (t, x)
    have hc : (t, x) ∈ (R.atlas.A c).source := (R.atlas.hA c).1
    have hz' : z ∈ b66k_refinementDomain R t 1 a c := ⟨hz, by rw [one_smul]; exact hc⟩
    obtain ⟨hTm, hTd, hTa, hDa⟩ := b66g_transition_mem R t a c z hz'
    have hTz : b66k_transition R a c (t.val, z) = b66g_ζ R t x := b66g_trans_point R t a c z hz
    have hD0 : fderiv ℂ (b66k_transition R a c) (t.val, z) (0, 1) ≠ 0 := by
      rw [← b66g_vertical_eq_D R t a c z hz]
      exact b66g_vertical_ne R t a c x hp.1 hc
    have hTd' : deriv (fun w => b66k_transition R a c (t.val, w)) z ≠ 0 := by
      rw [(b66g_transition_hasDerivAt R t a c z hTm).deriv]
      exact hD0
    have hdec : (fun w => h' a w - κ) =ᶠ[𝓝 z] fun w =>
        (h' c (b66k_transition R a c (t.val, w)) - κ) +
          b66g_coef R t q₀ c (b66k_transition R a c (t.val, w)) *
            u a c ((R.atlas.A a).symm (t.val, w)).2 := by
      filter_upwards [b66g_overlap_eventually R t a c z hz', (hopen a).mem_nhds hz]
        with w ⟨hmem, h1, h2⟩ hw
      have e := hh's a c _ hmem.1 hmem.2
      simp only [b66g_contract] at e
      rw [h1, h2] at e
      have hx' := (b66g_trans_inv R t a c w hw hmem.2).2
      simp only [b66g_coef]
      rw [hx']
      linear_combination -e
    have hu' := (b66g_holomorphic_spec R t hu.1).1 a c z hz'
    have hf1 : MeromorphicAt (fun w => h' c (b66k_transition R a c (t.val, w)) - κ) z :=
      ((AnalyticAt.comp (f := fun w => b66k_transition R a c (t.val, w))
        (by rw [hTz]; exact (hh'a c _ (b66g_own_domain R t x))) hTa).sub
        analyticAt_const).meromorphicAt
    have hQc : AnalyticAt ℂ (b66g_coef R t q₀ c) (b66k_transition R a c (t.val, z)) := by
      rw [hTz]
      exact b66g_coef_analytic R t hq₀ x
    have hf2a : MeromorphicAt (fun w => b66g_coef R t q₀ c (b66k_transition R a c (t.val, w))) z :=
      (AnalyticAt.comp (f := fun w => b66k_transition R a c (t.val, w)) hQc hTa).meromorphicAt
    have hf2 : MeromorphicAt (fun w => b66g_coef R t q₀ c (b66k_transition R a c (t.val, w)) *
        u a c ((R.atlas.A a).symm (t.val, w)).2) z := hf2a.mul hu'.meromorphicAt
    have hk1 : ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun w => h' c (b66k_transition R a c (t.val, w)) - κ) z := by
      have h := hvan ⟨x, hxT⟩
      rw [show (fun w => h' c (b66k_transition R a c (t.val, w)) - κ) =
        (fun y => h' (t, x) y - κ) ∘ fun w => b66k_transition R a c (t.val, w) from rfl,
        meromorphicOrderAt_comp_of_deriv_ne_zero hTa hTd', hTz]
      exact h
    have hk2 : ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun w => b66g_coef R t q₀ c (b66k_transition R a c (t.val, w)) *
          u a c ((R.atlas.A a).symm (t.val, w)).2) z := by
      rw [fun_meromorphicOrderAt_mul hf2a hu'.meromorphicAt,
        show (fun w => b66g_coef R t q₀ c (b66k_transition R a c (t.val, w))) =
          b66g_coef R t q₀ c ∘ fun w => b66k_transition R a c (t.val, w) from rfl,
        meromorphicOrderAt_comp_of_deriv_ne_zero hTa hTd', hTz, hkord x]
      exact le_add_of_nonneg_right hu'.meromorphicOrderAt_nonneg
    have hnum : ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun w => h' a w - κ) z := by
      rw [meromorphicOrderAt_congr (hdec.filter_mono nhdsWithin_le_nhds)]
      exact le_trans (le_min hk1 hk2) (meromorphicOrderAt_add hf1 hf2)
    have hden : meromorphicOrderAt (b66g_coef R t q₀ a) z = ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) := by
      rw [b66g_coef_order_chart R t hq₀ a z hz]
      exact hkord x
    have hnm : MeromorphicAt (fun w => h' a w - κ) z :=
      ((hh'a a z hz).sub analyticAt_const).meromorphicAt
    have hdm : MeromorphicAt (b66g_coef R t q₀ a) z := (hqa₀ a z hz).meromorphicAt
    rw [fun_meromorphicOrderAt_div hnm hdm, hden]
    rcases eq_or_ne (meromorphicOrderAt (fun w => h' a w - κ) z) ⊤ with htop | htop
    · rw [htop]
      simp
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hn] at hnum ⊢
      have : ((b66g_k R t q₀ x : ℕ) : ℤ) ≤ n := by exact_mod_cast hnum
      have h2 : (n : WithTop ℤ) - ((b66g_k R t q₀ x : ℕ) : WithTop ℤ) =
          ((n - (b66g_k R t q₀ x : ℕ) : ℤ) : WithTop ℤ) := by norm_cast
      rw [h2]
      exact_mod_cast (by omega : (0 : ℤ) ≤ n - (b66g_k R t q₀ x : ℕ))
  -- the holomorphic splitting
  set W : b66k_Index R → ℂ → ℂ := fun a => b66g_nf (fun w => (h' a w - κ) / b66g_coef R t q₀ a w)
  have hWm : ∀ a z, z ∈ b66k_domain R t a →
      MeromorphicAt (fun w => (h' a w - κ) / b66g_coef R t q₀ a w) z := fun a z hz =>
    ((hh'a a z hz).sub analyticAt_const).meromorphicAt.div (hqa₀ a z hz).meromorphicAt
  have hWa : ∀ a, AnalyticOnNhd ℂ (W a) (b66k_domain R t a) := fun a z hz =>
    b66g_nf_analytic (hWm a z hz) (hnn a z hz)
  have hueq : u = b66k_boundary R t W := by
    funext a b x
    by_cases hab : (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source
    · set z := (R.atlas.A a (t, x)).2
      have hz : z ∈ b66k_refinementDomain R t 1 a b :=
        b66g_refinement_point R t 1 a b x hab.1 (by rw [one_smul]; exact hab.2)
      have hxz : ((R.atlas.A a).symm (t.val, z)).2 = x := (b66g_chart_slice R t a x hab.1).2
      obtain ⟨hTm, hTd, hTa, hDa⟩ := b66g_transition_mem R t a b z hz
      have hU := (b66g_holomorphic_spec R t hu.1).1 a b z hz
      have hB : AnalyticAt ℂ (fun w => fderiv ℂ (b66k_transition R a b) (t.val, w) (0, 1) * W a w -
          W b (b66k_transition R a b (t.val, w))) z :=
        (hDa.mul (hWa a z hz.1)).sub
          (AnalyticAt.comp (f := fun w => b66k_transition R a b (t.val, w)) (hWa b _ hTd) hTa)
      have heq := b66g_eq_of_nhdsNE hU.continuousAt hB.continuousAt (by
        filter_upwards [b66g_avoid R t a z hz.1 T,
          nhdsWithin_le_nhds (b66g_boundary_near R t w a b z hz),
          b66g_nf_eventually (hWm a z hz.1),
          (b66g_trans_tendsto R t a b z hz).eventually (b66g_nf_eventually (hWm b _ hTd)),
          nhdsWithin_le_nhds (b66g_overlap_eventually R t a b z hz),
          nhdsWithin_le_nhds ((hopen a).mem_nhds hz.1)] with ν hwT hbw hna hnb ⟨hmem, _, _⟩ hwd
        simp only [W]
        rw [hwv a b _ hwT hmem.1 hmem.2, hbw, hna, hnb]
        have hx' := (b66g_trans_inv R t a b ν hwd hmem.2).2
        have hlaw : b66g_coef R t q₀ a ν = fderiv ℂ (b66k_transition R a b) (t.val, ν) (0, 1) *
            b66g_coef R t q₀ b (b66k_transition R a b (t.val, ν)) := by
          simp only [b66g_coef]
          rw [hx', ← b66g_vertical_eq_D R t a b ν hwd]
          have := hql₀ a b _ hmem.1 hmem.2
          rwa [pow_one] at this
        have hnb0 : b66g_coef R t q₀ b (b66k_transition R a b (t.val, ν)) ≠ 0 := by
          simp only [b66g_coef]
          rw [hx']
          exact hnz b _ hwT hmem.2
        have hD0 : fderiv ℂ (b66k_transition R a b) (t.val, ν) (0, 1) ≠ 0 := by
          rw [← b66g_vertical_eq_D R t a b ν hwd]
          exact b66g_vertical_ne R t a b _ hmem.1 hmem.2
        simp only [w]
        rw [hlaw]
        field_simp
        ring)
      rw [hxz] at heq
      rw [heq]
      simp only [b66k_boundary, ite_eq_left hab]
      rw [← hxz, b66g_vertical_eq_D R t a b z hz.1, hxz, b66g_trans_point R t a b z hz.1, hxz]
    · rw [(b66g_holomorphic_spec R t hu.1).2 a b x hab]
      simp only [b66k_boundary, ite_eq_right hab]
  exact Submodule.subset_span ⟨W, hWa, hueq⟩

theorem b66g_serre_pairing_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ E : b66k_cechH1 R t ≃ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      E c q = b66g_residueSum R t S v q.val := by
  obtain ⟨E, hE⟩ := b66g_serre_functional R t
  exact ⟨LinearEquiv.ofBijective E ⟨b66g_serre_injective R t E hE, b66g_serre_surjective R t E hE⟩,
    fun u hu c hc S v hmero hreg hv q => hE u hu c hc S v hmero hreg hv q⟩

end B66gSerreFinal

end HodgeLean.Foundations.Program
