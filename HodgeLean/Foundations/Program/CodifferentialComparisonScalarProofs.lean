import HodgeLean.Foundations.Program.CodifferentialComparisonHarmonicProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonGraphProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers Metric
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b3Forms_isManifold_real
variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_gen_b66m_sc_open_source (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
  (R.atlas.A a).open_source.preimage continuous_subtype_val

def b66f_gen_b66m_sc_cechProjection (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66g_scalarCycles R t →ₗ[ℂ] b66f_gen_b66g_H1O R t :=
  (((b66f_gen_b66g_scalarBoundaries R t).mkQ).comp (b66f_gen_b66g_scalarCycles R t).subtype).codRestrict
    (b66f_gen_b66g_H1O R t) (fun u => ⟨u.val, u.property, rfl⟩)

theorem b66f_gen_b66m_rs_forms_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (m : ℕ)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t m) :
    (∀ a, AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_domain R t a)) ∧
    (∀ a b x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      q a x = b66f_vertical R t a b x ^ m * q b x) ∧
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

theorem b66f_gen_b66m_rs_holomorphic_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {u : b66f_Cochain R} (hu : u ∈ b66f_gen_b66k_holomorphicCochains R t) :
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 a b)) ∧
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

theorem b66f_gen_b66m_rs_transition_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_gen_b66k_refinementDomain R t 1 a b) :
    (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source ∧
    b66f_transition R a b (t.val, z) ∈ b66f_domain R t b ∧
    AnalyticAt ℂ (fun w => b66f_transition R a b (t.val, w)) z ∧
    AnalyticAt ℂ (fun w => fderiv ℂ (b66f_transition R a b) (t.val, w) (0, 1)) z := by
  have hi := b66f_gen_b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hd : ContDiffAt ℂ ω (b66f_transition R a b) (t.val, z) :=
    (b66f_gen_b66k_transition_analytic R a b _ hm).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => fderiv ℂ (b66f_transition R a b) u (0, 1)) (t.val, z) :=
    (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
  refine ⟨hm, ?_, ?_, ?_⟩
  · have hy : (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source := hm.2
    change (t.val, (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).2) ∈ (R.atlas.A b).target
    have h1 : (R.atlas.A b ((R.atlas.A a).symm (t.val, z))).1 = t.val := by
      rw [R.atlas.hparam b _ hy, b66f_gen_b66k_inverse_parameter R a _ hz.1]
    convert (R.atlas.A b).map_source hy using 1
    exact Prod.ext h1.symm rfl
  · exact (b66f_gen_b66k_transition_analytic R a b _ hm).comp
      (analyticAt_const.prod analyticAt_id)
  · exact (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt

theorem b66f_gen_b66m_rs_overlap_eventually (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_gen_b66k_refinementDomain R t 1 a b) :
    ∀ᶠ w in 𝓝 z,
      (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∧
      R.atlas.A a (t, ((R.atlas.A a).symm (t.val, w)).2) = (t.val, w) ∧
      (R.atlas.A b (t, ((R.atlas.A a).symm (t.val, w)).2)).2 =
        b66f_transition R a b (t.val, w) := by
  have hi := b66f_gen_b66k_inverse_slice R t a z hz.1
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
  have hiw := b66f_gen_b66k_inverse_slice R t a w hw.1
  rw [hiw]
  exact ⟨⟨(R.atlas.A a).map_target hw.1, hw.2⟩, (R.atlas.A a).right_inv hw.1, rfl⟩

theorem b66f_gen_b66m_rs_chart_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (b : b66f_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) ∧
    ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x := by
  have h1 : R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) :=
    Prod.ext (R.atlas.hparam b _ hb) rfl
  refine ⟨h1, ?_⟩
  rw [← h1, (R.atlas.A b).left_inv hb]

theorem b66f_gen_b66m_rs_target_coefficient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (a b : b66f_Index R) (z : ℂ)
    (hz : z ∈ b66f_gen_b66k_refinementDomain R t 1 a b)
    (hq : AnalyticOnNhd ℂ (fun z => q b ((R.atlas.A b).symm (t.val, z)).2)
      (b66f_domain R t b)) :
    AnalyticAt ℂ (fun w => q b ((R.atlas.A a).symm (t.val, w)).2) z := by
  obtain ⟨_, hdom, han, _⟩ := b66f_gen_b66m_rs_transition_mem R t a b z hz
  have h1 : AnalyticAt ℂ (fun w =>
      q b ((R.atlas.A b).symm (t.val, b66f_transition R a b (t.val, w))).2) z :=
    AnalyticAt.comp (f := fun w => b66f_transition R a b (t.val, w)) (hq _ hdom) han
  apply h1.congr
  filter_upwards [b66f_gen_b66m_rs_overlap_eventually R t a b z hz] with w ⟨hmem, _, hb⟩
  rw [← hb, (b66f_gen_b66m_rs_chart_slice R t b _ hmem.2).2]

theorem b66f_gen_b66m_rs_kernel_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {u : b66f_Cochain R} (hu : u ∈ LinearMap.ker (b66f_gen_b66k_differential R t))
    (a b c : b66f_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) (hc : (t, x) ∈ (R.atlas.A c).source) :
    u a c x = u b c x + b66f_vertical R t b c x * u a b x := by
  have h := congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hu) a) b) c) x
  simp only [b66f_gen_b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩
      (R.atlas.A c).source from ⟨⟨ha, hb⟩, hc⟩)] at h
  linear_combination h

theorem b66f_gen_b66m_rs_contract_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) {u : b66f_Cochain R}
    (hu : u ∈ b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t)) :
    b66f_gen_b66g_contract R q u ∈ b66f_gen_b66g_scalarCycles R t := by
  obtain ⟨hqa, hql, _⟩ := b66f_gen_b66m_rs_forms_spec R t 1 hq
  obtain ⟨hua, huz⟩ := b66f_gen_b66m_rs_holomorphic_spec R t hu.1
  apply Submodule.subset_span
  refine ⟨fun a b z hz => ?_, fun a b x hx => ?_, fun a b c x ha hb hc => ?_⟩
  · exact (b66f_gen_b66m_rs_target_coefficient R t q a b z hz (hqa b)).mul (hua a b z hz)
  · simp only [b66f_gen_b66g_contract, huz a b x hx, mul_zero]
  · simp only [b66f_gen_b66g_contract]
    rw [b66f_gen_b66m_rs_kernel_spec R t hu.2 a b c x ha hb hc, hql b c x hb hc, pow_one]
    ring

theorem b66f_gen_b66k_cocycle_holomorphic_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (a b : b66f_Index R) :
    AnalyticOnNhd ℂ
      (fun z => b66f_cocycle R t h a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 a b) := by
  intro z hz
  have hi := b66f_gen_b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hd : ContDiffAt ℂ ω (b66f_transition R a b) (t.val, z) :=
    (b66f_gen_b66k_transition_analytic R a b _ hm).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => fderiv ℂ (b66f_transition R a b) u (h, 0)) (t.val, z) :=
    (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
  apply ContDiffAt.analyticAt
  apply (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq
  have hopen := ((R.atlas.A a).symm.trans (R.atlas.A b)).open_source
  have hev := (continuous_const.prodMk continuous_id).continuousAt
    (hopen.mem_nhds hm)
  filter_upwards [hev] with w hw
  change (t.val, w) ∈ (R.atlas.A a).target ∧
    (R.atlas.A a).symm (t.val, w) ∈ (R.atlas.A b).source at hw
  have hiw := b66f_gen_b66k_inverse_slice R t a w hw.1
  have hmem : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈
      (R.atlas.A a).source ∩ (R.atlas.A b).source := by
    rw [hiw]
    exact ⟨(R.atlas.A a).map_target hw.1, hw.2⟩
  rw [hiw] at hmem
  simp only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hmem,
    hiw, (R.atlas.A a).right_inv hw.1]
  rfl

theorem b66f_gen_b66k_cocycle_law_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (a b c : b66f_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66f_cocycle R t h a c x = b66f_cocycle R t h b c x +
      b66f_vertical R t b c x * b66f_cocycle R t h a b x := by
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
  have dab := (b66f_gen_b66k_transition_analytic R a b u hab).differentiableAt
  have dbc := (b66f_gen_b66k_transition_analytic R b c w hbc).differentiableAt
  let T : ((Fin 10 → ℂ) × ℂ) → ((Fin 10 → ℂ) × ℂ) :=
    fun v => (v.1, b66f_transition R a b v)
  have hT : T u = w := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam b _ hb).symm
    · exact congrArg (fun y => (R.atlas.A b y).2) ((R.atlas.A a).left_inv ha)
  have he : (fun v => b66f_transition R b c (T v)) =ᶠ[𝓝 u]
      b66f_transition R a c := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hab]
      with v hv
    have ht : T v = R.atlas.A b ((R.atlas.A a).symm v) := by
      apply Prod.ext
      · exact (b6a_transition_fst c₀ R.C R.atlas.A R.atlas.hparam a b v hv).symm
      · rfl
    change (R.atlas.A c ((R.atlas.A b).symm (T v))).2 = _
    rw [ht]
    rw [(R.atlas.A b).left_inv (x := (R.atlas.A a).symm v) hv.2]
    rfl
  have dbc' : HasFDerivAt (b66f_transition R b c)
      (fderiv ℂ (b66f_transition R b c) w) (T u) := by
    rw [hT]
    exact dbc.hasFDerivAt
  have hder := dbc'.comp u (hasFDerivAt_fst.prodMk dab.hasFDerivAt)
  have hf := (hder.congr_of_eventuallyEq he.symm).fderiv
  have hl (L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ) (q : ℂ) :
      L (h, q) = L (h, 0) + q * L (0, 1) := by
    have hp : (h, q) = (h, (0 : ℂ)) + q • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
      simp
    rw [hp, map_add, map_smul]
    rfl
  simp only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A c).source from ⟨ha, hc⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩ (R.atlas.A c).source from ⟨hb, hc⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨ha, hb⟩),
    b66f_vertical]
  change fderiv ℂ (b66f_transition R a c) u (h, 0) = _
  rw [hf]
  change fderiv ℂ (b66f_transition R b c) w
    (h, fderiv ℂ (b66f_transition R a b) u (h, 0)) = _
  rw [hl, mul_comm]

theorem b66f_gen_b66k_cocycle_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) :
    b66f_cocycle R t h ∈ b66f_gen_b66k_holomorphicCochains R t ⊓
      LinearMap.ker (b66f_gen_b66k_differential R t) := by
  constructor
  · apply Submodule.subset_span
    refine ⟨b66f_gen_b66k_cocycle_holomorphic_aux R t h, ?_⟩
    intro a b x hx
    simp only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hx]
  · change b66f_gen_b66k_differential R t (b66f_cocycle R t h) = 0
    funext a b c x
    simp only [b66f_gen_b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs with hx
    · rw [b66f_gen_b66k_cocycle_law_aux R t h a b c x hx.1.1 hx.1.2 hx.2]
      ring
    · rfl

def b66f_gen_b66m_dolbeaultIntegral (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) : ℂ :=
  2 * ((b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
      (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm θ)) : ℝ) -
    Complex.I * (b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
      (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm (Complex.I • θ))) : ℝ))

def b66f_gen_b66m_dolbeaultTrace (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (c : b4c_Dolbeault01 ℂ (b65z_fibre c₀ R.C t))
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) : ℂ :=
  let P := (Submodule.span ℂ (b4c_dbar ℂ (b65z_fibre c₀ R.C t) ''
    (b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) : Set (b65z_fibre c₀ R.C t → ℂ)))).comap
      (b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)).subtype
  b66f_gen_b66m_dolbeaultIntegral R t (Classical.choose (P.mkQ_surjective c)) θ

def b66f_gen_b66m_sc_tau (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (s : b66f_Cochain R) (b : b66f_Index R) (y : b65z_fibre c₀ R.C t) : ℂ :=
  -∑ᶠ c, ρ c y • s c b y.val.2

def b66f_gen_b66m_sc_gamma (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (s : b66f_Cochain R) : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ :=
  fun p => b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ s p.1.val) p

theorem b66f_gen_b66m_sc_scalarCycles_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {u : b66f_Cochain R} (hu : u ∈ b66f_gen_b66g_scalarCycles R t) :
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 a b)) ∧
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

def b66f_gen_b66m_sc_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (a : b66f_Index R) :
    b65z_fibre c₀ R.C t → ℂ := fun y => (R.atlas.A a y.val).2

theorem b66f_gen_b66m_sc_slice_value (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    R.atlas.A a y.val = (t.val, (R.atlas.A a y.val).2) := by
  refine Prod.ext ?_ rfl
  rw [R.atlas.hparam a _ hy]
  exact congrArg Subtype.val y.property

theorem b66f_gen_b66m_sc_slice_domain (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66m_sc_slice R t a y ∈ b66f_domain R t a := by
  change (t.val, (R.atlas.A a y.val).2) ∈ (R.atlas.A a).target
  rw [← b66f_gen_b66m_sc_slice_value R t a y hy]
  exact (R.atlas.A a).map_source hy

theorem b66f_gen_b66m_sc_inv_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ((R.atlas.A a).symm (t.val, b66f_gen_b66m_sc_slice R t a y)).2 = y.val.2 := by
  change ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2)).2 = _
  rw [← b66f_gen_b66m_sc_slice_value R t a y hy, (R.atlas.A a).left_inv hy]

theorem b66f_gen_b66m_sc_fibre_val (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (y : b65z_fibre c₀ R.C t) : y.val = (t, y.val.2) :=
  Prod.ext y.property rfl

theorem b66f_gen_b66g_slice_coordinate (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun p : b65z_fibre c₀ R.C t => (R.atlas.A a p.val).2)
      {p | p.val ∈ (R.atlas.A a).source} ∧
    ∀ p : b65z_fibre c₀ R.C t, p.val ∈ (R.atlas.A a).source →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p ≠ 0 :=
  b66f_gen_b66g_slice_coordinate_aux R t a

example := @b66f_gen_b66g_slice_coordinate

theorem b66f_gen_b66m_sc_slice_contMDiffAt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66f_gen_b66m_sc_slice R t a) y :=
  (b66f_gen_b66g_slice_coordinate R t a).1.contMDiffAt
    (((R.atlas.A a).open_source.preimage continuous_subtype_val).mem_nhds hy)

theorem b66f_gen_b66m_sc_cochain_holo (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (u : b66f_Cochain R) (c b : b66f_Index R)
    (hu : AnalyticOnNhd ℂ (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 c b))
    (y : b65z_fibre c₀ R.C t) (hc : y.val ∈ (R.atlas.A c).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : b65z_fibre c₀ R.C t => u c b y.val.2) y := by
  have hz : b66f_gen_b66m_sc_slice R t c y ∈ b66f_gen_b66k_refinementDomain R t 1 c b := by
    refine ⟨b66f_gen_b66m_sc_slice_domain R t c y hc, ?_⟩
    rw [b66f_gen_b66m_sc_inv_slice R t c y hc, one_smul, ← b66f_gen_b66m_sc_fibre_val R t y]
    exact hb
  have han := hu _ hz
  have hF : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2) (b66f_gen_b66m_sc_slice R t c y) :=
    han.contDiffAt.contMDiffAt
  apply (hF.comp y (b66f_gen_b66m_sc_slice_contMDiffAt R t c y hc)).congr_of_eventuallyEq
  filter_upwards [(b66f_gen_b66m_sc_open_source R t c).mem_nhds hc] with y' hy'
  simp only [Function.comp_apply, b66f_gen_b66m_sc_inv_slice R t c y' hy']

theorem b66f_gen_b66m_sc_tau_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66f_Cochain R} (hs : s ∈ b66f_gen_b66g_scalarCycles R t) (b : b66f_Index R)
    (y : b65z_fibre c₀ R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66f_gen_b66m_sc_tau R t ρ s b) y := by
  have hsa := (b66f_gen_b66m_sc_scalarCycles_spec R t hs).1
  apply ContMDiffAt.neg
  apply ρ.contMDiffAt_finsum
  intro c hc
  exact (b3A_contMDiffWithinAt_real
    (b66f_gen_b66m_sc_cochain_holo R t s c b (hsa c b) y (hρ c hc) hb)).of_le (by simp)

theorem b66f_gen_b66m_sc_tau_sub (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66f_Cochain R} (hs : s ∈ b66f_gen_b66g_scalarCycles R t) (a b : b66f_Index R)
    (y : b65z_fibre c₀ R.C t) (ha : y.val ∈ (R.atlas.A a).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    b66f_gen_b66m_sc_tau R t ρ s a y - b66f_gen_b66m_sc_tau R t ρ s b y = s a b y.val.2 := by
  have hlaw := (b66f_gen_b66m_sc_scalarCycles_spec R t hs).2.2
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
      rw [b66f_gen_b66m_sc_fibre_val R t y] at ha hb hyc
      rw [hlaw c a b y.val.2 hyc ha hb]
      ring
  unfold b66f_gen_b66m_sc_tau
  rw [neg_sub_neg, ← finsum_sub_distrib hf2 hf1]
  simp only [hterm]
  rw [← finsum_smul, ρ.sum_eq_one (mem_univ y), one_smul]

theorem b66f_gen_b66m_sc_gamma_local (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66f_Cochain R} (hs : s ∈ b66f_gen_b66g_scalarCycles R t) (b : b66f_Index R)
    (y : b65z_fibre c₀ R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ∀ᶠ y' in 𝓝 y, ∀ v : ℂ, b66f_gen_b66m_sc_gamma R t ρ s ⟨y', v⟩ =
      b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ s b) ⟨y', v⟩ := by
  have hsa := (b66f_gen_b66m_sc_scalarCycles_spec R t hs).1
  filter_upwards [(b66f_gen_b66m_sc_open_source R t b).mem_nhds hb] with y' hy' v
  have ha : y'.val ∈ (R.atlas.A y'.val).source := (R.atlas.hA y'.val).1
  have heq : b66f_gen_b66m_sc_tau R t ρ s y'.val =ᶠ[𝓝 y']
      b66f_gen_b66m_sc_tau R t ρ s b + fun y'' => s y'.val b y''.val.2 := by
    filter_upwards [(b66f_gen_b66m_sc_open_source R t y'.val).mem_nhds ha,
      (b66f_gen_b66m_sc_open_source R t b).mem_nhds hy'] with y'' h1 h2
    have := b66f_gen_b66m_sc_tau_sub R t ρ hρ hs y'.val b y'' h1 h2
    simp only [Pi.add_apply]
    linear_combination this
  change b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ s y'.val) ⟨y', v⟩ = _
  rw [RiemannRochAna_dbar_congr heq v]
  have hS := b66f_gen_b66m_sc_cochain_holo R t s y'.val b (hsa _ _) y' ha hy'
  rw [RiemannRochAna_dbar_add_at _ _ y'
    ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ hs b y' hy').mdifferentiableAt (by simp))
    ((b3A_contMDiffWithinAt_real hS).mdifferentiableWithinAt (by simp) |>.mdifferentiableAt
      Filter.univ_mem) v,
    RiemannRochAna_dbar_holomorphic_at _ y' (hS.mdifferentiableAt (by simp)) v, add_zero]

theorem b66f_gen_b66m_sc_gamma_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66f_Cochain R} (hs : s ∈ b66f_gen_b66g_scalarCycles R t) :
    b66f_gen_b66m_sc_gamma R t ρ s ∈ b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  refine ⟨fun p => ?_, fun x a v w => ?_⟩
  · set b := p.1.val
    have hb : p.1.val ∈ (R.atlas.A b).source := (R.atlas.hA b).1
    obtain ⟨χ, hχ, hχ1, hχs⟩ := RiemannRochAna_cutoff hE p.1
      ((b66f_gen_b66m_sc_open_source R t b).mem_nhds hb)
    let u : b65z_fibre c₀ R.C t → ℂ := fun y => (χ y : ℂ) * b66f_gen_b66m_sc_tau R t ρ s b y
    have hu : u ∈ b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) := by
      intro y
      by_cases hy : y ∈ tsupport χ
      · exact (Complex.ofRealCLM.contMDiff.comp hχ).contMDiffAt.mul
          (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hs b y (hχs hy))
      · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simp only [u, show χ z = 0 from hz, Complex.ofReal_zero, zero_mul]
    have hsm := RiemannRochAna_dbar_smooth (E := ℂ) (C := b65z_fibre c₀ R.C t) ⟨u, hu⟩
    apply (hsm p).congr_of_eventuallyEq
    have hbase : ∀ᶠ y' in 𝓝 p.1, ∀ v : ℂ, b66f_gen_b66m_sc_gamma R t ρ s ⟨y', v⟩ =
        b4c_dbar ℂ (b65z_fibre c₀ R.C t) u ⟨y', v⟩ := by
      filter_upwards [b66f_gen_b66m_sc_gamma_local R t ρ hρ hs b p.1 hb, hχ1.eventually_nhds]
        with y' h1 h2 v
      rw [h1 v]
      apply RiemannRochAna_dbar_congr
      filter_upwards [h2] with z hz
      simp only [u, show χ z = 1 from hz, Complex.ofReal_one, one_mul]
    have hp := (FiberBundle.continuous_proj ℂ
      (TangentSpace 𝓘(ℂ, ℂ) : b65z_fibre c₀ R.C t → Type)).continuousAt (x := p)
    filter_upwards [hp.preimage_mem_nhds hbase] with q hq
    rcases q with ⟨q1, q2⟩
    exact hq q2
  · exact RiemannRochAna_antilinear (E := ℂ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66f_gen_b66m_sc_tau R t ρ s x.val) x) a v w

theorem b66f_gen_b66m_sc_tau_finite (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R) (b : b66f_Index R) (y : b65z_fibre c₀ R.C t) :
    (Function.support fun c => ρ c y • u c b y.val.2).Finite := by
  apply (ρ.locallyFinite.point_finite y).subset
  intro c hc
  simp only [Function.mem_support] at hc ⊢
  exact fun h => hc (by rw [h, zero_smul])

theorem b66f_gen_b66m_sc_tau_add (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u v : b66f_Cochain R) (b : b66f_Index R) :
    b66f_gen_b66m_sc_tau R t ρ (u + v) b = b66f_gen_b66m_sc_tau R t ρ u b + b66f_gen_b66m_sc_tau R t ρ v b := by
  funext y
  simp only [b66f_gen_b66m_sc_tau, Pi.add_apply, smul_add]
  rw [finsum_add_distrib (b66f_gen_b66m_sc_tau_finite R t ρ u b y)
    (b66f_gen_b66m_sc_tau_finite R t ρ v b y), neg_add]

theorem b66f_gen_b66m_sc_tau_smul (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (z : ℂ) (u : b66f_Cochain R) (b : b66f_Index R) :
    b66f_gen_b66m_sc_tau R t ρ (z • u) b = z • b66f_gen_b66m_sc_tau R t ρ u b := by
  funext y
  have he : (fun c => ρ c y • (z • u c b y.val.2)) =
      fun c => z • (ρ c y • u c b y.val.2) := by
    funext c
    exact smul_comm _ _ _
  simp only [b66f_gen_b66m_sc_tau, Pi.smul_apply]
  rw [he, ← smul_finsum, smul_neg]

def b66f_gen_b66m_sc_gammaLinear (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    b66f_gen_b66g_scalarCycles R t →ₗ[ℂ] b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) where
  toFun u := ⟨b66f_gen_b66m_sc_gamma R t ρ u.val, b66f_gen_b66m_sc_gamma_mem R t ρ hρ u.property⟩
  map_add' u v := by
    apply Subtype.ext
    funext p
    rcases p with ⟨p, w⟩
    have hp := (R.atlas.hA p.val).1
    change b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ (u.val + v.val) p.val) ⟨p, w⟩ =
      b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ u.val p.val) ⟨p, w⟩ +
        b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ v.val p.val) ⟨p, w⟩
    rw [b66f_gen_b66m_sc_tau_add]
    exact RiemannRochAna_dbar_add_at _ _ p
      ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ u.property p.val p hp).mdifferentiableAt (by simp))
      ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ v.property p.val p hp).mdifferentiableAt (by simp)) w
  map_smul' z u := by
    apply Subtype.ext
    funext p
    rcases p with ⟨p, w⟩
    have hp := (R.atlas.hA p.val).1
    change b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ (z • u.val) p.val) ⟨p, w⟩ =
      z * b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ u.val p.val) ⟨p, w⟩
    rw [b66f_gen_b66m_sc_tau_smul]
    exact RiemannRochAna_dbar_smul_at z _ p
      ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ u.property p.val p hp).mdifferentiableAt (by simp)) w

def b66f_gen_b66m_sc_classLinear (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    b66f_gen_b66g_scalarCycles R t →ₗ[ℂ] b4c_Dolbeault01 ℂ (b65z_fibre c₀ R.C t) :=
  (Submodule.mkQ _).comp (b66f_gen_b66m_sc_gammaLinear R t ρ hρ)

theorem b66f_gen_b66m_sc_cechProjection_surjective (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Function.Surjective (b66f_gen_b66m_sc_cechProjection R t) := by
  intro c
  obtain ⟨u, hu, he⟩ := c.property
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

theorem b66f_gen_b66m_sc_dbar_of_boundary (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66f_domain R t a))
    (hu : b66f_gen_b66g_scalarBoundary R t v ∈ b66f_gen_b66g_scalarCycles R t) :
    ∃ F : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t),
      b4c_dbar ℂ (b65z_fibre c₀ R.C t) F =
        b66f_gen_b66m_sc_gamma R t ρ (b66f_gen_b66g_scalarBoundary R t v) := by
  let u := b66f_gen_b66g_scalarBoundary R t v
  let V := fun a (y : b65z_fibre c₀ R.C t) => v a (b66f_gen_b66m_sc_slice R t a y)
  let H := fun y : b65z_fibre c₀ R.C t => b66f_gen_b66m_sc_tau R t ρ u y.val y - V y.val y
  have hV (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (V a) y :=
    ((hv a _ (b66f_gen_b66m_sc_slice_domain R t a y hy)).contDiffAt.contMDiffAt).comp y
      (b66f_gen_b66m_sc_slice_contMDiffAt R t a y hy)
  have hloc (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      H =ᶠ[𝓝 y] b66f_gen_b66m_sc_tau R t ρ u a - V a := by
    filter_upwards [(b66f_gen_b66m_sc_open_source R t a).mem_nhds hy] with z hz
    have hb := (R.atlas.hA z.val).1
    have hba : (t, z.val.2) ∈ (R.atlas.A z.val).source ∩ (R.atlas.A a).source := by
      rw [← b66f_gen_b66m_sc_fibre_val R t z]
      exact ⟨hb, hz⟩
    have ht := b66f_gen_b66m_sc_tau_sub R t ρ hρ hu z.val a z hb hz
    change b66f_gen_b66m_sc_tau R t ρ u z.val z - b66f_gen_b66m_sc_tau R t ρ u a z =
      b66f_gen_b66g_scalarBoundary R t v z.val a z.val.2 at ht
    rw [b66f_gen_b66g_scalarBoundary, ite_eq_left hba, ← b66f_gen_b66m_sc_fibre_val R t z] at ht
    dsimp only [H, V, b66f_gen_b66m_sc_slice, Pi.sub_apply]
    linear_combination ht
  have hH : H ∈ b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) := by
    intro y
    have hy := (R.atlas.hA y.val).1
    apply ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu y.val y hy).sub
      ((b3A_contMDiffWithinAt_real (hV y.val y hy)).of_le (by simp))).congr_of_eventuallyEq
    exact hloc y.val y hy
  refine ⟨⟨H, hH⟩, ?_⟩
  funext p
  rcases p with ⟨y, w⟩
  have hy := (R.atlas.hA y.val).1
  change b4c_dbar ℂ (b65z_fibre c₀ R.C t) H ⟨y, w⟩ =
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_sc_tau R t ρ u y.val) ⟨y, w⟩
  rw [RiemannRochAna_dbar_congr (E := ℂ) (hloc y.val y hy) w,
    RiemannRochAna_dbar_sub_at _ _ y
      ((b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu y.val y hy).mdifferentiableAt (by simp))
      ((b3A_contMDiffWithinAt_real (hV y.val y hy)).mdifferentiableWithinAt
        (by simp) |>.mdifferentiableAt Filter.univ_mem) w,
    RiemannRochAna_dbar_holomorphic_at _ y ((hV y.val y hy).mdifferentiableAt (by simp)) w,
    sub_zero]

theorem b66f_gen_b66g_vertical_comp (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b c : b66f_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66f_vertical R t a c x = b66f_vertical R t b c x * b66f_vertical R t a b x := by
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
  have dab := (b66f_gen_b66k_transition_analytic R a b u hab).differentiableAt
  have dbc := (b66f_gen_b66k_transition_analytic R b c w hbc).differentiableAt
  let T : ((Fin 10 → ℂ) × ℂ) → ((Fin 10 → ℂ) × ℂ) :=
    fun v => (v.1, b66f_transition R a b v)
  have hT : T u = w := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam b _ hb).symm
    · exact congrArg (fun y => (R.atlas.A b y).2) ((R.atlas.A a).left_inv ha)
  have he : (fun v => b66f_transition R b c (T v)) =ᶠ[𝓝 u]
      b66f_transition R a c := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hab]
      with v hv
    have ht : T v = R.atlas.A b ((R.atlas.A a).symm v) := by
      apply Prod.ext
      · exact (b6a_transition_fst c₀ R.C R.atlas.A R.atlas.hparam a b v hv).symm
      · rfl
    change (R.atlas.A c ((R.atlas.A b).symm (T v))).2 = _
    rw [ht]
    rw [(R.atlas.A b).left_inv (x := (R.atlas.A a).symm v) hv.2]
    rfl
  have dbc' : HasFDerivAt (b66f_transition R b c)
      (fderiv ℂ (b66f_transition R b c) w) (T u) := by
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
  simp only [b66f_vertical]
  change fderiv ℂ (b66f_transition R a c) u (0, 1) = _
  rw [hf]
  change fderiv ℂ (b66f_transition R b c) w
    (0, fderiv ℂ (b66f_transition R a b) u (0, 1)) = _
  rw [hl, mul_comm]

theorem b66f_gen_b66g_boundaries_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66k_boundaries R t ≤
      b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t) ∧
    b66f_gen_b66g_scalarBoundaries R t ≤ b66f_gen_b66g_scalarCycles R t := by
  constructor
  · refine Submodule.span_le.mpr ?_
    rintro c ⟨v, hv, rfl⟩
    constructor
    · apply Submodule.subset_span
      refine ⟨?_, ?_⟩
      · intro a b z hz
        obtain ⟨_, hdom, han, hvert⟩ := b66f_gen_b66g_transition_mem R t a b z hz
        have h1 : AnalyticAt ℂ (fun w =>
            fderiv ℂ (b66f_transition R a b) (t.val, w) (0, 1) * v a w -
              v b (b66f_transition R a b (t.val, w))) z :=
          (hvert.mul (hv a z hz.1)).sub (AnalyticAt.comp (f := fun w =>
            b66f_transition R a b (t.val, w)) (hv b _ hdom) han)
        apply h1.congr
        filter_upwards [b66f_gen_b66g_overlap_eventually R t a b z hz] with w ⟨hmem, ha, hb⟩
        simp only [b66f_boundary, ite_eq_left hmem, b66f_vertical, ha, hb]
      · intro a b x hx
        simp only [b66f_boundary, ite_eq_right hx]
    · change b66f_gen_b66k_differential R t (b66f_boundary R t v) = 0
      funext a b c x
      simp only [b66f_gen_b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      split_ifs with hx
      · simp only [b66f_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
            (R.atlas.A c).source from ⟨hx.1.1, hx.2⟩),
          ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩
            (R.atlas.A c).source from ⟨hx.1.2, hx.2⟩), ite_eq_left hx.1,
          b66f_gen_b66g_vertical_comp R t a b c x hx.1.1 hx.1.2 hx.2]
        ring
      · rfl
  · refine Submodule.span_le.mpr ?_
    rintro c ⟨v, hv, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_, ?_⟩
    · intro a b z hz
      obtain ⟨_, hdom, han, _⟩ := b66f_gen_b66g_transition_mem R t a b z hz
      have h1 : AnalyticAt ℂ (fun w =>
          v a w - v b (b66f_transition R a b (t.val, w))) z :=
        (hv a z hz.1).sub (AnalyticAt.comp (f := fun w =>
          b66f_transition R a b (t.val, w)) (hv b _ hdom) han)
      apply h1.congr
      filter_upwards [b66f_gen_b66g_overlap_eventually R t a b z hz] with w ⟨hmem, ha, hb⟩
      simp only [b66f_gen_b66g_scalarBoundary, ite_eq_left hmem, ha, hb]
    · intro a b x hx
      simp only [b66f_gen_b66g_scalarBoundary, ite_eq_right hx]
    · intro a b c x ha hb hc
      simp only [b66f_gen_b66g_scalarBoundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
          (R.atlas.A c).source from ⟨ha, hc⟩),
        ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩
          (R.atlas.A c).source from ⟨hb, hc⟩),
        ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
          (R.atlas.A b).source from ⟨ha, hb⟩)]
      ring

theorem b66f_gen_b66g_boundaries (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66k_boundaries R t ≤
      b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t) ∧
    b66f_gen_b66g_scalarBoundaries R t ≤ b66f_gen_b66g_scalarCycles R t :=
  b66f_gen_b66g_boundaries_aux R t

example := @b66f_gen_b66g_boundaries

theorem b66f_gen_b66m_sc_class_of_boundary (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (hb : u ∈ b66f_gen_b66g_scalarBoundaries R t) :
    b66f_gen_b66m_sc_classLinear R t ρ hρ ⟨u, hu⟩ = 0 := by
  revert hu
  induction hb using Submodule.span_induction with
  | mem u h =>
    intro hu
    rcases h with ⟨v, hv, rfl⟩
    obtain ⟨F, hF⟩ := b66f_gen_b66m_sc_dbar_of_boundary R t ρ hρ v hv hu
    exact (RiemannRochAna_class_eq_zero_iff (Module.finrank_self ℂ) _).mpr ⟨F, hF⟩
  | zero =>
    intro hu
    exact map_zero _
  | add u v hu hv ihu ihv =>
    intro huv
    have huc := (b66f_gen_b66g_boundaries R t).2 hu
    have hvc := (b66f_gen_b66g_boundaries R t).2 hv
    change b66f_gen_b66m_sc_classLinear R t ρ hρ (⟨u, huc⟩ + ⟨v, hvc⟩) = 0
    rw [map_add, ihu huc, ihv hvc, add_zero]
  | smul z u hu ihu =>
    intro hzu
    have huc := (b66f_gen_b66g_boundaries R t).2 hu
    change b66f_gen_b66m_sc_classLinear R t ρ hρ (z • ⟨u, huc⟩) = 0
    rw [map_smul, ihu huc, smul_zero]

def b66f_gen_b66m_sc_pt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) : R.C ↪ b65z_fibre c₀ R.C t where
  toFun x := ⟨(t, x), rfl⟩
  inj' _ _ hxy := congrArg (fun p : b65z_fibre c₀ R.C t => p.val.2) hxy

def b66f_gen_b66m_sc_sliceD (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (a : b66f_Index R)
    (p : b65z_fibre c₀ R.C t) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66m_sc_slice R t a) p

def b66f_gen_b66m_sc_chartD (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (x₀ y : b65z_fibre c₀ R.C t) :
    ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x₀) y

theorem b66f_gen_b66m_sc_slice_chart (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (x₀ y : b65z_fibre c₀ R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (hya : y.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (b66f_gen_b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ∧
    deriv (b66f_gen_b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ≠ 0 ∧
    ∀ v : ℂ, b66f_gen_b66m_sc_sliceD R t a y v =
      deriv (b66f_gen_b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
        (extChartAt 𝓘(ℂ, ℂ) x₀ y) * b66f_gen_b66m_sc_chartD R t x₀ y v := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set h := b66f_gen_b66m_sc_slice R t a ∘ e.symm
  have hyt : e y ∈ e.target := e.map_source hy
  have hinv : e.symm (e y) = y := e.left_inv hy
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y) :=
    (contMDiffOn_extChartAt_symm x₀ (e y) hyt).contMDiffAt
      (extChartAt_target_mem_nhds' hyt)
  have hsl : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66f_gen_b66m_sc_slice R t a) (e.symm (e y)) := by
    rw [hinv]
    exact b66f_gen_b66m_sc_slice_contMDiffAt R t a y hya
  have hh : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω h (e y) := hsl.comp (e y) hsym
  have han : AnalyticAt ℂ h (e y) := (contMDiffAt_iff_contDiffAt.mp hh).analyticAt
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y) := by
    refine inter_mem (extChartAt_target_mem_nhds' hyt) ?_
    apply (continuousAt_extChartAt_symm'' hyt).preimage_mem_nhds
    rw [hinv]
    exact hopen.mem_nhds hya
  have hinj : InjOn h (e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source}) := by
    intro w₁ hw₁ w₂ hw₂ hw
    have h1 := b66f_gen_b66m_sc_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66f_gen_b66m_sc_slice_value R t a (e.symm w₂) hw₂.2
    have hv : (e.symm w₁).val = (e.symm w₂).val := by
      apply (R.atlas.A a).injOn hw₁.2 hw₂.2
      rw [h1, h2]
      exact congrArg (fun z => (t.val, z)) hw
    have hy' : e.symm w₁ = e.symm w₂ := Subtype.ext hv
    rw [← e.right_inv hw₁.1, ← e.right_inv hw₂.1, hy']
  refine ⟨han, rf8_deriv_ne_zero_of_injOn hU han hinj, fun v => ?_⟩
  have heq : b66f_gen_b66m_sc_slice R t a =ᶠ[𝓝 y] h ∘ e := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy'
    simp only [h, Function.comp_apply, e.left_inv hy']
  have hmd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) h (e y) :=
    mdifferentiableAt_iff_differentiableAt.mpr han.differentiableAt
  have hme : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℂ, ℂ)])
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66m_sc_slice R t a) y
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv h (e y))).comp
        (b66f_gen_b66m_sc_chartD R t x₀ y)) :=
    (HasMFDerivAt.comp (g := h) (f := e) y
      han.differentiableAt.hasDerivAt.hasFDerivAt.hasMFDerivAt
      hme.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66f_gen_b66m_sc_sliceD
  rw [hH.mfderiv]
  exact mul_comm (b66f_gen_b66m_sc_chartD R t x₀ y v) _

theorem b66f_gen_b66m_sc_fibre_mk (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (p : b65z_fibre c₀ R.C t) : (⟨(t, p.val.2), rfl⟩ : b65z_fibre c₀ R.C t) = p :=
  Subtype.ext (b66f_gen_b66m_sc_fibre_val R t p).symm

theorem b66f_gen_b66m_sc_coord_analytic (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (H : b65z_fibre c₀ R.C t → ℂ) (a : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_domain R t a)
    (hH : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω H (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2)) :
    AnalyticAt ℂ (fun w => H (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z := by
  set y₀ := b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2
  have hy₀v : y₀.val = (R.atlas.A a).symm (t.val, z) := b66f_gen_b66k_inverse_slice R t a z hz
  have hy₀a : y₀.val ∈ (R.atlas.A a).source := by
    rw [hy₀v]
    exact (R.atlas.A a).map_target hz
  set e := extChartAt 𝓘(ℂ, ℂ) y₀
  set h := b66f_gen_b66m_sc_slice R t a ∘ e.symm
  obtain ⟨han, hder, _⟩ := b66f_gen_b66m_sc_slice_chart R t a y₀ y₀ (mem_extChartAt_source y₀) hy₀a
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
    exact (b66f_gen_b66m_sc_open_source R t a).mem_nhds hy₀a
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
  rw [b66f_gen_b66m_sc_inv_slice R t a (e.symm w) hw.2]
  exact congrArg H (b66f_gen_b66m_sc_fibre_mk R t (e.symm w)).symm

theorem b66f_gen_b66m_sc_boundary_of_dbar (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (F : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t))
    (hF : b4c_dbar ℂ (b65z_fibre c₀ R.C t) F = b66f_gen_b66m_sc_gamma R t ρ u) :
    u ∈ b66f_gen_b66g_scalarBoundaries R t := by
  let H := fun a => b66f_gen_b66m_sc_tau R t ρ u a - (F : b65z_fibre c₀ R.C t → ℂ)
  have hH (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (H a) y := by
    apply RiemannRochAna_analyticAt_of_dbar_germ (Module.finrank_self ℂ) (H a) y
    filter_upwards [(b66f_gen_b66m_sc_open_source R t a).mem_nhds hy] with y' hy'
    have hτ := b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a y' hy'
    refine ⟨hτ.sub (F.property y'), fun w => ?_⟩
    rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
      ((F.property y').mdifferentiableAt (by simp)) w, hF,
      ← (b66f_gen_b66m_sc_gamma_local R t ρ hρ hu a y' hy').self_of_nhds w, sub_self]
  let v := fun a z => H a (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2)
  have hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66f_domain R t a) := by
    intro a z hz
    apply b66f_gen_b66m_sc_coord_analytic R t (H a) a z hz
    apply hH
    change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
    rw [b66f_gen_b66k_inverse_slice R t a z hz]
    exact (R.atlas.A a).map_target hz
  apply Submodule.subset_span
  refine ⟨v, hv, ?_⟩
  funext a b x
  by_cases hx : (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source
  · rw [b66f_gen_b66g_scalarBoundary, ite_eq_left hx]
    change u a b x =
      H a (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm
        (t.val, (R.atlas.A a (t, x)).2)).2) -
      H b (b66f_gen_b66m_sc_pt R t ((R.atlas.A b).symm
        (t.val, (R.atlas.A b (t, x)).2)).2)
    have hia := b66f_gen_b66m_sc_inv_slice R t a (b66f_gen_b66m_sc_pt R t x) hx.1
    have hib := b66f_gen_b66m_sc_inv_slice R t b (b66f_gen_b66m_sc_pt R t x) hx.2
    change ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2 = x at hia
    change ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x at hib
    rw [hia, hib]
    have ht := b66f_gen_b66m_sc_tau_sub R t ρ hρ hu a b (b66f_gen_b66m_sc_pt R t x) hx.1 hx.2
    change b66f_gen_b66m_sc_tau R t ρ u a (b66f_gen_b66m_sc_pt R t x) -
      b66f_gen_b66m_sc_tau R t ρ u b (b66f_gen_b66m_sc_pt R t x) = u a b x at ht
    dsimp only [H, Pi.sub_apply]
    linear_combination -ht
  · rw [(b66f_gen_b66m_sc_scalarCycles_spec R t hu).2.1 a b x hx,
      b66f_gen_b66g_scalarBoundary, ite_eq_right hx]

theorem b66f_gen_b66m_sc_kernel_eq (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    LinearMap.ker (b66f_gen_b66m_sc_cechProjection R t) =
      LinearMap.ker (b66f_gen_b66m_sc_classLinear R t ρ hρ) := by
  ext u
  constructor
  · intro hu
    have hx := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
    change ((b66f_gen_b66g_scalarBoundaries R t).mkQ u.val) = 0 at hx
    exact LinearMap.mem_ker.mpr (b66f_gen_b66m_sc_class_of_boundary R t ρ hρ u.val u.property
      ((Submodule.Quotient.mk_eq_zero (b66f_gen_b66g_scalarBoundaries R t)).mp hx))
  · intro hu
    have hx := LinearMap.mem_ker.mp hu
    change (Submodule.Quotient.mk (b66f_gen_b66m_sc_gammaLinear R t ρ hρ u) :
      b4c_Dolbeault01 ℂ (b65z_fibre c₀ R.C t)) = 0 at hx
    obtain ⟨F, hF⟩ := (RiemannRochAna_class_eq_zero_iff (Module.finrank_self ℂ) _).mp hx
    have hb := b66f_gen_b66m_sc_boundary_of_dbar R t ρ hρ u.val u.property F hF
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero (b66f_gen_b66g_scalarBoundaries R t)).mpr hb

theorem b66f_gen_b66m_sc_comparison (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    ∃ E : b66f_gen_b66g_H1O R t →ₗ[ℂ] b4c_Dolbeault01 ℂ (b65z_fibre c₀ R.C t),
      Function.Injective E ∧
      ∀ u, E (b66f_gen_b66m_sc_cechProjection R t u) = b66f_gen_b66m_sc_classLinear R t ρ hρ u := by
  let f := b66f_gen_b66m_sc_cechProjection R t
  let g := b66f_gen_b66m_sc_classLinear R t ρ hρ
  have hf := b66f_gen_b66m_sc_cechProjection_surjective R t
  have hk := b66f_gen_b66m_sc_kernel_eq R t ρ hρ
  let E := f.liftOfSurjective hf ⟨g, hk.le⟩
  have hE (u) : E (f u) = g u := LinearMap.equivOfSurjective_apply hf hk.le
  have hi : Function.Injective E := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := hf x
    obtain ⟨v, rfl⟩ := hf y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LinearMap.mem_ker.mp
    rw [hk]
    change g (u - v) = 0
    rw [map_sub, ← hE, ← hE, hxy, sub_self]
  exact ⟨E, hi, hE⟩

end HodgeLean.Foundations.Program
