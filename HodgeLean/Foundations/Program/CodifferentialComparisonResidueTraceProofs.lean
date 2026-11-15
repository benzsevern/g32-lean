import HodgeLean.Foundations.Program.CodifferentialComparisonTracePairingProofs
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

def b66f_gen_b66m_localPoleProduct (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (a : b66f_Index R)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (q : b65z_fibre c₀ R.C t) (z : ℂ) : ℂ :=
  v a (b66f_gen_b66m_sc_slice R t a ((chartAt ℂ q).symm (b3Rest_ζ (Module.finrank_self ℂ) q z))) *
    θ.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
      (b3Rest_ζ (Module.finrank_self ℂ) q z))

def b66f_gen_b66m_integrationSlice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (q : b65z_fibre c₀ R.C t) (z : ℂ) : ℂ :=
  b66f_gen_b66m_sc_slice R t a ((chartAt ℂ q).symm (b3Rest_ζ (Module.finrank_self ℂ) q z))

theorem b66f_gen_b66m_integrationSlice_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (q : b65z_fibre c₀ R.C t) (ha : q.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (b66f_gen_b66m_integrationSlice R t a q) 0 ∧
      deriv (b66f_gen_b66m_integrationSlice R t a q) 0 ≠ 0 ∧
      b66f_gen_b66m_integrationSlice R t a q 0 = b66f_gen_b66m_sc_slice R t a q := by
  obtain ⟨hhan, hhd, _⟩ := b66f_gen_b66m_sc_slice_chart R t a q q (mem_extChartAt_source q) ha
  change AnalyticAt ℂ (b66f_gen_b66m_sc_slice R t a ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) at hhan
  change deriv (b66f_gen_b66m_sc_slice R t a ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) ≠ 0 at hhd
  let e := b3Rest_e (Module.finrank_self ℂ)
  let A : ℂ → ℂ := fun z => chartAt ℂ q q + z * e
  have hA : HasDerivAt A e 0 := by
    simpa [A] using ((hasDerivAt_id (0 : ℂ)).mul_const e).const_add (chartAt ℂ q q)
  have hA0 : A 0 = chartAt ℂ q q := by simp [A]
  have han : AnalyticAt ℂ A 0 := by dsimp [A]; fun_prop
  have hh : AnalyticAt ℂ (b66f_gen_b66m_sc_slice R t a ∘ (chartAt ℂ q).symm) (A 0) := hA0.symm ▸ hhan
  have heq : b66f_gen_b66m_integrationSlice R t a q =
      (b66f_gen_b66m_sc_slice R t a ∘ (chartAt ℂ q).symm) ∘ A := by
    funext z
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact hh.comp han
  · rw [heq, (hh.differentiableAt.hasDerivAt.comp 0 hA).deriv, hA0]
    exact mul_ne_zero hhd (b3Rest_e_ne_zero (Module.finrank_self ℂ))
  · unfold b66f_gen_b66m_integrationSlice b3Rest_ζ
    rw [zero_smul, add_zero, (chartAt ℂ q).left_inv (mem_chart_source ℂ q)]

theorem b66f_gen_b66m_integrationSlice_residue (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (q : b65z_fibre c₀ R.C t) (ha : q.val ∈ (R.atlas.A a).source)
    (C : ℂ → ℂ) (hC : MeromorphicAt C (b66f_gen_b66m_sc_slice R t a q)) :
    MeromorphicAt (fun z => C (b66f_gen_b66m_integrationSlice R t a q z) *
      deriv (b66f_gen_b66m_integrationSlice R t a q) z) 0 ∧
    TauCeti.Contour.residue (fun z => C (b66f_gen_b66m_integrationSlice R t a q z) *
      deriv (b66f_gen_b66m_integrationSlice R t a q) z) 0 =
      TauCeti.Contour.residue C (b66f_gen_b66m_sc_slice R t a q) := by
  obtain ⟨hD, hn, h0⟩ := b66f_gen_b66m_integrationSlice_spec R t a q ha
  have hc : MeromorphicAt C (b66f_gen_b66m_integrationSlice R t a q 0) := h0.symm ▸ hC
  refine ⟨(hc.comp_analyticAt hD).mul hD.deriv.meromorphicAt, ?_⟩
  rw [b66m_rs_residue_comp hD hn hc, h0]

theorem b66f_gen_b66m_rs_chartD_vec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (x₀ y : b65z_fibre c₀ R.C t) (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (u : ℂ) :
    b66f_gen_b66m_sc_chartD R t x₀ y (b4cov_vec x₀ y u) = u :=
  (b4cov_triv_eq_mfderiv x₀ y hy (b4cov_vec x₀ y u)).symm.trans (b4cov_triv_vec x₀ y hy u)

theorem b66f_gen_b66m_localPoleProduct_germ (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (Q : b66f_forms R t 1)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : ∀ b (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = Q.val b p.val.2 * b66f_gen_b66m_sc_sliceD R t b p w)
    (a : b66f_Index R) (q : b65z_fibre c₀ R.C t) (ha : q.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66m_localPoleProduct R t v a θ q =ᶠ[𝓝 0] fun z =>
      (v a (b66f_gen_b66m_integrationSlice R t a q z) * Q.val a
        ((R.atlas.A a).symm (t.val, b66f_gen_b66m_integrationSlice R t a q z)).2) *
          deriv (b66f_gen_b66m_integrationSlice R t a q) z := by
  let e := chartAt ℂ q
  let c := b3Rest_e (Module.finrank_self ℂ)
  let hh := b66f_gen_b66m_sc_slice R t a ∘ e.symm
  have hqe : q ∈ e.source := mem_chart_source ℂ q
  have hex : e q ∈ e.target := e.map_source hqe
  have hsc : Tendsto (fun z : ℂ => e q + z * c) (𝓝 0) (𝓝 (e q)) := by
    have hc : Continuous (fun z : ℂ => e q + z * c) := by fun_prop
    simpa using hc.tendsto 0
  have hsym : Tendsto (fun z : ℂ => e.symm (e q + z * c)) (𝓝 0) (𝓝 q) := by
    have h := (e.continuousAt_symm hex).tendsto.comp hsc
    rwa [e.left_inv hqe] at h
  have htarget := hsc.eventually (e.open_target.mem_nhds hex)
  have hsource := hsym.eventually ((b66f_gen_b66m_sc_open_source R t a).mem_nhds ha)
  filter_upwards [htarget, hsource] with z h1 h2
  let y := e.symm (e q + z * c)
  have hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) q).source := by
    simpa only [extChartAt_source] using e.map_target h1
  have hey : e y = e q + z * c := e.right_inv h1
  obtain ⟨hyan, _, hD⟩ := b66f_gen_b66m_sc_slice_chart R t a q y hy h2
  change AnalyticAt ℂ hh (e y) at hyan
  change ∀ w : ℂ, b66f_gen_b66m_sc_sliceD R t a y w =
    deriv hh (e y) * b66f_gen_b66m_sc_chartD R t q y w at hD
  have hd : deriv (b66f_gen_b66m_integrationSlice R t a q) z = deriv hh (e q + z * c) * c := by
    rw [hey] at hyan
    have hs : HasDerivAt (fun σ : ℂ => e q + σ * c) c z := by
      simpa using ((hasDerivAt_id z).mul_const c).const_add (e q)
    change deriv (hh ∘ fun σ : ℂ => e q + σ * c) z = _
    exact (hyan.differentiableAt.hasDerivAt.comp z hs).deriv
  have hvec : b3Forms_chartVec q c (e q + z * c) = ⟨y, b4cov_vec q y c⟩ :=
    congrArg (fun w : TangentSpace 𝓘(ℂ, ℂ) y =>
      (⟨y, w⟩ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t)))
        (b4c_residue_vec_chart h1 c).symm
  have hk : b66f_gen_b66m_sc_sliceD R t a y (b4cov_vec q y c) = deriv hh (e q + z * c) * c := by
    refine (hD (b4cov_vec q y c)).trans ?_
    rw [b66f_gen_b66m_rs_chartD_vec R t q y hy, hey]
  change v a (b66f_gen_b66m_sc_slice R t a y) * θ.val (b3Forms_chartVec q c (e q + z * c)) =
    (v a (b66f_gen_b66m_sc_slice R t a y) * Q.val a
      ((R.atlas.A a).symm (t.val, b66f_gen_b66m_sc_slice R t a y)).2) *
        deriv (b66f_gen_b66m_integrationSlice R t a q) z
  rw [hvec, hθ a y h2 (b4cov_vec q y c), hk, hd, b66f_gen_b66m_sc_inv_slice R t a y h2]
  ring

theorem b66f_gen_b66m_localPoleProduct_residue (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (Q : b66f_forms R t 1)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : ∀ b (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = Q.val b p.val.2 * b66f_gen_b66m_sc_sliceD R t b p w)
    (a : b66f_Index R) (q : b65z_fibre c₀ R.C t) (ha : q.val ∈ (R.atlas.A a).source)
    (hv : MeromorphicAt (v a) (b66f_gen_b66m_sc_slice R t a q)) :
    MeromorphicAt (b66f_gen_b66m_localPoleProduct R t v a θ q) 0 ∧
      TauCeti.Contour.residue (b66f_gen_b66m_localPoleProduct R t v a θ q) 0 =
        TauCeti.Contour.residue (fun w => v a w * Q.val a
          ((R.atlas.A a).symm (t.val, w)).2) (b66f_gen_b66m_sc_slice R t a q) := by
  obtain ⟨hqa, _, _⟩ := b66f_gen_b66m_rs_forms_spec R t 1 Q.property
  have hC : MeromorphicAt (fun w => v a w * Q.val a
      ((R.atlas.A a).symm (t.val, w)).2) (b66f_gen_b66m_sc_slice R t a q) :=
    hv.mul (hqa a _ (b66f_gen_b66m_sc_slice_domain R t a q ha)).meromorphicAt
  obtain ⟨hm, hres⟩ := b66f_gen_b66m_integrationSlice_residue R t a q ha _ hC
  have hG := (b66f_gen_b66m_localPoleProduct_germ R t v Q θ hθ a q ha).filter_mono
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  refine ⟨hm.congr hG.symm, ?_⟩
  rw [TauCeti.Contour.residue_congr_nhdsNE hG]
  simpa only [Pi.mul_apply] using hres

def b66f_gen_b66m_radialCutoff (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b65z_fibre c₀ R.C t) (r : ℝ) : b65z_fibre c₀ R.C t → ℝ :=
  b3Rest_cfun (Module.finrank_self ℂ) q
    (fun z : ℂ => b4c_residue_profile (r / 4) (r / 2) ‖z‖)

theorem b66f_gen_b66m_meromorphic_integration_disc (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (q : b65z_fibre c₀ R.C t) (U : Set (b65z_fibre c₀ R.C t))
    (hU : U ∈ 𝓝 q) (G : ℂ → ℂ) (hG : MeromorphicAt G 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target ∧
      (chartAt ℂ q).symm (b3Rest_ζ (Module.finrank_self ℂ) q z) ∈ U ∧
      (z ≠ 0 → AnalyticAt ℂ G z) := by
  let e := chartAt ℂ q
  have hq : q ∈ e.source := mem_chart_source ℂ q
  have hqe : e q ∈ e.target := e.map_source hq
  have hζ : Tendsto (b3Rest_ζ (Module.finrank_self ℂ) q) (𝓝 0) (𝓝 (e q)) := by
    have hc : Continuous (b3Rest_ζ (Module.finrank_self ℂ) q) := by
      unfold b3Rest_ζ
      fun_prop
    simpa only [b3Rest_ζ, zero_smul, add_zero] using hc.tendsto 0
  have hp : Tendsto (fun z => e.symm (b3Rest_ζ (Module.finrank_self ℂ) q z))
      (𝓝 0) (𝓝 q) := by
    have h := (e.continuousAt_symm hqe).tendsto.comp hζ
    rwa [e.left_inv hq] at h
  have hA : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → AnalyticAt ℂ G z := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] using hG.eventually_analyticAt
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ),
      b3Rest_ζ (Module.finrank_self ℂ) q z ∈ e.target ∧
      e.symm (b3Rest_ζ (Module.finrank_self ℂ) q z) ∈ U ∧
      (z ≠ 0 → AnalyticAt ℂ G z) :=
    (hζ.eventually (e.open_target.mem_nhds hqe)).and ((hp.eventually hU).and hA)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  exact ⟨r, hr, fun z hz => hball (by simpa only [dist_zero_right] using hz)⟩

theorem b66f_gen_b66m_radialCutoff_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b65z_fibre c₀ R.C t) (r : ℝ) (hr : 0 < r)
    (hchart : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (b66f_gen_b66m_radialCutoff R t q r) ∧
      b66f_gen_b66m_radialCutoff R t q r =ᶠ[𝓝 q] 1 ∧
      tsupport (b66f_gen_b66m_radialCutoff R t q r) ⊆ b3Rest_reg (Module.finrank_self ℂ) q r := by
  have ha : 0 < r / 4 := by linarith
  have hab : r / 4 < r / 2 := by linarith
  let g : ℂ → ℝ := fun z => b4c_residue_profile (r / 4) (r / 2) ‖z‖
  have hg : ContDiff ℝ ∞ g := b4c_residue_profile_radial_smooth ha hab
  have hgc : HasCompactSupport g := b4c_residue_profile_radial_compact hab
  have hgr : tsupport g ⊆ Metric.ball 0 r := by
    intro z hz
    have hn : ‖z‖ ≤ r / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        b4c_residue_profile_radial_support hab hz
    exact mem_ball_zero_iff.mpr (by linarith)
  have hgs : ∀ z ∈ tsupport g, b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target :=
    fun z hz => hchart z (mem_ball_zero_iff.mp (hgr hz))
  have hsm := b3Rest_smoothFun_cfun (Module.finrank_self ℂ) q hg hgc hgs
  refine ⟨RiemannRochAna_contMDiff_of_smooth_fun hsm, ?_,
    b3Rest_tsupport_cfun_reg (Module.finrank_self ℂ) q hgc hgr hchart⟩
  have hc : ContinuousAt (fun y : b65z_fibre c₀ R.C t =>
      (b3Rest_L (Module.finrank_self ℂ)).symm (chartAt ℂ q y - chartAt ℂ q q)) q :=
    (b3Rest_L (Module.finrank_self ℂ)).symm.continuous.continuousAt.comp
      (((chartAt ℂ q).continuousOn.continuousAt
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))).sub continuousAt_const)
  have ht : Tendsto (fun y : b65z_fibre c₀ R.C t =>
      (b3Rest_L (Module.finrank_self ℂ)).symm (chartAt ℂ q y - chartAt ℂ q q))
      (𝓝 q) (𝓝 0) := by simpa only [sub_self, map_zero] using hc.tendsto
  filter_upwards [(chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q),
    ht.eventually (b4c_residue_profile_radial_one ha hab)] with y hy h1
  change b3Rest_cfun (Module.finrank_self ℂ) q g y = 1
  rw [b3Rest_cfun, if_pos hy]
  exact h1

def b66f_gen_b66m_poleCorrection (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (a : b66f_Index R)
    (χ : b65z_fibre c₀ R.C t → ℝ) : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ :=
  fun p => v a (b66f_gen_b66m_sc_slice R t a p.1) *
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ z : ℂ)) p

theorem b66f_gen_b66m_splitting_holomorphic_off_poles (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
    (hy : y.val.2 ∉ S) (ha : y.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : b65z_fibre c₀ R.C t => v a (b66f_gen_b66m_sc_slice R t a z)) y := by
  have hv := hr a (b66f_gen_b66m_sc_slice R t a y) (b66f_gen_b66m_sc_slice_domain R t a y ha)
    (by rwa [b66f_gen_b66m_sc_inv_slice R t a y ha])
  exact hv.contDiffAt.contMDiffAt.comp y (b66f_gen_b66m_sc_slice_contMDiffAt R t a y ha)

theorem b66f_gen_b66m_poleCorrection_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (a : b66f_Index R) (χ : b65z_fibre c₀ R.C t → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ {y | y.val ∈ (R.atlas.A a).source})
    (hc : ∀ y : b65z_fibre c₀ R.C t, y.val.2 ∈ S → ∃ c : ℝ, χ =ᶠ[𝓝 y] fun _ => c) :
    b66f_gen_b66m_poleCorrection R t v a χ ∈ b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) := by
  let f : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) :=
    ⟨fun z => (χ z : ℂ), Complex.ofRealCLM.contMDiff.comp hχ⟩
  have hd := b4c_dbar_mem_aux f
  refine ⟨fun p => ?_, fun y c z w => ?_⟩
  · have hzero (c : ℝ) (hconst : χ =ᶠ[𝓝 p.1] fun _ => c) :
        ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ (b66f_gen_b66m_poleCorrection R t v a χ) p := by
      have hC : (fun z => (χ z : ℂ)) =ᶠ[𝓝 p.1] fun _ => (c : ℂ) :=
        hconst.mono (fun z hz => congrArg Complex.ofReal hz)
      have hz := RiemannRochAna_dbar_eventually_zero (E := ℂ) hC
      have hp := (FiberBundle.continuous_proj ℂ
        (TangentSpace 𝓘(ℂ, ℂ) : b65z_fibre c₀ R.C t → Type)).continuousAt (x := p)
      apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hp.preimage_mem_nhds hz] with q hq
      exact mul_eq_zero.mpr (Or.inr (hq q.2))
    by_cases hy : p.1.val.2 ∈ S
    · obtain ⟨c, hc⟩ := hc p.1 hy
      exact hzero c hc
    by_cases hm : p.1 ∈ tsupport χ
    · have hV := b66f_gen_b66m_splitting_holomorphic_off_poles R t S v hr a p.1 hy (hs hm)
      have hVr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (fun y => v a (b66f_gen_b66m_sc_slice R t a y)) p.1 :=
        (b3A_contMDiffWithinAt_real hV).of_le (by simp)
      exact (hVr.comp p RiemannRochAna_projection_smooth.contMDiffAt).mul (hd.1 p)
    · exact hzero 0 (notMem_tsupport_iff_eventuallyEq.mp hm)
  · have hh := hd.2 y c z w
    change b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun y => (χ y : ℂ)) ⟨y, c • z + w⟩ = _ at hh
    unfold b66f_gen_b66m_poleCorrection
    rw [hh]
    ring

theorem b66f_gen_b66m_pole_cutoff_constant (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (h1 : ∀ i, χ i =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)] 1)
    (hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i))
    (i : S) (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∈ S) :
    ∃ c : ℝ, χ i =ᶠ[𝓝 y] fun _ => c := by
  let j : S := ⟨y.val.2, hy⟩
  have hp : b66f_gen_b66m_sc_pt R t j.val = y := b66f_gen_b66m_sc_fibre_mk R t y
  by_cases heq : j = i
  · refine ⟨1, ?_⟩
    have hpi : b66f_gen_b66m_sc_pt R t i.val = y := by rwa [← heq]
    have h := h1 i
    rw [hpi] at h
    filter_upwards [h] with z hz
    simpa only [Pi.one_apply] using hz
  · refine ⟨0, ?_⟩
    rw [← hp]
    exact notMem_tsupport_iff_eventuallyEq.mp (hsep i j heq)

def b66f_gen_b66m_tracePotential (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R) (v : b66f_Index R → ℂ → ℂ) : b65z_fibre c₀ R.C t → ℂ :=
  fun y => b66f_gen_b66m_sc_tau R t ρ u y.val y - v y.val (b66f_gen_b66m_sc_slice R t y.val y)

def b66f_gen_b66m_traceRegularization (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R) (v : b66f_Index R → ℂ → ℂ) (S : Finset R.C)
    (χ : S → b65z_fibre c₀ R.C t → ℝ) : b65z_fibre c₀ R.C t → ℂ :=
  fun y => ((1 - ∑ i, χ i y : ℝ) : ℂ) * b66f_gen_b66m_tracePotential R t ρ u v y +
    ∑ i : S, (χ i y : ℂ) * b66f_gen_b66m_sc_tau R t ρ u (t, i.val) y

theorem b66f_gen_b66m_tracePotential_local (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
    (hy : y.val.2 ∉ S) (ha : y.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66m_tracePotential R t ρ u v y =
      b66f_gen_b66m_sc_tau R t ρ u a y - v a (b66f_gen_b66m_sc_slice R t a y) := by
  have hb := (R.atlas.hA y.val).1
  have hba : (t, y.val.2) ∈ (R.atlas.A y.val).source ∩ (R.atlas.A a).source := by
    rw [← b66f_gen_b66m_sc_fibre_val R t y]
    exact ⟨hb, ha⟩
  have ht := b66f_gen_b66m_sc_tau_sub R t ρ hρ hu y.val a y hb ha
  rw [hv y.val a y.val.2 hy hba.1 hba.2, b66f_gen_b66g_scalarBoundary,
    ite_eq_left hba, ← b66f_gen_b66m_sc_fibre_val R t y] at ht
  dsimp only [b66f_gen_b66m_tracePotential, b66f_gen_b66m_sc_slice]
  linear_combination ht

theorem b66f_gen_b66m_tracePotential_germ (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t)
    (hy : y.val.2 ∉ S) (ha : y.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66m_tracePotential R t ρ u v =ᶠ[𝓝 y]
      b66f_gen_b66m_sc_tau R t ρ u a - fun z => v a (b66f_gen_b66m_sc_slice R t a z) := by
  have hopen : IsOpen {z : b65z_fibre c₀ R.C t | z.val.2 ∉ S} :=
    S.finite_toSet.isClosed.isOpen_compl.preimage (continuous_snd.comp continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hy, (b66f_gen_b66m_sc_open_source R t a).mem_nhds ha]
    with z hz hza
  exact b66f_gen_b66m_tracePotential_local R t ρ hρ u hu S v hv a z hz hza

theorem b66f_gen_b66m_tracePotential_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66f_gen_b66m_tracePotential R t ρ u v) y := by
  have ha := (R.atlas.hA y.val).1
  have ht := b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu y.val y ha
  have hV := b66f_gen_b66m_splitting_holomorphic_off_poles R t S v hr y.val y hy ha
  apply (ht.sub ((b3A_contMDiffWithinAt_real hV).of_le (by simp))).congr_of_eventuallyEq
  exact b66f_gen_b66m_tracePotential_germ R t ρ hρ u hu S v hv y.val y hy ha

theorem b66f_gen_b66m_tracePotential_cutoff_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : b65z_fibre c₀ R.C t → ℝ) (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ)
    (hz : ∀ y : b65z_fibre c₀ R.C t, y.val.2 ∈ S → χ =ᶠ[𝓝 y] 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y => (χ y : ℂ) * b66f_gen_b66m_tracePotential R t ρ u v y) := by
  intro y
  by_cases hy : y.val.2 ∈ S
  · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz y hy] with z hz'
    simp only [Pi.zero_apply] at hz'
    simp [hz']
  · exact (Complex.ofRealCLM.contMDiff.comp hχ).contMDiffAt.mul
      (b66f_gen_b66m_tracePotential_smooth R t ρ hρ u hu S v hr hv y hy)

theorem b66f_gen_b66m_cutoff_tau_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t) (a : b66f_Index R)
    (χ : b65z_fibre c₀ R.C t → ℝ) (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ {y | y.val ∈ (R.atlas.A a).source}) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y => (χ y : ℂ) * b66f_gen_b66m_sc_tau R t ρ u a y) := by
  intro y
  by_cases hy : y ∈ tsupport χ
  · exact (Complex.ofRealCLM.contMDiff.comp hχ).contMDiffAt.mul
      (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a y (hs hy))
  · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]

theorem b66f_gen_b66m_traceRegularization_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hχ : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (hz : ∀ y : b65z_fibre c₀ R.C t, y.val.2 ∈ S →
      (fun z => 1 - ∑ i, χ i z) =ᶠ[𝓝 y] 0) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66f_gen_b66m_traceRegularization R t ρ u v S χ) := by
  have hcut : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun y => 1 - ∑ i, χ i y) :=
    contMDiff_const.sub (ContMDiff.sum fun i _ => hχ i)
  exact (b66f_gen_b66m_tracePotential_cutoff_smooth R t ρ hρ u hu S v hr hv _ hcut hz).add
    (ContMDiff.sum fun i _ => b66f_gen_b66m_cutoff_tau_smooth R t ρ hρ u hu (t, i.val)
      (χ i) (hχ i) (hs i))

theorem b66f_gen_b66m_pole_cutoff_complement (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (h1 : ∀ i, χ i =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)] 1)
    (hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i)) :
    ∀ y : b65z_fibre c₀ R.C t, y.val.2 ∈ S →
      (fun z => 1 - ∑ i, χ i z) =ᶠ[𝓝 y] 0 := by
  intro y hy
  let i : S := ⟨y.val.2, hy⟩
  have hp : b66f_gen_b66m_sc_pt R t i.val = y := b66f_gen_b66m_sc_fibre_mk R t y
  have hterm (j : S) : ∀ᶠ z in 𝓝 y, χ j z = if j = i then 1 else 0 := by
    by_cases hj : j = i
    · subst j
      have h := h1 i
      rw [hp] at h
      filter_upwards [h] with z hz
      simpa only [Pi.one_apply, ite_true] using hz
    · have h0 : χ j =ᶠ[𝓝 y] 0 := by
        rw [← hp]
        exact notMem_tsupport_iff_eventuallyEq.mp (hsep j i (Ne.symm hj))
      filter_upwards [h0] with z hz
      simpa only [if_neg hj, Pi.zero_apply] using hz
  filter_upwards [Filter.eventually_all.mpr hterm] with z hz
  simp only [hz]
  simp

theorem b66f_gen_b66m_traceRegularization_pole_germ (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R) (v : b66f_Index R → ℂ → ℂ) (S : Finset R.C)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (h1 : ∀ i, χ i =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)] 1)
    (hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i)) (i : S) :
    b66f_gen_b66m_traceRegularization R t ρ u v S χ =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)]
      b66f_gen_b66m_sc_tau R t ρ u (t, i.val) := by
  have hterm (j : S) : ∀ᶠ z in 𝓝 (b66f_gen_b66m_sc_pt R t i.val),
      χ j z = if j = i then 1 else 0 := by
    by_cases hj : j = i
    · subst j
      filter_upwards [h1 i] with z hz
      simpa only [Pi.one_apply, ite_true] using hz
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (hsep j i (Ne.symm hj))]
        with z hz
      simpa only [if_neg hj, Pi.zero_apply] using hz
  filter_upwards [Filter.eventually_all.mpr hterm] with z hz
  unfold b66f_gen_b66m_traceRegularization
  simp [hz, apply_ite, ite_mul]

theorem b66f_gen_b66m_cutoff_split_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (a : b66f_Index R) (χ : b65z_fibre c₀ R.C t → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ {y | y.val ∈ (R.atlas.A a).source})
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun z => (χ z : ℂ) * v a (b66f_gen_b66m_sc_slice R t a z)) y ∧
    ∀ w : ℂ, b4c_dbar ℂ (b65z_fibre c₀ R.C t)
      (fun z => (χ z : ℂ) * v a (b66f_gen_b66m_sc_slice R t a z)) ⟨y, w⟩ =
      v a (b66f_gen_b66m_sc_slice R t a y) *
        b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ z : ℂ)) ⟨y, w⟩ := by
  have hχC := Complex.ofRealCLM.contMDiff.comp hχ
  by_cases hm : y ∈ tsupport χ
  · have hV := b66f_gen_b66m_splitting_holomorphic_off_poles R t S v hr a y hy (hs hm)
    have hVr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun z => v a (b66f_gen_b66m_sc_slice R t a z)) y :=
      (b3A_contMDiffWithinAt_real hV).of_le (by simp)
    refine ⟨hχC.contMDiffAt.mul hVr, fun w => ?_⟩
    rw [RiemannRochAna_dbar_mul_at (fun z => (χ z : ℂ))
      (fun z => v a (b66f_gen_b66m_sc_slice R t a z)) y (hχC.mdifferentiable (by simp) y)
      (hVr.mdifferentiableAt (by simp)) w,
      RiemannRochAna_dbar_holomorphic_at _ y (hV.mdifferentiableAt (by simp)) w,
      mul_zero, zero_add]
  · have hzero : (fun z => (χ z : ℂ)) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hm] with z hz
      change (χ z : ℂ) = 0
      rw [show χ z = 0 from hz, Complex.ofReal_zero]
    have hprod : (fun z => (χ z : ℂ) * v a (b66f_gen_b66m_sc_slice R t a z)) =ᶠ[𝓝 y]
        fun _ => 0 := by
      filter_upwards [hzero] with z hz
      change (χ z : ℂ) * v a (b66f_gen_b66m_sc_slice R t a z) = 0
      rw [show (χ z : ℂ) = 0 from hz, zero_mul]
    refine ⟨contMDiffAt_const.congr_of_eventuallyEq hprod, fun w => ?_⟩
    rw [RiemannRochAna_dbar_const_germ hprod w,
      RiemannRochAna_dbar_const_germ hzero w, mul_zero]

theorem b66f_gen_b66m_traceRegularization_value (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) :
    b66f_gen_b66m_traceRegularization R t ρ u v S χ y = b66f_gen_b66m_tracePotential R t ρ u v y +
      ∑ i : S, (χ i y : ℂ) * v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) y) := by
  have hterm (i : S) : (χ i y : ℂ) * b66f_gen_b66m_sc_tau R t ρ u (t, i.val) y =
      (χ i y : ℂ) * b66f_gen_b66m_tracePotential R t ρ u v y +
        (χ i y : ℂ) * v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) y) := by
    by_cases hz : χ i y = 0
    · simp [hz]
    · have hys := hs i (subset_tsupport _ (Function.mem_support.mpr hz))
      rw [b66f_gen_b66m_tracePotential_local R t ρ hρ u hu S v hv (t, i.val) y hy hys]
      ring
  unfold b66f_gen_b66m_traceRegularization
  push_cast
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem b66f_gen_b66m_traceRegularization_germ (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) :
    b66f_gen_b66m_traceRegularization R t ρ u v S χ =ᶠ[𝓝 y]
      b66f_gen_b66m_tracePotential R t ρ u v + ∑ i : S,
        fun z => (χ i z : ℂ) * v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) z) := by
  have hopen : IsOpen {z : b65z_fibre c₀ R.C t | z.val.2 ∉ S} :=
    S.finite_toSet.isClosed.isOpen_compl.preimage (continuous_snd.comp continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hy] with z hz
  simpa only [Pi.add_apply, Finset.sum_apply] using
    b66f_gen_b66m_traceRegularization_value R t ρ hρ u hu S v hv χ hs z hz

theorem b66f_gen_b66m_tracePotential_dbar (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) (w : ℂ) :
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_tracePotential R t ρ u v) ⟨y, w⟩ =
      b66f_gen_b66m_sc_gamma R t ρ u ⟨y, w⟩ := by
  have ha := (R.atlas.hA y.val).1
  have ht := b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu y.val y ha
  have hV := b66f_gen_b66m_splitting_holomorphic_off_poles R t S v hr y.val y hy ha
  rw [RiemannRochAna_dbar_congr
    (b66f_gen_b66m_tracePotential_germ R t ρ hρ u hu S v hv y.val y hy ha) w,
    RiemannRochAna_dbar_sub_at _ _ y (ht.mdifferentiableAt (by simp))
      ((b3A_contMDiffWithinAt_real hV).mdifferentiableWithinAt (by simp)
        |>.mdifferentiableAt Filter.univ_mem) w,
    RiemannRochAna_dbar_holomorphic_at _ y (hV.mdifferentiableAt (by simp)) w, sub_zero]
  rfl

theorem b66f_gen_b66m_traceRegularization_dbar_off_poles (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hχ : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (y : b65z_fibre c₀ R.C t) (hy : y.val.2 ∉ S) (w : ℂ) :
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_traceRegularization R t ρ u v S χ) ⟨y, w⟩ =
      b66f_gen_b66m_sc_gamma R t ρ u ⟨y, w⟩ + ∑ i : S,
        v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) y) *
          b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ i z : ℂ)) ⟨y, w⟩ := by
  let f : S → b65z_fibre c₀ R.C t → ℂ :=
    fun i z => (χ i z : ℂ) * v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) z)
  have hf (i : S) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (f i) y :=
    (b66f_gen_b66m_cutoff_split_spec R t S v hr (t, i.val) (χ i) (hχ i) (hs i) y hy).1.mdifferentiableAt
      (by simp)
  rw [RiemannRochAna_dbar_congr
    (b66f_gen_b66m_traceRegularization_germ R t ρ hρ u hu S v hv χ hs y hy) w,
    RiemannRochAna_dbar_add_at _ _ y
      ((b66f_gen_b66m_tracePotential_smooth R t ρ hρ u hu S v hr hv y hy).mdifferentiableAt (by simp))
      (MDifferentiableAt.sum fun i _ => hf i) w,
    b66f_gen_b66m_tracePotential_dbar R t ρ hρ u hu S v hr hv y hy w,
    RiemannRochAna_dbar_sum_at Finset.univ f y (fun i _ => hf i) w]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (b66f_gen_b66m_cutoff_split_spec R t S v hr (t, i.val) (χ i) (hχ i) (hs i) y hy).2 w

theorem b66f_gen_b66m_traceRegularization_dbar (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hχ : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (h1 : ∀ i, χ i =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)] 1)
    (hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i))
    (y : b65z_fibre c₀ R.C t) (w : ℂ) :
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (b66f_gen_b66m_traceRegularization R t ρ u v S χ) ⟨y, w⟩ =
      b66f_gen_b66m_sc_gamma R t ρ u ⟨y, w⟩ + ∑ i : S,
        v (t, i.val) (b66f_gen_b66m_sc_slice R t (t, i.val) y) *
          b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ i z : ℂ)) ⟨y, w⟩ := by
  by_cases hy : y.val.2 ∈ S
  · let i : S := ⟨y.val.2, hy⟩
    have hp : b66f_gen_b66m_sc_pt R t i.val = y := b66f_gen_b66m_sc_fibre_mk R t y
    have hgerm : b66f_gen_b66m_traceRegularization R t ρ u v S χ =ᶠ[𝓝 y]
        b66f_gen_b66m_sc_tau R t ρ u (t, i.val) := by
      rw [← hp]
      exact b66f_gen_b66m_traceRegularization_pole_germ R t ρ u v S χ h1 hsep i
    have hsource : y.val ∈ (R.atlas.A (t, i.val)).source := by
      rw [← hp]
      exact (R.atlas.hA _).1
    have hγ := (b66f_gen_b66m_sc_gamma_local R t ρ hρ hu (t, i.val) y hsource).self_of_nhds w
    have hz (j : S) : b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ j z : ℂ)) ⟨y, w⟩ = 0 := by
      obtain ⟨c, hc⟩ := b66f_gen_b66m_pole_cutoff_constant R t S χ h1 hsep j y hy
      have hC : (fun z => (χ j z : ℂ)) =ᶠ[𝓝 y] fun _ => (c : ℂ) :=
        hc.mono (fun z hz => congrArg Complex.ofReal hz)
      exact RiemannRochAna_dbar_const_germ hC w
    rw [RiemannRochAna_dbar_congr hgerm w, hγ]
    simp only [hz, mul_zero, Finset.sum_const_zero, add_zero]
  · exact b66f_gen_b66m_traceRegularization_dbar_off_poles R t ρ hρ u hu S v hr hv χ hχ hs y hy w

theorem b66f_gen_b66m_dolbeaultIntegral_zero (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) : b66f_gen_b66m_dolbeaultIntegral R t 0 θ = 0 := by
  apply add_eq_left.mp
  simpa only [zero_add] using (b66f_gen_b66m_dolbeaultIntegral_add_left R t 0 0 θ).symm

theorem b66f_gen_b66m_dolbeaultIntegral_sum (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {ι : Type} (s : Finset ι) (β : ι → b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t))
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultIntegral R t (∑ i ∈ s, β i) θ =
      ∑ i ∈ s, b66f_gen_b66m_dolbeaultIntegral R t (β i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using b66f_gen_b66m_dolbeaultIntegral_zero R t θ
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, b66f_gen_b66m_dolbeaultIntegral_add_left, ih]

theorem b66f_gen_b66m_trace_global_assembly (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (χ : S → b65z_fibre c₀ R.C t → ℝ)
    (hχ : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source})
    (h1 : ∀ i, χ i =ᶠ[𝓝 (b66f_gen_b66m_sc_pt R t i.val)] 1)
    (hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i))
    : ∃ β : S → b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t),
      (∀ i, (β i).val = b66f_gen_b66m_poleCorrection R t v (t, i.val) (χ i)) ∧
      ∀ θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t),
        b66f_gen_b66m_dolbeaultIntegral R t
          ⟨b66f_gen_b66m_sc_gamma R t ρ u, b66f_gen_b66m_sc_gamma_mem R t ρ hρ hu⟩ θ =
            -∑ i : S, b66f_gen_b66m_dolbeaultIntegral R t (β i) θ := by
  let β : S → b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) := fun i =>
    ⟨b66f_gen_b66m_poleCorrection R t v (t, i.val) (χ i),
      b66f_gen_b66m_poleCorrection_mem R t S v hr (t, i.val) (χ i) (hχ i) (hs i)
        (fun y hy => b66f_gen_b66m_pole_cutoff_constant R t S χ h1 hsep i y hy)⟩
  let F : b4c_SmoothFun ℂ (b65z_fibre c₀ R.C t) :=
    ⟨b66f_gen_b66m_traceRegularization R t ρ u v S χ,
      b66f_gen_b66m_traceRegularization_smooth R t ρ hρ u hu S v hr hv χ hχ hs
        (b66f_gen_b66m_pole_cutoff_complement R t S χ h1 hsep)⟩
  have heq : (⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) F, b4c_dbar_mem_aux F⟩ :
      b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) =
      ⟨b66f_gen_b66m_sc_gamma R t ρ u, b66f_gen_b66m_sc_gamma_mem R t ρ hρ hu⟩ + ∑ i, β i := by
    apply Subtype.ext
    funext p
    rcases p with ⟨y, w⟩
    simpa only [Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply,
      β, F, b66f_gen_b66m_poleCorrection] using
        b66f_gen_b66m_traceRegularization_dbar R t ρ hρ u hu S v hr hv χ hχ hs h1 hsep y w
  refine ⟨β, fun i => rfl, fun θ => ?_⟩
  have hz := b66f_gen_b66m_dolbeaultIntegral_dbar R t F θ
  rw [heq, b66f_gen_b66m_dolbeaultIntegral_add_left, b66f_gen_b66m_dolbeaultIntegral_sum] at hz
  exact eq_neg_iff_add_eq_zero.mpr hz

def b66f_gen_b66m_localTraceProduct (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (z : ℂ) : ℂ :=
  β.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
    (b3Rest_ζ (Module.finrank_self ℂ) q z)) *
  θ.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
    (b3Rest_ζ (Module.finrank_self ℂ) q z))

theorem b66f_gen_b66m_antihol_chart_coefficient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (q : b65z_fibre c₀ R.C t) (z : ℂ)
    (hz : b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    b3Rest_coef (Module.finrank_self ℂ) (RiemannRochAna_re01 β) q z =
      starRingEnd ℂ (β.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
        (b3Rest_ζ (Module.finrank_self ℂ) q z))) := by
  let u := b3Rest_ζ (Module.finrank_self ℂ) q z
  let e := b3Rest_e (Module.finrank_self ℂ)
  have h : β.val (b3Forms_chartVec q (Complex.I • e) u) =
      -Complex.I * β.val (b3Forms_chartVec q e u) := by
    let L := fderiv ℂ (b3Forms_tr q ((chartAt ℂ q).symm u)) u
    have hh := β.property.2 ((chartAt ℂ q).symm u) Complex.I (L e) 0
    change β.val ⟨(chartAt ℂ q).symm u, L (Complex.I • e)⟩ =
      -Complex.I * β.val ⟨(chartAt ℂ q).symm u, L e⟩
    rw [L.map_smul]
    simp only [add_zero, RiemannRochAna_zero_fibre, Complex.star_def,
      Complex.conj_I] at hh
    exact hh
  unfold b3Rest_coef
  rw [RiemannRochAna_loc_re01 β hz, RiemannRochAna_loc_re01 β hz]
  change ((β.val (b3Forms_chartVec q e u)).re : ℂ) -
    Complex.I * ((β.val (b3Forms_chartVec q (Complex.I • e) u)).re : ℂ) = _
  rw [h]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, u, e]

theorem b66f_gen_b66m_real_chart_coefficient_smul (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (c : ℝ)
    (α : b65z_fibre c₀ R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (q : b65z_fibre c₀ R.C t) (z : ℂ) :
    b3Rest_coef (Module.finrank_self ℂ) (c • α) q z =
      (c : ℂ) * b3Rest_coef (Module.finrank_self ℂ) α q z := by
  simp only [b3Rest_coef, b3Forms_loc_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem b66f_gen_b66m_cfun_dbar_coefficient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b65z_fibre c₀ R.C t) (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g)
    (hgs : ∀ z ∈ tsupport g, b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (z : ℂ) (hz : b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    b4c_dbar ℂ (b65z_fibre c₀ R.C t)
      (fun y => (b3Rest_cfun (Module.finrank_self ℂ) q g y : ℂ))
        (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
          (b3Rest_ζ (Module.finrank_self ℂ) q z)) =
      ((fderiv ℝ g z 1 : ℂ) + Complex.I * (fderiv ℝ g z Complex.I : ℂ)) / 2 := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  let χ := b3Rest_cfun (Module.finrank_self ℂ) q g
  have hsm := b3Rest_smoothFun_cfun (Module.finrank_self ℂ) q hg hgc hgs
  have hχ := RiemannRochAna_contMDiff_of_smooth_fun hsm
  let β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) :=
    ⟨b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun y => (χ y : ℂ)),
      b4c_dbar_mem_aux ⟨fun y => (χ y : ℂ), Complex.ofRealCLM.contMDiff.comp hχ⟩⟩
  have hreal : RiemannRochAna_re01 β = (1 / 2 : ℝ) • b3Forms_d (b3Forms_fun χ) := by
    ext x v
    have hv : v = fun _ => v 0 := by funext i; fin_cases i; rfl
    rw [hv]
    exact RiemannRochAna_dbar_ofReal_re χ hχ x (v 0)
  have hcoef : starRingEnd ℂ (β.val (b3Forms_chartVec q
      (b3Rest_e (Module.finrank_self ℂ)) (b3Rest_ζ (Module.finrank_self ℂ) q z))) =
      (1 / 2 : ℂ) * ((fderiv ℝ g z 1 : ℂ) -
        Complex.I * (fderiv ℝ g z Complex.I : ℂ)) := by
    rw [← b66f_gen_b66m_antihol_chart_coefficient R t β q z hz, hreal,
      b66f_gen_b66m_real_chart_coefficient_smul,
      b3Rest_coef_d_cfun (Module.finrank_self ℂ) q (hg.differentiable (by simp)) hsm hz]
    norm_num
  have hc := congrArg (starRingEnd ℂ) hcoef
  simp only [map_mul, map_sub, map_div₀, map_ofNat, map_one, Complex.conj_ofReal,
    Complex.conj_I, Complex.conj_conj] at hc
  change β.val _ = _
  rw [hc]
  ring

theorem b66f_gen_b66m_poleCorrection_local_product (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (v : b66f_Index R → ℂ → ℂ) (a : b66f_Index R)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g)
    (hgs : ∀ z ∈ tsupport g, b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (hβ : β.val = b66f_gen_b66m_poleCorrection R t v a (b3Rest_cfun (Module.finrank_self ℂ) q g))
    (z : ℂ) (hz : b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    2 * Complex.I * b66f_gen_b66m_localTraceProduct R t β θ q z =
      b66m_planarTraceDensity (fun w => (g w : ℂ)) z *
        (v a (b66f_gen_b66m_sc_slice R t a ((chartAt ℂ q).symm
          (b3Rest_ζ (Module.finrank_self ℂ) q z))) *
          θ.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
            (b3Rest_ζ (Module.finrank_self ℂ) q z))) := by
  unfold b66f_gen_b66m_localTraceProduct
  rw [hβ]
  change 2 * Complex.I * ((v a (b66f_gen_b66m_sc_slice R t a ((chartAt ℂ q).symm
      (b3Rest_ζ (Module.finrank_self ℂ) q z))) *
      b4c_dbar ℂ (b65z_fibre c₀ R.C t)
        (fun y => (b3Rest_cfun (Module.finrank_self ℂ) q g y : ℂ))
        (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
          (b3Rest_ζ (Module.finrank_self ℂ) q z))) * θ.val _) = _
  rw [b66f_gen_b66m_cfun_dbar_coefficient R t q g hg hgc hgs z hz,
    b66m_planarTraceDensity_ofReal (hg.differentiable (by simp) z)]
  ring_nf
  simp [Complex.I_sq] <;> ring

theorem b66f_gen_b66m_poleCorrection_tsupport (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (a : b66f_Index R)
    (χ : b65z_fibre c₀ R.C t → ℝ) (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t))
    (hβ : β.val = b66f_gen_b66m_poleCorrection R t v a χ) :
    tsupport (RiemannRochAna_re01 β) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro y hy
  by_contra hm
  have hχ : (fun z => (χ z : ℂ)) =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hm] with z hz
    change (χ z : ℂ) = 0
    rw [show χ z = 0 from hz, Complex.ofReal_zero]
  have hd (w : ℂ) := RiemannRochAna_dbar_const_germ hχ w
  apply hy
  ext w
  have hw : w = fun _ => w 0 := by funext i; fin_cases i; rfl
  rw [hw]
  change (β.val ⟨y, w 0⟩).re = 0
  rw [hβ]
  change (v a (b66f_gen_b66m_sc_slice R t a y) *
    b4c_dbar ℂ (b65z_fibre c₀ R.C t) (fun z => (χ z : ℂ)) ⟨y, w 0⟩).re = 0
  rw [hd, mul_zero]
  rfl

theorem b66f_gen_b66m_hol_chart_coefficient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (q : b65z_fibre c₀ R.C t) (z : ℂ)
    (hz : b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm θ) q z =
      θ.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
        (b3Rest_ζ (Module.finrank_self ℂ) q z)) := by
  unfold b3Rest_coef
  rw [b3Forms_loc_reForm_apply θ hz, b3Forms_loc_reForm_apply θ hz,
    b3Forms_chartVec_smul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem b66f_gen_b66m_star_antihol_chart_coefficient (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (z : ℂ)
    (hz : b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target) :
    starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
      (b3Forms_star (RiemannRochAna_re01 β)) q z) =
      Complex.I * β.val (b3Forms_chartVec q (b3Rest_e (Module.finrank_self ℂ))
        (b3Rest_ζ (Module.finrank_self ℂ) q z)) := by
  rw [b3Rest_coef_star (Module.finrank_self ℂ) _ q hz,
    b66f_gen_b66m_antihol_chart_coefficient R t β q z hz]
  simp

theorem b66f_gen_b66m_re01_wedge_local (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (r : ℝ)
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (hs : tsupport (RiemannRochAna_re01 β) ⊆ b3Rest_reg (Module.finrank_self ℂ) q r) :
    b3Forms_integral (b3Rest_b (Module.finrank_self ℂ))
      (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm θ)) =
      ∫ z : ℂ in Metric.ball 0 r,
        (b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm θ) q z *
          starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
            (b3Forms_star (RiemannRochAna_re01 β)) q z)).re := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  have hβ := RiemannRochAna_re01_smooth β
  have hs' : tsupport (b3Forms_star (RiemannRochAna_re01 β)) ⊆
      b3Rest_reg (Module.finrank_self ℂ) q r := by
    apply Subset.trans (b := tsupport (RiemannRochAna_re01 β)) _ hs
    apply closure_mono
    intro p hp hzero
    apply hp
    simp only [b3Forms_star, hzero, b3Rest_starPt_zero]
  have hc := b3Forms_pairing_comm (b3Rest_b (Module.finrank_self ℂ))
    (RiemannRochAna_re01 β) (b3Forms_reForm θ)
  change b3Forms_integral _ (b3Forms_wedgeForm (b3Forms_reForm θ) (RiemannRochAna_re01 β)) =
    -b3Forms_integral _ (b3Forms_wedgeForm (RiemannRochAna_re01 β) (b3Forms_reForm θ)) at hc
  have ht := b3Rest_inner_star_eq
    (b3Rest_SF.mk (b3Forms_reForm θ) (b3Forms_isSmooth_reForm θ)) hβ
  change b3Rest_inner (Module.finrank_self ℂ) (b3Forms_reForm θ)
    (b3Forms_star (RiemannRochAna_re01 β)) = -_ at ht
  simp only [b3Rest_SF.form_mk] at ht
  rw [hc, neg_neg] at ht
  rw [← ht]
  exact b3Rest_inner_eq_disc (Module.finrank_self ℂ) (b3Forms_isSmooth_reForm θ)
    hβ.star q hr hs'

theorem b66f_gen_b66m_dolbeaultIntegral_local (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (r : ℝ)
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (hs : tsupport (RiemannRochAna_re01 β) ⊆ b3Rest_reg (Module.finrank_self ℂ) q r) :
    b66f_gen_b66m_dolbeaultIntegral R t β θ =
      2 * ((∫ z : ℂ in Metric.ball 0 r,
        (b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm θ) q z *
          starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
            (b3Forms_star (RiemannRochAna_re01 β)) q z)).re : ℝ) -
        Complex.I * (∫ z : ℂ in Metric.ball 0 r,
          (b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm (Complex.I • θ)) q z *
            starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
              (b3Forms_star (RiemannRochAna_re01 β)) q z)).re : ℝ)) := by
  rw [b66f_gen_b66m_dolbeaultIntegral, b66f_gen_b66m_re01_wedge_local R t β θ q r hr hs,
    b66f_gen_b66m_re01_wedge_local R t β (Complex.I • θ) q r hr hs]

theorem b66f_gen_b66m_dolbeaultIntegral_local_complex (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t))
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (q : b65z_fibre c₀ R.C t) (r : ℝ)
    (hr : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (hs : tsupport (RiemannRochAna_re01 β) ⊆ b3Rest_reg (Module.finrank_self ℂ) q r)
    (hi : MeasureTheory.IntegrableOn (b66f_gen_b66m_localTraceProduct R t β θ q) (Metric.ball 0 r)) :
    b66f_gen_b66m_dolbeaultIntegral R t β θ = 2 * Complex.I *
      ∫ z : ℂ in Metric.ball 0 r, b66f_gen_b66m_localTraceProduct R t β θ q z := by
  let K := b66f_gen_b66m_localTraceProduct R t β θ q
  have hA : (∫ z : ℂ in Metric.ball 0 r,
      (b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm θ) q z *
        starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
          (b3Forms_star (RiemannRochAna_re01 β)) q z)).re) =
      ∫ z : ℂ in Metric.ball 0 r, (Complex.I * K z).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hzt := hr z (mem_ball_zero_iff.mp hz)
    dsimp only
    rw [b66f_gen_b66m_hol_chart_coefficient R t θ q z hzt,
      b66f_gen_b66m_star_antihol_chart_coefficient R t β q z hzt]
    congr 1
    dsimp [K, b66f_gen_b66m_localTraceProduct]
    ring
  have hB : (∫ z : ℂ in Metric.ball 0 r,
      (b3Rest_coef (Module.finrank_self ℂ) (b3Forms_reForm (Complex.I • θ)) q z *
        starRingEnd ℂ (b3Rest_coef (Module.finrank_self ℂ)
          (b3Forms_star (RiemannRochAna_re01 β)) q z)).re) =
      ∫ z : ℂ in Metric.ball 0 r, (-K z).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hzt := hr z (mem_ball_zero_iff.mp hz)
    dsimp only
    rw [b66f_gen_b66m_hol_chart_coefficient R t (Complex.I • θ) q z hzt,
      b66f_gen_b66m_star_antihol_chart_coefficient R t β q z hzt]
    congr 1
    change (Complex.I * θ.val _ ) * (Complex.I * β.val _) = -K z
    dsimp [K, b66f_gen_b66m_localTraceProduct]
    rw [show ∀ a b : ℂ, (Complex.I * a) * (Complex.I * b) = -(a * b) from
      fun a b => by calc
        _ = (Complex.I * Complex.I) * (a * b) := by ring
        _ = _ := by rw [Complex.I_mul_I, neg_one_mul]]
    ring
  have hAi : (∫ z : ℂ in Metric.ball 0 r, (Complex.I * K z).re) =
      (Complex.I * ∫ z : ℂ in Metric.ball 0 r, K z).re := by
    simpa only [Complex.reCLM_apply, MeasureTheory.integral_const_mul] using
      (Complex.reCLM.integral_comp_comm (hi.const_mul Complex.I))
  have hBi : (∫ z : ℂ in Metric.ball 0 r, (-K z).re) =
      (-(∫ z : ℂ in Metric.ball 0 r, K z)).re := by
    simpa only [Complex.reCLM_apply, Pi.neg_apply, MeasureTheory.integral_neg] using
      (Complex.reCLM.integral_comp_comm hi.neg)
  rw [b66f_gen_b66m_dolbeaultIntegral_local R t β θ q r hr hs, hA, hB, hAi, hBi]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem b66f_gen_b66m_poleCorrection_integral (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) (a : b66f_Index R)
    (β : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t)) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (q : b65z_fibre c₀ R.C t) (r : ℝ) (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgr : tsupport g ⊆ Metric.ball 0 r)
    (hg1 : g =ᶠ[𝓝 0] 1)
    (hchart : ∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target)
    (hβ : β.val = b66f_gen_b66m_poleCorrection R t v a (b3Rest_cfun (Module.finrank_self ℂ) q g))
    (hmero : MeromorphicAt (b66f_gen_b66m_localPoleProduct R t v a θ q) 0)
    (han : ∀ z ∈ tsupport g, z ≠ 0 → AnalyticAt ℂ (b66f_gen_b66m_localPoleProduct R t v a θ q) z) :
    b66f_gen_b66m_dolbeaultIntegral R t β θ = -(2 * (Real.pi : ℂ) * Complex.I) *
      TauCeti.Contour.residue (b66f_gen_b66m_localPoleProduct R t v a θ q) 0 := by
  let G := b66f_gen_b66m_localPoleProduct R t v a θ q
  let K := b66f_gen_b66m_localTraceProduct R t β θ q
  let ψ : ℂ → ℂ := fun z => (g z : ℂ)
  let Q : ℂ → ℂ := fun z => b66m_planarTraceDensity ψ z * G z
  have hsψ : tsupport ψ ⊆ tsupport g := tsupport_comp_subset Complex.ofReal_zero g
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
  have hcψ : HasCompactSupport ψ := hgc.comp_left Complex.ofReal_zero
  have hψ1 : ψ =ᶠ[𝓝 0] 1 := by
    filter_upwards [hg1] with z hz
    change (g z : ℂ) = 1
    rw [show g z = 1 from hz, Complex.ofReal_one]
  have hGψ : ∀ z ∈ tsupport ψ, z ≠ 0 → AnalyticAt ℂ G z :=
    fun z hz => han z (hsψ hz)
  have hQi : MeasureTheory.Integrable Q := b66m_cutoff_density_integrable hψ hcψ hψ1 hGψ
  have hgs : ∀ z ∈ tsupport g, b3Rest_ζ (Module.finrank_self ℂ) q z ∈ (chartAt ℂ q).target :=
    fun z hz => hchart z (mem_ball_zero_iff.mp (hgr hz))
  have hprod (z : ℂ) (hz : z ∈ Metric.ball 0 r) : 2 * Complex.I * K z = Q z :=
    b66f_gen_b66m_poleCorrection_local_product R t v a β θ q g hg hgc hgs hβ z
      (hchart z (mem_ball_zero_iff.mp hz))
  have hn : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hKi : MeasureTheory.IntegrableOn K (Metric.ball 0 r) :=
    ((hQi.const_mul ((2 : ℂ) * Complex.I)⁻¹).integrableOn).congr_fun
      (fun z hz => by
        change ((2 : ℂ) * Complex.I)⁻¹ * Q z = K z
        rw [← hprod z hz, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]) measurableSet_ball
  have hsupport : tsupport (RiemannRochAna_re01 β) ⊆ b3Rest_reg (Module.finrank_self ℂ) q r :=
    (b66f_gen_b66m_poleCorrection_tsupport R t v a _ β hβ).trans
      (b3Rest_tsupport_cfun_reg (Module.finrank_self ℂ) q hgc hgr hchart)
  have hQall : (∫ z : ℂ in Metric.ball 0 r, Q z) = ∫ z : ℂ, Q z := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    congr 1
    funext z
    by_cases hz : z ∈ Metric.ball 0 r
    · exact indicator_of_mem hz Q
    · have hs : z ∉ tsupport ψ := fun h => hz (hgr (hsψ h))
      have hd := (b66m_planarTraceDensity_constant_germ
        (notMem_tsupport_iff_eventuallyEq.mp hs)).self_of_nhds
      rw [indicator_of_notMem hz]
      change 0 = b66m_planarTraceDensity ψ z * G z
      rw [show b66m_planarTraceDensity ψ z = 0 from hd, zero_mul]
  calc
    b66f_gen_b66m_dolbeaultIntegral R t β θ = 2 * Complex.I * ∫ z : ℂ in Metric.ball 0 r, K z :=
      b66f_gen_b66m_dolbeaultIntegral_local_complex R t β θ q r hchart hsupport hKi
    _ = ∫ z : ℂ in Metric.ball 0 r, (2 * Complex.I) * K z :=
      (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ z : ℂ in Metric.ball 0 r, Q z :=
      MeasureTheory.setIntegral_congr_fun measurableSet_ball hprod
    _ = ∫ z : ℂ, Q z := hQall
    _ = -(2 * (Real.pi : ℂ) * Complex.I) * TauCeti.Contour.residue G 0 := by
      have hres := b66m_residue_trace_smooth_cutoff hmero hψ hcψ hψ1 hGψ
      rw [hres]
      have hC : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      field_simp <;> rfl

theorem b66f_gen_b66m_trace_residue_sum (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (Q : b66f_forms R t 1) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : ∀ b (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = Q.val b p.val.2 * b66f_gen_b66m_sc_sliceD R t b p w) :
    b66f_gen_b66m_dolbeaultIntegral R t
      ⟨b66f_gen_b66m_sc_gamma R t ρ u, b66f_gen_b66m_sc_gamma_mem R t ρ hρ hu⟩ θ =
        (2 * (Real.pi : ℂ) * Complex.I) * b66f_residueSum R t S v Q.val := by
  let T (i : S) : Finset (b65z_fibre c₀ R.C t) :=
    (Finset.univ.erase i).image (fun j : S => b66f_gen_b66m_sc_pt R t j.val)
  let U (i : S) : Set (b65z_fibre c₀ R.C t) :=
    {y | y.val ∈ (R.atlas.A (t, i.val)).source} ∩ (T i : Set (b65z_fibre c₀ R.C t))ᶜ
  have hG (i : S) := b66f_gen_b66m_localPoleProduct_residue R t v Q θ hθ (t, i.val)
    (b66f_gen_b66m_sc_pt R t i.val) (R.atlas.hA _).1
    (hm _ _ (b66f_gen_b66m_sc_slice_domain R t (t, i.val) (b66f_gen_b66m_sc_pt R t i.val) (R.atlas.hA _).1))
  have h (i : S) : ∃ r : ℝ, 0 < r ∧
      (∀ z : ℂ, ‖z‖ < r → b3Rest_ζ (Module.finrank_self ℂ)
        (b66f_gen_b66m_sc_pt R t i.val) z ∈ (chartAt ℂ (b66f_gen_b66m_sc_pt R t i.val)).target) ∧
      tsupport (b66f_gen_b66m_radialCutoff R t (b66f_gen_b66m_sc_pt R t i.val) r) ⊆ U i ∧
      ∀ z : ℂ, ‖z‖ < r → z ≠ 0 → AnalyticAt ℂ
        (b66f_gen_b66m_localPoleProduct R t v (t, i.val) θ (b66f_gen_b66m_sc_pt R t i.val)) z := by
    have hi : b66f_gen_b66m_sc_pt R t i.val ∉ T i := by
      simp only [T, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
        not_exists, not_and]
      intro j hji heq
      exact hji (Subtype.ext ((b66f_gen_b66m_sc_pt R t).injective heq))
    have hU : U i ∈ 𝓝 (b66f_gen_b66m_sc_pt R t i.val) := inter_mem
      ((b66f_gen_b66m_sc_open_source R t (t, i.val)).mem_nhds (R.atlas.hA _).1)
      ((T i).finite_toSet.isClosed.isOpen_compl.mem_nhds hi)
    obtain ⟨r, hrpos, hdisc⟩ := b66f_gen_b66m_meromorphic_integration_disc R t
      (b66f_gen_b66m_sc_pt R t i.val) (U i) hU _ (hG i).1
    have hchart := fun z hz => (hdisc z hz).1
    refine ⟨r, hrpos, hchart, ?_, fun z hz => (hdisc z hz).2.2⟩
    intro y hy
    have hreg := (b66f_gen_b66m_radialCutoff_spec R t _ r hrpos hchart).2.2 hy
    obtain ⟨z, hz, hzy⟩ := hreg.2
    have heq : (chartAt ℂ (b66f_gen_b66m_sc_pt R t i.val)).symm
        (b3Rest_ζ (Module.finrank_self ℂ) (b66f_gen_b66m_sc_pt R t i.val) z) = y := by
      rw [hzy, (chartAt ℂ (b66f_gen_b66m_sc_pt R t i.val)).left_inv hreg.1]
    rw [← heq]
    exact (hdisc z (mem_ball_zero_iff.mp hz)).2.1
  choose r hrpos hchart hsup han using h
  let χ := fun i : S => b66f_gen_b66m_radialCutoff R t (b66f_gen_b66m_sc_pt R t i.val) (r i)
  have hχ := fun i => (b66f_gen_b66m_radialCutoff_spec R t (b66f_gen_b66m_sc_pt R t i.val)
    (r i) (hrpos i) (hchart i)).1
  have hχ1 := fun i => (b66f_gen_b66m_radialCutoff_spec R t (b66f_gen_b66m_sc_pt R t i.val)
    (r i) (hrpos i) (hchart i)).2.1
  have hs : ∀ i : S, tsupport (χ i) ⊆ {y | y.val ∈ (R.atlas.A (t, i.val)).source} :=
    fun i y hy => (hsup i hy).1
  have hsep : ∀ i j : S, j ≠ i → b66f_gen_b66m_sc_pt R t j.val ∉ tsupport (χ i) := by
    intro i j hji hmem
    apply (hsup i hmem).2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, rfl⟩
  obtain ⟨β, hβ, hint⟩ := b66f_gen_b66m_trace_global_assembly R t ρ hρ u hu S v hr hv χ hχ hs hχ1 hsep
  have heval (i : S) : b66f_gen_b66m_dolbeaultIntegral R t (β i) θ =
      -(2 * (Real.pi : ℂ) * Complex.I) * TauCeti.Contour.residue
        (fun w => v (t, i.val) w * Q.val (t, i.val)
          ((R.atlas.A (t, i.val)).symm (t.val, w)).2)
        (b66f_gen_b66m_sc_slice R t (t, i.val) (b66f_gen_b66m_sc_pt R t i.val)) := by
    let g : ℂ → ℝ := fun z => b4c_residue_profile (r i / 4) (r i / 2) ‖z‖
    have ha : 0 < r i / 4 := by linarith [hrpos i]
    have hab : r i / 4 < r i / 2 := by linarith [hrpos i]
    have hgr : tsupport g ⊆ Metric.ball 0 (r i) := by
      intro z hz
      have hn : ‖z‖ ≤ r i / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          b4c_residue_profile_radial_support hab hz
      exact mem_ball_zero_iff.mpr (by linarith [hrpos i])
    have he := b66f_gen_b66m_poleCorrection_integral R t v (t, i.val) (β i) θ
      (b66f_gen_b66m_sc_pt R t i.val) (r i) g (b4c_residue_profile_radial_smooth ha hab)
      (b4c_residue_profile_radial_compact hab) hgr
      (b4c_residue_profile_radial_one ha hab) (hchart i) (hβ i) (hG i).1
      (fun z hz => han i z (mem_ball_zero_iff.mp (hgr hz)))
    rwa [(hG i).2] at he
  rw [hint θ]
  simp_rw [heval]
  rw [← Finset.mul_sum, neg_mul, neg_neg]
  congr 1
  unfold b66f_residueSum
  have hpt (x : R.C) : (b66f_gen_b66m_sc_pt R t x).val = (t, x) := rfl
  simp_rw [b66f_gen_b66m_sc_slice, hpt]
  exact (Finset.sum_coe_sort S (fun x : R.C => TauCeti.Contour.residue
      (fun z => v (t, x) z * Q.val (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
      (R.atlas.A (t, x) (t, x)).2))

theorem b66f_gen_b66m_cechTrace_residue (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_gen_b66g_scalarBoundary R t v a b x)
    (Q : b66f_forms R t 1) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : ∀ b (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = Q.val b p.val.2 * b66f_gen_b66m_sc_sliceD R t b p w) (c : b66f_gen_b66g_H1O R t)
    (hc : c.val = (b66f_gen_b66g_scalarBoundaries R t).mkQ u) :
    b66f_gen_b66m_cechTrace R t ρ hρ c θ =
      (2 * (Real.pi : ℂ) * Complex.I) * b66f_residueSum R t S v Q.val := by
  have heq : c = b66f_gen_b66m_sc_cechProjection R t ⟨u, hu⟩ := Subtype.ext hc
  rw [heq, b66f_gen_b66m_cechTrace_cycle]
  exact b66f_gen_b66m_trace_residue_sum R t ρ hρ u hu S v hm hr hv Q θ hθ

theorem b66f_gen_b66m_tensor_residue (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ) (q r : b66f_Coeff R) :
    b66f_residueSum R t S
      (fun a z => q a ((R.atlas.A a).symm (t.val, z)).2 * v a z) r =
      b66f_residueSum R t S v (b66f_product R q r) := by
  unfold b66f_residueSum
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  funext z
  simp only [b66f_product]
  ring

theorem b66f_gen_b66m_contraction_trace (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {y | y.val ∈ (R.atlas.A a).source})
    (u : b66f_Cochain R)
    (hu : u ∈ b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t))
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hm : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hr : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → u a b x = b66f_boundary R t v a b x)
    (q r : b66f_forms R t 1) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = r.val a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (c : b66f_gen_b66g_H1O R t)
    (hc : c.val = (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R q.val u)) :
    b66f_residueSum R t S v (b66f_product R q.val r.val) =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66f_gen_b66m_cechTrace R t ρ hρ c θ := by
  obtain ⟨hm', hr', hv'⟩ := b66f_gen_b66m_tensor_splitting R t u S v hm hr hv q
  have ht := b66f_gen_b66m_cechTrace_residue R t ρ hρ (b66f_gen_b66g_contract R q.val u)
    (b66f_gen_b66m_rs_contract_mem R t q.property hu) S
    (fun a z => q.val a ((R.atlas.A a).symm (t.val, z)).2 * v a z)
    hm' hr' hv' r θ hθ c hc
  rw [b66f_gen_b66m_tensor_residue] at ht
  have hn : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [ht, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem b66f_gen_b66m_chartForm_coefficient (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_forms R t 1) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hθ : θ.val = b66f_chartForm R t q.val)
    (a : b66f_Index R) (p : b65z_fibre c₀ R.C t) (ha : p.val ∈ (R.atlas.A a).source)
    (w : ℂ) : θ.val ⟨p, w⟩ = q.val a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w := by
  obtain ⟨M, hM, _⟩ := (b66f_gen_b66g_primitive_comparison hg R t).1
  have heq : M q = θ := by
    apply Subtype.ext
    rw [hθ]
    funext y
    have hp : y.1.val = (t, y.1.val.2) := Prod.ext y.1.property rfl
    have hy : y.1.val ∈ (R.atlas.A (t, y.1.val.2)).source := by
      rw [hp]
      exact (R.atlas.hA _).1
    exact hM q _ y.1 hy y.2
  rw [← heq]
  exact hM q a p ha w

theorem b66f_gen_b66m_multiplicationMatrix_trace (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {y | y.val ∈ (R.atlas.A a).source})
    (q r : Fin 3 → b66f_primitiveForms R t)
    (η : Fin 3 → b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hη : ∀ i, (η i).val = b66f_chartForm R t (r i).val)
    (S : Fin 10 → Finset R.C) (v : Fin 10 → b66f_Index R → ℂ → ℂ)
    (hm : ∀ j a z, z ∈ b66f_domain R t a → MeromorphicAt (v j a) z)
    (hr : ∀ j a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
    (hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t (Pi.single j 1) a b x = b66f_boundary R t (v j) a b x)
    (i : Fin 9) (j : Fin 10) (c : b66f_gen_b66g_H1O R t)
    (hc : c.val = (b66f_gen_b66g_scalarBoundaries R t).mkQ
      (b66f_gen_b66g_contract R (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val
        (b66f_cocycle R t (Pi.single j 1)))) :
    b66f_multiplicationMatrix R t q r S v i j =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * b66f_gen_b66m_cechTrace R t ρ hρ c
        (η ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2) := by
  have hraw : b66f_multiplicationMatrix R t q r S v i j =
      b66f_residueSum R t (S j) (v j)
        (b66f_product R (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val
          (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).val) := by
    obtain ⟨Q, hQ, _, he⟩ := b66f_gen_b66g_invariant_primitive_aux R t (Pi.single j 1)
      (S j) (v j) (hm j) (hr j) (hv j)
      (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1)
      (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2)
    change b66f_residueSum R t (S j) (v j)
      (b66f_average R t (b66f_product R _ _)) = _
    rw [← hQ]
    exact he
  rw [hraw]
  exact b66f_gen_b66m_contraction_trace R t ρ hρ _ (b66f_gen_b66k_cocycle_mem R t (Pi.single j 1))
    (S j) (v j) (hm j) (hr j) (hv j)
    ⟨(q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val,
      (q _).property.1⟩
    ⟨(r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).val,
      (r _).property.1⟩ _ (b66f_gen_b66m_chartForm_coefficient hg R t _ _ (hη _)) c hc

end HodgeLean.Foundations.Program
