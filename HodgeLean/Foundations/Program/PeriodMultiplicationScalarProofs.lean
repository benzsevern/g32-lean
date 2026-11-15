import HodgeLean.Foundations.Program.PeriodMultiplicationDefs

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

attribute [local instance] b3Forms_isManifold_real

theorem b66m_sc_slice_value (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    R.atlas.A a y.val = (t.val, (R.atlas.A a y.val).2) := by
  refine Prod.ext ?_ rfl
  rw [R.atlas.hparam a _ hy]
  exact congrArg Subtype.val y.property

def b66m_sc_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R) :
    rf8_fibre R.C t → ℂ := fun y => (R.atlas.A a y.val).2

def b66m_sc_sliceD (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (p : rf8_fibre R.C t) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66m_sc_slice R t a) p

def b66m_sc_chartD (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x₀ y : rf8_fibre R.C t) :
    ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x₀) y

theorem b66m_sc_fibre_val (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (y : rf8_fibre R.C t) : y.val = (t, y.val.2) :=
  Prod.ext y.property rfl

theorem b66m_sc_slice_contMDiffAt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66m_sc_slice R t a) y :=
  (b66g_slice_coordinate R t a).1.contMDiffAt
    (((R.atlas.A a).open_source.preimage continuous_subtype_val).mem_nhds hy)

theorem b66m_sc_slice_chart (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (x₀ y : rf8_fibre R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (hya : y.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ∧
    deriv (b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ≠ 0 ∧
    ∀ v : ℂ, b66m_sc_sliceD R t a y v =
      deriv (b66m_sc_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
        (extChartAt 𝓘(ℂ, ℂ) x₀ y) * b66m_sc_chartD R t x₀ y v := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set h := b66m_sc_slice R t a ∘ e.symm
  have hyt : e y ∈ e.target := e.map_source hy
  have hinv : e.symm (e y) = y := e.left_inv hy
  have hopen : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y) :=
    (contMDiffOn_extChartAt_symm x₀ (e y) hyt).contMDiffAt
      (extChartAt_target_mem_nhds' hyt)
  have hsl : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66m_sc_slice R t a) (e.symm (e y)) := by
    rw [hinv]
    exact b66m_sc_slice_contMDiffAt R t a y hya
  have hh : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω h (e y) := hsl.comp (e y) hsym
  have han : AnalyticAt ℂ h (e y) := (contMDiffAt_iff_contDiffAt.mp hh).analyticAt
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y) := by
    refine inter_mem (extChartAt_target_mem_nhds' hyt) ?_
    apply (continuousAt_extChartAt_symm'' hyt).preimage_mem_nhds
    rw [hinv]
    exact hopen.mem_nhds hya
  have hinj : InjOn h (e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source}) := by
    intro w₁ hw₁ w₂ hw₂ hw
    have h1 := b66m_sc_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66m_sc_slice_value R t a (e.symm w₂) hw₂.2
    have hv : (e.symm w₁).val = (e.symm w₂).val := by
      apply (R.atlas.A a).injOn hw₁.2 hw₂.2
      rw [h1, h2]
      exact congrArg (fun z => (t.val, z)) hw
    have hy' : e.symm w₁ = e.symm w₂ := Subtype.ext hv
    rw [← e.right_inv hw₁.1, ← e.right_inv hw₂.1, hy']
  refine ⟨han, rf8_deriv_ne_zero_of_injOn hU han hinj, fun v => ?_⟩
  have heq : b66m_sc_slice R t a =ᶠ[𝓝 y] h ∘ e := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy'
    simp only [h, Function.comp_apply, e.left_inv hy']
  have hmd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) h (e y) :=
    mdifferentiableAt_iff_differentiableAt.mpr han.differentiableAt
  have hme : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℂ, ℂ)])
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66m_sc_slice R t a) y
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv h (e y))).comp
        (b66m_sc_chartD R t x₀ y)) :=
    (HasMFDerivAt.comp (g := h) (f := e) y
      han.differentiableAt.hasDerivAt.hasFDerivAt.hasMFDerivAt
      hme.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66m_sc_sliceD
  rw [hH.mfderiv]
  exact mul_comm (b66m_sc_chartD R t x₀ y v) _

theorem b66m_sc_fibre_mk (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (p : rf8_fibre R.C t) : (⟨(t, p.val.2), rfl⟩ : rf8_fibre R.C t) = p :=
  Subtype.ext (b66m_sc_fibre_val R t p).symm

def b66m_sc_pt (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) : R.C ↪ rf8_fibre R.C t where
  toFun x := ⟨(t, x), rfl⟩
  inj' _ _ hxy := congrArg (fun p : rf8_fibre R.C t => p.val.2) hxy

theorem b66m_sc_scalarCycles_spec (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
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

theorem b66m_sc_inv_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ((R.atlas.A a).symm (t.val, b66m_sc_slice R t a y)).2 = y.val.2 := by
  change ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2)).2 = _
  rw [← b66m_sc_slice_value R t a y hy, (R.atlas.A a).left_inv hy]

theorem b66m_sc_slice_domain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (y : rf8_fibre R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    b66m_sc_slice R t a y ∈ b66k_domain R t a := by
  change (t.val, (R.atlas.A a y.val).2) ∈ (R.atlas.A a).target
  rw [← b66m_sc_slice_value R t a y hy]
  exact (R.atlas.A a).map_source hy

theorem b66m_sc_open_source (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) : IsOpen {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A a).source} :=
  (R.atlas.A a).open_source.preimage continuous_subtype_val

theorem b66m_sc_cochain_holo (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R) (c b : b66k_Index R)
    (hu : AnalyticOnNhd ℂ (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 c b))
    (y : rf8_fibre R.C t) (hc : y.val ∈ (R.atlas.A c).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : rf8_fibre R.C t => u c b y.val.2) y := by
  have hz : b66m_sc_slice R t c y ∈ b66k_refinementDomain R t 1 c b := by
    refine ⟨b66m_sc_slice_domain R t c y hc, ?_⟩
    rw [b66m_sc_inv_slice R t c y hc, one_smul, ← b66m_sc_fibre_val R t y]
    exact hb
  have han := hu _ hz
  have hF : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z => u c b ((R.atlas.A c).symm (t.val, z)).2) (b66m_sc_slice R t c y) :=
    han.contDiffAt.contMDiffAt
  apply (hF.comp y (b66m_sc_slice_contMDiffAt R t c y hc)).congr_of_eventuallyEq
  filter_upwards [(b66m_sc_open_source R t c).mem_nhds hc] with y' hy'
  simp only [Function.comp_apply, b66m_sc_inv_slice R t c y' hy']

def b66m_sc_tau (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (s : b66k_Cochain R) (b : b66k_Index R) (y : rf8_fibre R.C t) : ℂ :=
  -∑ᶠ c, ρ c y • s c b y.val.2

theorem b66m_sc_tau_smooth (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (b : b66k_Index R)
    (y : rf8_fibre R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66m_sc_tau R t ρ s b) y := by
  have hsa := (b66m_sc_scalarCycles_spec R t hs).1
  apply ContMDiffAt.neg
  apply ρ.contMDiffAt_finsum
  intro c hc
  exact (b3A_contMDiffWithinAt_real
    (b66m_sc_cochain_holo R t s c b (hsa c b) y (hρ c hc) hb)).of_le (by simp)

theorem b66m_sc_tau_sub (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (a b : b66k_Index R)
    (y : rf8_fibre R.C t) (ha : y.val ∈ (R.atlas.A a).source)
    (hb : y.val ∈ (R.atlas.A b).source) :
    b66m_sc_tau R t ρ s a y - b66m_sc_tau R t ρ s b y = s a b y.val.2 := by
  have hlaw := (b66m_sc_scalarCycles_spec R t hs).2.2
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
      rw [b66m_sc_fibre_val R t y] at ha hb hyc
      rw [hlaw c a b y.val.2 hyc ha hb]
      ring
  unfold b66m_sc_tau
  rw [neg_sub_neg, ← finsum_sub_distrib hf2 hf1]
  simp only [hterm]
  rw [← finsum_smul, ρ.sum_eq_one (mem_univ y), one_smul]

def b66m_sc_gamma (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (s : b66k_Cochain R) : TangentBundle 𝓘(ℂ, ℂ) (rf8_fibre R.C t) → ℂ :=
  fun p => b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ s p.1.val) p

theorem b66m_sc_gamma_local (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) (b : b66k_Index R)
    (y : rf8_fibre R.C t) (hb : y.val ∈ (R.atlas.A b).source) :
    ∀ᶠ y' in 𝓝 y, ∀ v : ℂ, b66m_sc_gamma R t ρ s ⟨y', v⟩ =
      b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ s b) ⟨y', v⟩ := by
  have hsa := (b66m_sc_scalarCycles_spec R t hs).1
  filter_upwards [(b66m_sc_open_source R t b).mem_nhds hb] with y' hy' v
  have ha : y'.val ∈ (R.atlas.A y'.val).source := (R.atlas.hA y'.val).1
  have heq : b66m_sc_tau R t ρ s y'.val =ᶠ[𝓝 y']
      b66m_sc_tau R t ρ s b + fun y'' => s y'.val b y''.val.2 := by
    filter_upwards [(b66m_sc_open_source R t y'.val).mem_nhds ha,
      (b66m_sc_open_source R t b).mem_nhds hy'] with y'' h1 h2
    have := b66m_sc_tau_sub R t ρ hρ hs y'.val b y'' h1 h2
    simp only [Pi.add_apply]
    linear_combination this
  change b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ s y'.val) ⟨y', v⟩ = _
  rw [RiemannRochAna_dbar_congr heq v]
  have hS := b66m_sc_cochain_holo R t s y'.val b (hsa _ _) y' ha hy'
  rw [RiemannRochAna_dbar_add_at _ _ y'
    ((b66m_sc_tau_smooth R t ρ hρ hs b y' hy').mdifferentiableAt (by simp))
    ((b3A_contMDiffWithinAt_real hS).mdifferentiableWithinAt (by simp) |>.mdifferentiableAt
      Filter.univ_mem) v,
    RiemannRochAna_dbar_holomorphic_at _ y' (hS.mdifferentiableAt (by simp)) v, add_zero]

theorem b66m_sc_gamma_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    {s : b66k_Cochain R} (hs : s ∈ b66g_scalarCycles R t) :
    b66m_sc_gamma R t ρ s ∈ b4c_Smooth01 ℂ (rf8_fibre R.C t) := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  refine ⟨fun p => ?_, fun x a v w => ?_⟩
  · set b := p.1.val
    have hb : p.1.val ∈ (R.atlas.A b).source := (R.atlas.hA b).1
    obtain ⟨χ, hχ, hχ1, hχs⟩ := RiemannRochAna_cutoff hE p.1
      ((b66m_sc_open_source R t b).mem_nhds hb)
    let u : rf8_fibre R.C t → ℂ := fun y => (χ y : ℂ) * b66m_sc_tau R t ρ s b y
    have hu : u ∈ b4c_SmoothFun ℂ (rf8_fibre R.C t) := by
      intro y
      by_cases hy : y ∈ tsupport χ
      · exact (Complex.ofRealCLM.contMDiff.comp hχ).contMDiffAt.mul
          (b66m_sc_tau_smooth R t ρ hρ hs b y (hχs hy))
      · apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simp only [u, show χ z = 0 from hz, Complex.ofReal_zero, zero_mul]
    have hsm := RiemannRochAna_dbar_smooth (E := ℂ) (C := rf8_fibre R.C t) ⟨u, hu⟩
    apply (hsm p).congr_of_eventuallyEq
    have hbase : ∀ᶠ y' in 𝓝 p.1, ∀ v : ℂ, b66m_sc_gamma R t ρ s ⟨y', v⟩ =
        b4c_dbar ℂ (rf8_fibre R.C t) u ⟨y', v⟩ := by
      filter_upwards [b66m_sc_gamma_local R t ρ hρ hs b p.1 hb, hχ1.eventually_nhds]
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
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66m_sc_tau R t ρ s x.val) x) a v w

theorem b66m_sc_coord_analytic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (H : rf8_fibre R.C t → ℂ) (a : b66k_Index R) (z : ℂ) (hz : z ∈ b66k_domain R t a)
    (hH : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω H (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2)) :
    AnalyticAt ℂ (fun w => H (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, w)).2)) z := by
  set y₀ := b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2
  have hy₀v : y₀.val = (R.atlas.A a).symm (t.val, z) := b66k_inverse_slice R t a z hz
  have hy₀a : y₀.val ∈ (R.atlas.A a).source := by
    rw [hy₀v]
    exact (R.atlas.A a).map_target hz
  set e := extChartAt 𝓘(ℂ, ℂ) y₀
  set h := b66m_sc_slice R t a ∘ e.symm
  obtain ⟨han, hder, _⟩ := b66m_sc_slice_chart R t a y₀ y₀ (mem_extChartAt_source y₀) hy₀a
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
    exact (b66m_sc_open_source R t a).mem_nhds hy₀a
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
  rw [b66m_sc_inv_slice R t a (e.symm w) hw.2]
  exact congrArg H (b66m_sc_fibre_mk R t (e.symm w)).symm


theorem b66m_sc_tau_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (u : b66k_Cochain R) (b : b66k_Index R) (y : rf8_fibre R.C t) :
    (Function.support fun c => ρ c y • u c b y.val.2).Finite := by
  apply (ρ.locallyFinite.point_finite y).subset
  intro c hc
  simp only [Function.mem_support] at hc ⊢
  exact fun h => hc (by rw [h, zero_smul])

theorem b66m_sc_tau_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (u v : b66k_Cochain R) (b : b66k_Index R) :
    b66m_sc_tau R t ρ (u + v) b = b66m_sc_tau R t ρ u b + b66m_sc_tau R t ρ v b := by
  funext y
  simp only [b66m_sc_tau, Pi.add_apply, smul_add]
  rw [finsum_add_distrib (b66m_sc_tau_finite R t ρ u b y)
    (b66m_sc_tau_finite R t ρ v b y), neg_add]

theorem b66m_sc_tau_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (z : ℂ) (u : b66k_Cochain R) (b : b66k_Index R) :
    b66m_sc_tau R t ρ (z • u) b = z • b66m_sc_tau R t ρ u b := by
  funext y
  have he : (fun c => ρ c y • (z • u c b y.val.2)) =
      fun c => z • (ρ c y • u c b y.val.2) := by
    funext c
    exact smul_comm _ _ _
  simp only [b66m_sc_tau, Pi.smul_apply]
  rw [he, ← smul_finsum, smul_neg]

def b66m_sc_gammaLinear (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    b66g_scalarCycles R t →ₗ[ℂ] b4c_Smooth01 ℂ (rf8_fibre R.C t) where
  toFun u := ⟨b66m_sc_gamma R t ρ u.val, b66m_sc_gamma_mem R t ρ hρ u.property⟩
  map_add' u v := by
    apply Subtype.ext
    funext p
    rcases p with ⟨p, w⟩
    have hp := (R.atlas.hA p.val).1
    change b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ (u.val + v.val) p.val) ⟨p, w⟩ =
      b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ u.val p.val) ⟨p, w⟩ +
        b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ v.val p.val) ⟨p, w⟩
    rw [b66m_sc_tau_add]
    exact RiemannRochAna_dbar_add_at _ _ p
      ((b66m_sc_tau_smooth R t ρ hρ u.property p.val p hp).mdifferentiableAt (by simp))
      ((b66m_sc_tau_smooth R t ρ hρ v.property p.val p hp).mdifferentiableAt (by simp)) w
  map_smul' z u := by
    apply Subtype.ext
    funext p
    rcases p with ⟨p, w⟩
    have hp := (R.atlas.hA p.val).1
    change b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ (z • u.val) p.val) ⟨p, w⟩ =
      z * b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ u.val p.val) ⟨p, w⟩
    rw [b66m_sc_tau_smul]
    exact RiemannRochAna_dbar_smul_at z _ p
      ((b66m_sc_tau_smooth R t ρ hρ u.property p.val p hp).mdifferentiableAt (by simp)) w

theorem b66m_sc_boundary_of_dbar (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t)
    (F : b4c_SmoothFun ℂ (rf8_fibre R.C t))
    (hF : b4c_dbar ℂ (rf8_fibre R.C t) F = b66m_sc_gamma R t ρ u) :
    u ∈ b66g_scalarBoundaries R t := by
  let H := fun a => b66m_sc_tau R t ρ u a - (F : rf8_fibre R.C t → ℂ)
  have hH (a : b66k_Index R) (y : rf8_fibre R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (H a) y := by
    apply RiemannRochAna_analyticAt_of_dbar_germ (Module.finrank_self ℂ) (H a) y
    filter_upwards [(b66m_sc_open_source R t a).mem_nhds hy] with y' hy'
    have hτ := b66m_sc_tau_smooth R t ρ hρ hu a y' hy'
    refine ⟨hτ.sub (F.property y'), fun w => ?_⟩
    rw [RiemannRochAna_dbar_sub_at _ _ y' (hτ.mdifferentiableAt (by simp))
      ((F.property y').mdifferentiableAt (by simp)) w, hF,
      ← (b66m_sc_gamma_local R t ρ hρ hu a y' hy').self_of_nhds w, sub_self]
  let v := fun a z => H a (b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2)
  have hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a) := by
    intro a z hz
    apply b66m_sc_coord_analytic R t (H a) a z hz
    apply hH
    change (t, ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A a).source
    rw [b66k_inverse_slice R t a z hz]
    exact (R.atlas.A a).map_target hz
  apply Submodule.subset_span
  refine ⟨v, hv, ?_⟩
  funext a b x
  by_cases hx : (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source
  · rw [b66g_scalarBoundary, ite_eq_left hx]
    change u a b x =
      H a (b66m_sc_pt R t ((R.atlas.A a).symm
        (t.val, (R.atlas.A a (t, x)).2)).2) -
      H b (b66m_sc_pt R t ((R.atlas.A b).symm
        (t.val, (R.atlas.A b (t, x)).2)).2)
    have hia := b66m_sc_inv_slice R t a (b66m_sc_pt R t x) hx.1
    have hib := b66m_sc_inv_slice R t b (b66m_sc_pt R t x) hx.2
    change ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2)).2 = x at hia
    change ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x at hib
    rw [hia, hib]
    have ht := b66m_sc_tau_sub R t ρ hρ hu a b (b66m_sc_pt R t x) hx.1 hx.2
    change b66m_sc_tau R t ρ u a (b66m_sc_pt R t x) -
      b66m_sc_tau R t ρ u b (b66m_sc_pt R t x) = u a b x at ht
    dsimp only [H, Pi.sub_apply]
    linear_combination -ht
  · rw [(b66m_sc_scalarCycles_spec R t hu).2.1 a b x hx,
      b66g_scalarBoundary, ite_eq_right hx]

theorem b66m_sc_dbar_of_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (v : b66k_Index R → ℂ → ℂ)
    (hv : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (hu : b66g_scalarBoundary R t v ∈ b66g_scalarCycles R t) :
    ∃ F : b4c_SmoothFun ℂ (rf8_fibre R.C t),
      b4c_dbar ℂ (rf8_fibre R.C t) F =
        b66m_sc_gamma R t ρ (b66g_scalarBoundary R t v) := by
  let u := b66g_scalarBoundary R t v
  let V := fun a (y : rf8_fibre R.C t) => v a (b66m_sc_slice R t a y)
  let H := fun y : rf8_fibre R.C t => b66m_sc_tau R t ρ u y.val y - V y.val y
  have hV (a : b66k_Index R) (y : rf8_fibre R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (V a) y :=
    ((hv a _ (b66m_sc_slice_domain R t a y hy)).contDiffAt.contMDiffAt).comp y
      (b66m_sc_slice_contMDiffAt R t a y hy)
  have hloc (a : b66k_Index R) (y : rf8_fibre R.C t)
      (hy : y.val ∈ (R.atlas.A a).source) :
      H =ᶠ[𝓝 y] b66m_sc_tau R t ρ u a - V a := by
    filter_upwards [(b66m_sc_open_source R t a).mem_nhds hy] with z hz
    have hb := (R.atlas.hA z.val).1
    have hba : (t, z.val.2) ∈ (R.atlas.A z.val).source ∩ (R.atlas.A a).source := by
      rw [← b66m_sc_fibre_val R t z]
      exact ⟨hb, hz⟩
    have ht := b66m_sc_tau_sub R t ρ hρ hu z.val a z hb hz
    change b66m_sc_tau R t ρ u z.val z - b66m_sc_tau R t ρ u a z =
      b66g_scalarBoundary R t v z.val a z.val.2 at ht
    rw [b66g_scalarBoundary, ite_eq_left hba, ← b66m_sc_fibre_val R t z] at ht
    dsimp only [H, V, b66m_sc_slice, Pi.sub_apply]
    linear_combination ht
  have hH : H ∈ b4c_SmoothFun ℂ (rf8_fibre R.C t) := by
    intro y
    have hy := (R.atlas.hA y.val).1
    apply ((b66m_sc_tau_smooth R t ρ hρ hu y.val y hy).sub
      ((b3A_contMDiffWithinAt_real (hV y.val y hy)).of_le (by simp))).congr_of_eventuallyEq
    exact hloc y.val y hy
  refine ⟨⟨H, hH⟩, ?_⟩
  funext p
  rcases p with ⟨y, w⟩
  have hy := (R.atlas.hA y.val).1
  change b4c_dbar ℂ (rf8_fibre R.C t) H ⟨y, w⟩ =
    b4c_dbar ℂ (rf8_fibre R.C t) (b66m_sc_tau R t ρ u y.val) ⟨y, w⟩
  rw [RiemannRochAna_dbar_congr (E := ℂ) (hloc y.val y hy) w,
    RiemannRochAna_dbar_sub_at _ _ y
      ((b66m_sc_tau_smooth R t ρ hρ hu y.val y hy).mdifferentiableAt (by simp))
      ((b3A_contMDiffWithinAt_real (hV y.val y hy)).mdifferentiableWithinAt
        (by simp) |>.mdifferentiableAt Filter.univ_mem) w,
    RiemannRochAna_dbar_holomorphic_at _ y ((hV y.val y hy).mdifferentiableAt (by simp)) w,
    sub_zero]

def b66m_sc_classLinear (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    b66g_scalarCycles R t →ₗ[ℂ] b4c_Dolbeault01 ℂ (rf8_fibre R.C t) :=
  (Submodule.mkQ _).comp (b66m_sc_gammaLinear R t ρ hρ)

def b66m_sc_cechProjection (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_scalarCycles R t →ₗ[ℂ] b66g_H1O R t :=
  (((b66g_scalarBoundaries R t).mkQ).comp (b66g_scalarCycles R t).subtype).codRestrict
    (b66g_H1O R t) (fun u => ⟨u.val, u.property, rfl⟩)

theorem b66m_sc_cechProjection_surjective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Function.Surjective (b66m_sc_cechProjection R t) := by
  intro c
  obtain ⟨u, hu, he⟩ := c.property
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

theorem b66m_sc_class_of_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (u : b66k_Cochain R) (hu : u ∈ b66g_scalarCycles R t)
    (hb : u ∈ b66g_scalarBoundaries R t) :
    b66m_sc_classLinear R t ρ hρ ⟨u, hu⟩ = 0 := by
  revert hu
  induction hb using Submodule.span_induction with
  | mem u h =>
    intro hu
    rcases h with ⟨v, hv, rfl⟩
    obtain ⟨F, hF⟩ := b66m_sc_dbar_of_boundary R t ρ hρ v hv hu
    exact (RiemannRochAna_class_eq_zero_iff (Module.finrank_self ℂ) _).mpr ⟨F, hF⟩
  | zero =>
    intro hu
    exact map_zero _
  | add u v hu hv ihu ihv =>
    intro huv
    have huc := (b66g_boundaries R t).2 hu
    have hvc := (b66g_boundaries R t).2 hv
    change b66m_sc_classLinear R t ρ hρ (⟨u, huc⟩ + ⟨v, hvc⟩) = 0
    rw [map_add, ihu huc, ihv hvc, add_zero]
  | smul z u hu ihu =>
    intro hzu
    have huc := (b66g_boundaries R t).2 hu
    change b66m_sc_classLinear R t ρ hρ (z • ⟨u, huc⟩) = 0
    rw [map_smul, ihu huc, smul_zero]

theorem b66m_sc_kernel_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    LinearMap.ker (b66m_sc_cechProjection R t) =
      LinearMap.ker (b66m_sc_classLinear R t ρ hρ) := by
  ext u
  constructor
  · intro hu
    have hx := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
    change ((b66g_scalarBoundaries R t).mkQ u.val) = 0 at hx
    exact LinearMap.mem_ker.mpr (b66m_sc_class_of_boundary R t ρ hρ u.val u.property
      ((Submodule.Quotient.mk_eq_zero (b66g_scalarBoundaries R t)).mp hx))
  · intro hu
    have hx := LinearMap.mem_ker.mp hu
    change (Submodule.Quotient.mk (b66m_sc_gammaLinear R t ρ hρ u) :
      b4c_Dolbeault01 ℂ (rf8_fibre R.C t)) = 0 at hx
    obtain ⟨F, hF⟩ := (RiemannRochAna_class_eq_zero_iff (Module.finrank_self ℂ) _).mp hx
    have hb := b66m_sc_boundary_of_dbar R t ρ hρ u.val u.property F hF
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero (b66g_scalarBoundaries R t)).mpr hb

theorem b66m_sc_comparison (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    ∃ E : b66g_H1O R t →ₗ[ℂ] b4c_Dolbeault01 ℂ (rf8_fibre R.C t),
      Function.Injective E ∧
      ∀ u, E (b66m_sc_cechProjection R t u) = b66m_sc_classLinear R t ρ hρ u := by
  let f := b66m_sc_cechProjection R t
  let g := b66m_sc_classLinear R t ρ hρ
  have hf := b66m_sc_cechProjection_surjective R t
  have hk := b66m_sc_kernel_eq R t ρ hρ
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

theorem b66m_sc_finite (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Module.Finite ℂ (b66g_H1O R t) ∧
      Module.finrank ℂ (b66g_H1O R t) ≤ Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (M := rf8_fibre R.C t) isClosed_univ
    (fun c => {y : rf8_fibre R.C t | y.val ∈ (R.atlas.A c).source})
    (fun c => b66m_sc_open_source R t c)
    (fun y _ => mem_iUnion.mpr ⟨y.val, (R.atlas.hA y.val).1⟩)
  obtain ⟨E, hi, _⟩ := b66m_sc_comparison R t ρ hρ
  have hd := b4c_dolbeault_finite_aux (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  letI := hd.1
  exact ⟨Module.Finite.of_injective E hi,
    (LinearMap.finrank_le_finrank_of_injective hi).trans_eq hd.2⟩

def b66m_sc_periodEval (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    {n : ℕ} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    b3_HolForm ℂ (rf8_fibre R.C t) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i => b3A_toDual
    ⟨(R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val,
      b3A_lattice_mem_linearDual _⟩

theorem b66m_sc_periodSubspace_range (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    {n : ℕ} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    b66g_periodSubspace R s t B = LinearMap.range (b66m_sc_periodEval R s t B) := by
  unfold b66g_periodSubspace
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro v ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩

theorem b66m_sc_periodSubspace_finrank (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    {n : ℕ} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    Module.finrank ℂ (b66g_periodSubspace R s t B) ≤
      Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  letI := b3Forms_holForm_finiteDimensional (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  rw [b66m_sc_periodSubspace_range]
  exact LinearMap.finrank_range_le _

theorem b66m_sc_finrank_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Module.finrank ℂ (b66g_H1O R t) = Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) := by
  obtain ⟨P, _⟩ := b6m_period_comparison (rf8_fibre R.C t)
  letI := b3_periodLattice_finite (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  letI := b3_periodLattice_free (E := ℂ) (C := rf8_fibre R.C t)
  let n := Module.finrank ℤ (b3_periodLattice ℂ (rf8_fibre R.C t))
  let B : Module.Basis (Fin n) ℤ (b66g_Homology R t) :=
    (Module.finBasis ℤ (b3_periodLattice ℂ (rf8_fibre R.C t))).map P.symm
  obtain ⟨E, _⟩ := b66g_griffiths R t t n B
  have hq := (b66g_periodSubspace R t t B).finrank_quotient_add_finrank
  have hn₀ : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  rw [← E.finrank_eq, hn₀] at hq
  have hb := b66m_sc_periodSubspace_finrank R t t B
  have hu := (b66m_sc_finite R t).2
  have hn := b3_finrank_periodLattice (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)
  change n = 2 * Module.finrank ℂ (b3_HolForm ℂ (rf8_fibre R.C t)) at hn
  omega

theorem b66m_sc_comparison_equiv (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source}) :
    ∃ E : b66g_H1O R t ≃ₗ[ℂ] b4c_Dolbeault01 ℂ (rf8_fibre R.C t),
      ∀ u, E (b66m_sc_cechProjection R t u) = b66m_sc_classLinear R t ρ hρ u := by
  obtain ⟨E, hi, hE⟩ := b66m_sc_comparison R t ρ hρ
  letI := (b66m_sc_finite R t).1
  letI := (b4c_dolbeault_finite_aux (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)).1
  have hd : Module.finrank ℂ (b66g_H1O R t) =
      Module.finrank ℂ (b4c_Dolbeault01 ℂ (rf8_fibre R.C t)) :=
    (b66m_sc_finrank_eq R t).trans
      (b4c_dolbeault_finite_aux (E := ℂ) (C := rf8_fibre R.C t) (Module.finrank_self ℂ)).2.symm
  have hs : Function.Surjective E := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi
  exact ⟨LinearEquiv.ofBijective E ⟨hi, hs⟩, hE⟩

end HodgeLean.Foundations.Program
