import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: the Riemann sphere

`OnePoint ℂ` with the charts `z` (away from `∞`) and `1 / z` (away from `0`) is a compact connected
Riemann surface. A holomorphic `1`-form on it is `a(z) dz` with `a` entire and `a(z) = O(|z|⁻²)`
at infinity, so `a = 0` by Liouville: the sphere has no holomorphic `1`-forms.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology OnePoint
open scoped ContDiff

namespace HodgeLean.Foundations.Program

/-- The inversion `z ↦ 1 / z` of the Riemann sphere, exchanging `0` and `∞`. -/
def b4cov_sphInv : OnePoint ℂ → OnePoint ℂ :=
  fun p ↦ p.elim ((0 : ℂ) : OnePoint ℂ) fun z ↦ if z = 0 then (OnePoint.infty : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem b4cov_sphInv_infty : b4cov_sphInv (OnePoint.infty : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem b4cov_sphInv_zero : b4cov_sphInv ((0 : ℂ) : OnePoint ℂ) = (OnePoint.infty : OnePoint ℂ) := by
  simp [b4cov_sphInv]

theorem b4cov_sphInv_coe {z : ℂ} (hz : z ≠ 0) :
    b4cov_sphInv (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [b4cov_sphInv, hz]

theorem b4cov_sphInv_involutive : Function.Involutive b4cov_sphInv := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp
    · rw [b4cov_sphInv_coe hz, b4cov_sphInv_coe (inv_ne_zero hz), inv_inv]

theorem b4cov_tendsto_sphInv_zero :
    Tendsto (fun z : ℂ ↦ b4cov_sphInv (z : OnePoint ℂ)) (𝓝 0) (𝓝 (OnePoint.infty : OnePoint ℂ)) := by
  rw [← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
  refine ⟨?_, ?_⟩
  swap
  · rw [Filter.tendsto_pure_left]
    intro s hs
    simp only [b4cov_sphInv_zero]
    exact mem_of_mem_nhds hs
  have h1 : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 (OnePoint.infty : OnePoint ℂ)) :=
    OnePoint.tendsto_coe_infty.comp (by
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_nhdsNE_zero)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [b4cov_sphInv_coe hz]

theorem b4cov_sphInv_continuous : Continuous b4cov_sphInv := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · simp only [b4cov_sphInv_infty]
    have h1 : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ)) (coclosedCompact ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) :=
      (OnePoint.continuous_coe.tendsto 0).comp (by
        rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        exact Filter.tendsto_inv₀_cobounded)
    refine h1.congr' ?_
    have : {z : ℂ | z ≠ 0} ∈ coclosedCompact ℂ := by
      rw [Filter.coclosedCompact_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact)
    filter_upwards [this] with z hz
    rw [b4cov_sphInv_coe hz]
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      simp only [ContinuousAt, b4cov_sphInv_zero]
      exact b4cov_tendsto_sphInv_zero
    · have h1 : ContinuousAt (fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ)) z :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
      refine h1.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [b4cov_sphInv_coe hw]

/-- The inversion as a homeomorphism. -/
def b4cov_sphInvHomeo : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := b4cov_sphInv
  invFun := b4cov_sphInv
  left_inv := b4cov_sphInv_involutive
  right_inv := b4cov_sphInv_involutive
  continuous_toFun := b4cov_sphInv_continuous
  continuous_invFun := b4cov_sphInv_continuous

/-- The chart `z` of the sphere, defined away from `∞`. -/
def b4cov_chart0 : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

/-- The chart `1 / z` of the sphere, defined away from `0`. -/
def b4cov_chartInf : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  b4cov_sphInvHomeo.toOpenPartialHomeomorph.trans b4cov_chart0

theorem b4cov_chart0_source : b4cov_chart0.source = range ((↑) : ℂ → OnePoint ℂ) := by
  simp [b4cov_chart0]

theorem b4cov_chart0_target : b4cov_chart0.target = univ := by
  simp [b4cov_chart0]

theorem b4cov_chart0_coe (z : ℂ) : b4cov_chart0 (z : OnePoint ℂ) = z := by
  have : (z : OnePoint ℂ) ∈ (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
      ((↑) : ℂ → OnePoint ℂ)).target := by simp
  have h := (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph
      ((↑) : ℂ → OnePoint ℂ)).left_inv (x := z) (by simp)
  simpa [b4cov_chart0] using h

theorem b4cov_chart0_symm (z : ℂ) : b4cov_chart0.symm z = (z : OnePoint ℂ) := by
  simp [b4cov_chart0]

theorem b4cov_chartInf_apply (p : OnePoint ℂ) : b4cov_chartInf p = b4cov_chart0 (b4cov_sphInv p) :=
  rfl

theorem b4cov_chartInf_symm (w : ℂ) : b4cov_chartInf.symm w = b4cov_sphInv (w : OnePoint ℂ) := by
  change b4cov_sphInv (b4cov_chart0.symm w) = _
  rw [b4cov_chart0_symm]

theorem b4cov_chartInf_source :
    b4cov_chartInf.source = {p | b4cov_sphInv p ≠ OnePoint.infty} := by
  ext p
  change p ∈ univ ∩ b4cov_sphInv ⁻¹' b4cov_chart0.source ↔ _
  rw [b4cov_chart0_source]
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_range, mem_ofPred_eq]
  exact OnePoint.ne_infty_iff_exists.symm

theorem b4cov_sphInv_ne_infty_iff (z : ℂ) :
    b4cov_sphInv (z : OnePoint ℂ) ≠ OnePoint.infty ↔ z ≠ 0 := by
  constructor
  · rintro h rfl; exact h b4cov_sphInv_zero
  · intro hz; rw [b4cov_sphInv_coe hz]; exact OnePoint.coe_ne_infty _

theorem b4cov_chart0_sphInv {z : ℂ} (hz : z ≠ 0) : b4cov_chart0 (b4cov_sphInv z) = z⁻¹ := by
  rw [b4cov_sphInv_coe hz, b4cov_chart0_coe]

/-- **The charted space structure of the sphere.** -/
@[instance_reducible] def b4cov_sphChartedSpace : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {b4cov_chart0, b4cov_chartInf}
  chartAt p := p.elim b4cov_chartInf fun _ ↦ b4cov_chart0
  mem_chart_source p := by
    induction p using OnePoint.rec with
    | infty =>
      change OnePoint.infty ∈ b4cov_chartInf.source
      rw [b4cov_chartInf_source]
      simp only [mem_ofPred_eq, b4cov_sphInv_infty]
      exact OnePoint.coe_ne_infty _
    | coe z =>
      change (z : OnePoint ℂ) ∈ b4cov_chart0.source
      rw [b4cov_chart0_source]
      exact mem_range_self z
  chart_mem_atlas p := by
    induction p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl rfl

attribute [local instance] b4cov_sphChartedSpace

theorem b4cov_trans_self_contDiffOn (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    ContDiffOn ℂ ω (e.symm ≫ₕ e) (e.symm ≫ₕ e).source :=
  contDiffOn_id.congr fun z hz ↦ e.right_inv hz.1

/-- **The sphere is a complex manifold**: the transition maps are `z ↦ 1 / z`. -/
theorem b4cov_sph_isManifold : IsManifold 𝓘(ℂ, ℂ) ω (OnePoint ℂ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  have hinv : ContDiffOn ℂ ω (fun z : ℂ ↦ z⁻¹) {z | z ≠ 0} := contDiffOn_inv ℂ
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · exact b4cov_trans_self_contDiffOn _
  · refine (hinv.mono fun z hz ↦ ?_).congr fun z hz ↦ ?_
    · have := hz.2
      simp only [OpenPartialHomeomorph.symm_symm] at this
      rw [mem_preimage, b4cov_chartInf_source, mem_ofPred_eq, b4cov_chart0_symm] at this
      exact (b4cov_sphInv_ne_infty_iff z).1 this
    · have h2 := hz.2
      simp only [OpenPartialHomeomorph.symm_symm] at h2
      rw [mem_preimage, b4cov_chartInf_source, mem_ofPred_eq, b4cov_chart0_symm] at h2
      change b4cov_chartInf (b4cov_chart0.symm z) = z⁻¹
      rw [b4cov_chart0_symm, b4cov_chartInf_apply,
        b4cov_chart0_sphInv ((b4cov_sphInv_ne_infty_iff z).1 h2)]
  · refine (hinv.mono fun z hz ↦ ?_).congr fun z hz ↦ ?_
    · have := hz.2
      simp only [OpenPartialHomeomorph.symm_symm] at this
      rw [mem_preimage, b4cov_chart0_source, b4cov_chartInf_symm] at this
      obtain ⟨y, hy⟩ := this
      exact (b4cov_sphInv_ne_infty_iff z).1 (hy ▸ OnePoint.coe_ne_infty y)
    · have h2 := hz.2
      simp only [OpenPartialHomeomorph.symm_symm] at h2
      rw [mem_preimage, b4cov_chart0_source, b4cov_chartInf_symm] at h2
      obtain ⟨y, hy⟩ := h2
      change b4cov_chart0 (b4cov_chartInf.symm z) = z⁻¹
      rw [b4cov_chartInf_symm,
        b4cov_chart0_sphInv ((b4cov_sphInv_ne_infty_iff z).1 (hy ▸ OnePoint.coe_ne_infty y))]
  · exact b4cov_trans_self_contDiffOn _

attribute [local instance] b4cov_sph_isManifold

theorem b4cov_chartAt_coe (z : ℂ) : chartAt ℂ (z : OnePoint ℂ) = b4cov_chart0 := rfl

theorem b4cov_chartAt_infty : chartAt ℂ (OnePoint.infty : OnePoint ℂ) = b4cov_chartInf := rfl

section Forms

variable (θ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ) → ℂ)

theorem b4cov_form_smul (hθ : θ ∈ b3_HolForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) (v : ℂ) :
    θ ⟨x, v⟩ = v * θ ⟨x, (1 : ℂ)⟩ := by
  have h0 : θ ⟨x, 0⟩ = 0 := by
    have := hθ.2 x 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have := hθ.2 x v (1 : ℂ) 0
  rw [add_zero, h0, add_zero] at this
  rw [← this]
  congr 2
  change v = v * 1
  rw [mul_one]

/-- The section `z ↦ ∂/∂z` over the finite part of the sphere. -/
def b4cov_sec0 (z : ℂ) : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ) := ⟨(z : OnePoint ℂ), (1 : ℂ)⟩

theorem b4cov_coe_contMDiff :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : ℂ ↦ (z : OnePoint ℂ)) := by
  intro z₀
  rw [contMDiffAt_iff]
  refine ⟨OnePoint.continuous_coe.continuousAt, ?_⟩
  simp only [modelWithCornersSelf_coe, range_id, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, id_eq]
  refine contDiffWithinAt_id.congr (fun z _ ↦ ?_) ?_
  · simp [b4cov_chartAt_coe, b4cov_chart0_coe]
  · simp [b4cov_chartAt_coe, b4cov_chart0_coe]

theorem b4cov_sec0_contMDiff : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent ω b4cov_sec0 := by
  intro z₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨b4cov_coe_contMDiff z₀, ?_⟩
  refine (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z ↦ ?_)
  change (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z₀ : OnePoint ℂ) (b4cov_sec0 z)).2 = 1
  rw [TangentBundle.trivializationAt_apply]
  simp only [b4cov_sec0, b4cov_chartAt_coe, modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  have hid : ⇑(b4cov_chart0.extend 𝓘(ℂ, ℂ)) ∘ ⇑(b4cov_chart0.extend 𝓘(ℂ, ℂ)).symm = id := by
    funext w
    simp [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      b4cov_chart0_symm, b4cov_chart0_coe]
  rw [hid, fderiv_id]
  rfl

/-- The section `w ↦ ∂/∂w` in the chart at infinity. -/
def b4cov_secInf (w : ℂ) : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ) :=
  ⟨b4cov_chartInf.symm w,
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ)).symm
      (b4cov_chartInf.symm w) 1⟩

theorem b4cov_chartInf_symm_mem (w : ℂ) : b4cov_chartInf.symm w ∈ b4cov_chartInf.source := by
  apply b4cov_chartInf.map_target
  have : b4cov_chartInf.target = univ := by
    simp [b4cov_chartInf, b4cov_chart0_target]
  rw [this]; trivial

theorem b4cov_triv_secInf (w : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ)
      (b4cov_secInf w)).2 = 1 := by
  rw [b4cov_secInf, Bundle.Trivialization.apply_mk_symm]
  rw [TangentBundle.trivializationAt_baseSet, b4cov_chartAt_infty]
  exact b4cov_chartInf_symm_mem w

theorem b4cov_secInf_contMDiffAt : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent ω b4cov_secInf 0 := by
  rw [Bundle.contMDiffAt_totalSpace]
  have hproj : (b4cov_secInf 0).proj = OnePoint.infty := by
    change b4cov_chartInf.symm 0 = _
    rw [b4cov_chartInf_symm, b4cov_sphInv_zero]
  refine ⟨?_, ?_⟩
  · have := contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := (OnePoint.infty : OnePoint ℂ))
    rw [b4cov_chartAt_infty] at this
    have ht : b4cov_chartInf.target = univ := by simp [b4cov_chartInf, b4cov_chart0_target]
    exact this.contMDiffAt (by rw [ht]; exact univ_mem)
  · rw [hproj]
    exact (contMDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w ↦ b4cov_triv_secInf w)

/-- **The coefficient at infinity**: `θ(∂/∂w) = -z² θ(∂/∂z)` at `w = 1 / z`. -/
theorem b4cov_secInf_rel (hθ : θ ∈ b3_HolForm ℂ (OnePoint ℂ)) {z : ℂ} (hz : z ≠ 0) :
    θ (b4cov_secInf z⁻¹) = -z ^ 2 * θ (b4cov_sec0 z) := by
  have key : ∀ (pt : OnePoint ℂ) (_ : pt = (z : OnePoint ℂ)) (c : ℂ),
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ) ⟨pt, c⟩).2 = 1 →
        θ ⟨pt, c⟩ = -z ^ 2 * θ (b4cov_sec0 z) := by
    rintro _ rfl c hc
    rw [TangentBundle.trivializationAt_apply] at hc
    simp only [b4cov_chartAt_coe, b4cov_chartAt_infty, modelWithCornersSelf_coe, range_id,
      fderivWithin_univ] at hc
    have hF : (⇑(b4cov_chartInf.extend 𝓘(ℂ, ℂ)) ∘ ⇑(b4cov_chart0.extend 𝓘(ℂ, ℂ)).symm) =ᶠ[𝓝 z]
        fun u ↦ u⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds hz] with u hu
      simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
        OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, id_eq,
        b4cov_chart0_symm, b4cov_chartInf_apply, b4cov_chart0_sphInv hu]
    have hz' : (b4cov_chart0.extend 𝓘(ℂ, ℂ)) (z : OnePoint ℂ) = z := by
      simp [OpenPartialHomeomorph.extend_coe, b4cov_chart0_coe]
    rw [hz', hF.fderiv_eq, fderiv_inv] at hc
    change c * -(z ^ 2)⁻¹ = 1 at hc
    have hc' : c = -z ^ 2 := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
      field_simp at hc
      linear_combination -hc
    rw [b4cov_form_smul θ hθ, hc']
    rfl
  have hpt : (b4cov_secInf z⁻¹).proj = (z : OnePoint ℂ) := by
    change b4cov_chartInf.symm z⁻¹ = _
    rw [b4cov_chartInf_symm, b4cov_sphInv_coe (inv_ne_zero hz), inv_inv]
  exact key _ hpt _ (b4cov_triv_secInf z⁻¹)

/-- **The sphere has no nonzero holomorphic `1`-forms** (Liouville). -/
theorem b4cov_sphere_form_eq_zero (hθ : θ ∈ b3_HolForm ℂ (OnePoint ℂ)) : θ = 0 := by
  let a : ℂ → ℂ := fun z ↦ θ (b4cov_sec0 z)
  have ha : Differentiable ℂ a :=
    (contMDiff_iff_contDiff.1 (hθ.1.comp b4cov_sec0_contMDiff)).differentiable (by simp)
  let b : ℂ → ℂ := fun w ↦ θ (b4cov_secInf w)
  have hb : ContinuousAt b 0 :=
    ((hθ.1 (b4cov_secInf 0)).comp 0 b4cov_secInf_contMDiffAt).continuousAt
  have hrel : ∀ z, z ≠ 0 → b z⁻¹ = -z ^ 2 * a z := fun z hz ↦ b4cov_secInf_rel θ hθ hz
  obtain ⟨δ, hδ, hbδ⟩ := Metric.continuousAt_iff.1 hb 1 one_pos
  set M := ‖b 0‖ + 1
  have hbM : ∀ w : ℂ, ‖w‖ < δ → ‖b w‖ ≤ M := fun w hw ↦ by
    have := hbδ (by simpa using hw)
    rw [dist_eq_norm] at this
    have h2 := norm_le_insert' (b w) (b 0)
    linarith
  have hfar : ∀ z : ℂ, δ⁻¹ < ‖z‖ → ‖a z‖ * ‖z‖ ^ 2 ≤ M := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz
      linarith [inv_pos.2 hδ]
    have h1 : ‖z⁻¹‖ < δ := by
      rw [norm_inv]
      exact (inv_lt_comm₀ hδ (norm_pos_iff.2 hz0)).1 hz
    have h2 := hbM _ h1
    rw [hrel z hz0, norm_mul, norm_neg, norm_pow] at h2
    linarith
  -- `a` is bounded
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) δ⁻¹).exists_bound_of_continuousOn
    ha.continuous.continuousOn
  have hbdd : Bornology.IsBounded (range a) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max K (M * δ ^ 2), ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : ‖z‖ ≤ δ⁻¹
    · exact (hK z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      have h1 := hfar z hz
      have h2 : δ⁻¹ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (inv_pos.2 hδ).le hz.le 2
      have h3 : ‖a z‖ ≤ M * δ ^ 2 := by
        have hd : 0 < δ⁻¹ ^ 2 := pow_pos (inv_pos.2 hδ) 2
        have : ‖a z‖ * δ⁻¹ ^ 2 ≤ M := (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans h1
        rw [inv_pow] at this
        rwa [← le_div_iff₀ (inv_pos.2 (pow_pos hδ 2)), div_inv_eq_mul] at this
      exact h3.trans (le_max_right _ _)
  have hconst : ∀ z, a z = a 0 := fun z ↦ ha.apply_eq_apply_of_bounded hbdd z 0
  have ha0 : a 0 = 0 := by
    by_contra hc
    have hpos : 0 < ‖a 0‖ := norm_pos_iff.2 hc
    obtain ⟨n, hn⟩ := exists_nat_gt (max δ⁻¹ (M / ‖a 0‖))
    have hnδ : δ⁻¹ < ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact (le_max_left _ _).trans_lt hn
    have h1 := hfar n hnδ
    rw [hconst, Complex.norm_natCast] at h1
    have hM : M / ‖a 0‖ < n := (le_max_right _ _).trans_lt hn
    have hMpos : 0 < M := by positivity
    have hn1 : (1 : ℝ) ≤ n := by
      have : 0 < (n : ℝ) := (div_pos hMpos hpos).trans hM
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
    have : M < ‖a 0‖ * n := by rwa [div_lt_iff₀' hpos] at hM
    nlinarith
  have hazero : ∀ z, a z = 0 := fun z ↦ (hconst z).trans ha0
  -- `b` vanishes, also at `0`
  have hbne : ∀ w : ℂ, w ≠ 0 → b w = 0 := fun w hw ↦ by
    have := hrel w⁻¹ (inv_ne_zero hw)
    rw [inv_inv] at this
    rw [this, hazero, mul_zero]
  have hb0 : b 0 = 0 := by
    have h1 : Tendsto b (𝓝[≠] 0) (𝓝 (b 0)) := hb.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto b (𝓝[≠] 0) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hbne w hw).symm)
    exact tendsto_nhds_unique h1 h2
  -- the value at infinity
  have hinf : θ ⟨OnePoint.infty, (1 : ℂ)⟩ = 0 := by
    have key : ∀ (pt : OnePoint ℂ) (_ : pt = OnePoint.infty) (c : ℂ),
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (OnePoint.infty : OnePoint ℂ) ⟨pt, c⟩).2 = 1 →
          θ ⟨pt, c⟩ = 0 → θ ⟨OnePoint.infty, (1 : ℂ)⟩ = 0 := by
      rintro _ rfl c hc hθc
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [TangentBundle.trivializationAt_apply] at hc
        simp at hc
      rw [b4cov_form_smul θ hθ] at hθc
      exact (mul_eq_zero.1 hθc).resolve_left hc0
    have hpt : (b4cov_secInf 0).proj = OnePoint.infty := by
      change b4cov_chartInf.symm 0 = _
      rw [b4cov_chartInf_symm, b4cov_sphInv_zero]
    exact key _ hpt _ (b4cov_triv_secInf 0) hb0
  funext p
  obtain ⟨x, v⟩ := p
  induction x using OnePoint.rec with
  | infty =>
    exact (b4cov_form_smul θ hθ _ v).trans (by rw [hinf]; exact mul_zero (show ℂ from v))
  | coe z =>
    have : θ ⟨(z : OnePoint ℂ), (1 : ℂ)⟩ = a z := rfl
    exact (b4cov_form_smul θ hθ _ v).trans (by rw [this, hazero]; exact mul_zero (show ℂ from v))

end Forms

/-- **A compact Riemann surface of genus zero**: the sphere. -/
theorem b4cov_exists_genusZero :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Y)
      (_ : T2Space Y) (_ : CompactSpace Y) (_ : ConnectedSpace Y) (_ : Nonempty Y),
      Module.finrank ℂ (b3_HolForm ℂ Y) = 0 := by
  refine ⟨OnePoint ℂ, inferInstance, b4cov_sphChartedSpace, b4cov_sph_isManifold, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  have : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
  rw [this, finrank_bot]

end HodgeLean.Foundations.Program
