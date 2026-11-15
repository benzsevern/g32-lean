import HodgeLean.Foundations.Program.CodifferentialComparisonResidueTraceProofs
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

def b66f_gen_b66m_complexPeriodFunctional (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (A D : b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℝ] ℝ) :
    (ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) →ₗ[ℂ] ℂ :=
  LinearMap.liftBaseChange ℂ
    (((Complex.ofRealCLM.toLinearMap.comp A).toAddMonoidHom.comp
        (b3Rest2_θHom (Module.finrank_self ℂ)) +
      Complex.I • ((Complex.ofRealCLM.toLinearMap.comp D).toAddMonoidHom.comp
        (b3Rest2_θHom (Module.finrank_self ℂ)))).toIntLinearMap)

def b66f_gen_b66m_correctedLocalForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R)
    (β : b66f_Index R → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ) :
    TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ :=
  fun p => β p.1.val p -
    (show ℂ →L[ℝ] ℂ from
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66f_gen_b66m_sc_tau R t ρ u p.1.val) p.1) p.2

theorem b66f_gen_b66m_relCoef_exists (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (a : b66f_Index R) :
    ∃ α : (Fin 10 → ℂ) × ℂ → ℂ,
      AnalyticOn ℂ α ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U)) ∧
      ∀ (u : b6t_polydisc c₀) (x : b65z_fibre c₀ R.C u), u.val ∈ U →
        x.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
          θ.val u ⟨x, v⟩ = α (u.val, b66f_gen_b66m_sc_slice R u a x) * b66f_gen_b66m_sc_sliceD R u a x v := by
  obtain ⟨α, hα, hθ⟩ := θ.property.2 (R.atlas.A a) (R.atlas.hA a).2 (R.atlas.hparam a)
  refine ⟨α, hα, fun u x hu hx v => ?_⟩
  rw [hθ u x hu hx v, b66f_gen_b66m_sc_slice_value R u a x hx]
  rfl

def b66f_gen_b66m_relCoef (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (a : b66f_Index R) : (Fin 10 → ℂ) × ℂ → ℂ :=
  (b66f_gen_b66m_relCoef_exists R θ a).choose

def b66f_gen_b66m_parameterLocalForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (h : Fin 10 → ℂ) (a : b66f_Index R) :
    TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ := fun p =>
  fderiv ℂ (b66f_gen_b66m_relCoef R θ a) (t.val, b66f_gen_b66m_sc_slice R t a p.1) (h, 0) *
    b66f_gen_b66m_sc_sliceD R t a p.1 p.2

theorem b66f_gen_b66m_correctedParameterForm_add (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (p : b65z_fibre c₀ R.C t) (v w : ℂ) :
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, v + w⟩ =
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, v⟩ +
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, w⟩ := by
  have hD := (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
    (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) p.val) p).map_add v w
  simp only [b66f_gen_b66m_correctedLocalForm, b66f_gen_b66m_parameterLocalForm]
  rw [hD, map_add, mul_add]
  ring

theorem b66f_gen_b66m_correctedParameterForm_smul (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (p : b65z_fibre c₀ R.C t) (c : ℝ) (v : ℂ) :
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, c • v⟩ =
    c • b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, v⟩ := by
  simp only [b66f_gen_b66m_correctedLocalForm, b66f_gen_b66m_parameterLocalForm]
  have hD := (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
    (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) p.val) p).map_smul c v
  have hS := ((b66f_gen_b66m_sc_sliceD R t p.val p).restrictScalars ℝ).map_smul c v
  change b66f_gen_b66m_sc_sliceD R t p.val p (c • v) = c • b66f_gen_b66m_sc_sliceD R t p.val p v at hS
  rw [hD, hS]
  simp only [Complex.real_smul]
  ring

def b66f_gen_b66m_correctedParameterScalarForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (L : ℂ →L[ℝ] ℝ) :
    b65z_fibre c₀ R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  b66m_scalarTangentForm
    (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h))
    (b66f_gen_b66m_correctedParameterForm_add R t θ q h ρ)
    (b66f_gen_b66m_correctedParameterForm_smul R t θ q h ρ) L

theorem b66f_gen_b66m_realDifferential_smooth (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (f : b65z_fibre c₀ R.C t → ℂ)
    (S : Set (b65z_fibre c₀ R.C t)) (hS : IsOpen S)
    (hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f S)
    (p : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t)) (hp : p.1 ∈ S) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) =>
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f q.1) q.2) p := by
  have ho : IsOpen ((Bundle.TotalSpace.proj :
      TangentBundle 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) → b65z_fibre c₀ R.C t) ⁻¹' S) :=
    hS.preimage (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℝ, ℂ)))
  have hd := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hS.uniqueMDiffOn
  let pr : TangentBundle 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) := ⟨p.1, p.2⟩
  have hm := hd.contMDiffAt (x := pr) (ho.mem_nhds hp)
  have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ)
    (n := ∞)).contMDiffAt.comp pr hm
  have hr := RiemannRochAna_realTangent (E := ℂ) (C := b65z_fibre c₀ R.C t)
  apply (hs.comp p (hr p)).congr_of_eventuallyEq
  filter_upwards [((hr p).continuousAt).preimage_mem_nhds (ho.mem_nhds hp)] with q hq
  change (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f q.1) q.2 =
    (show ℂ →L[ℝ] ℂ from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f S q.1) q.2
  rw [mfderivWithin_of_mem_nhds (hS.mem_nhds hq)]

theorem b66f_gen_b66m_coordinateForm_smooth (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (a : b66f_Index R) (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (b66f_domain R t a))
    (p : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t))
    (hp : p.1.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) =>
        A (b66f_gen_b66m_sc_slice R t a q.1) * b66f_gen_b66m_sc_sliceD R t a q.1 q.2) p := by
  let S : Set (b65z_fibre c₀ R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  have hS : IsOpen S := b66f_gen_b66m_sc_open_source R t a
  have hs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (b66f_gen_b66m_sc_slice R t a) S := by
    intro y hy
    exact (b3A_contMDiffWithinAt_real
      (b66f_gen_b66m_sc_slice_contMDiffAt R t a y hy).contMDiffWithinAt).of_le (by simp)
  have hD := b66f_gen_b66m_realDifferential_smooth R t (b66f_gen_b66m_sc_slice R t a) S hS hs p hp
  have hAc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (A ∘ b66f_gen_b66m_sc_slice R t a) p.1 :=
    (b3A_contMDiffWithinAt_real
      (((hA _ (b66f_gen_b66m_sc_slice_domain R t a p.1 hp)).contDiffAt.contMDiffAt).comp
        p.1 (b66f_gen_b66m_sc_slice_contMDiffAt R t a p.1 hp)).contMDiffWithinAt).of_le (by simp)
  have hproj : ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (fun q : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) => q.1) p :=
    RiemannRochAna_projection_smooth (E := ℂ) (C := b65z_fibre c₀ R.C t) p
  apply ((hAc.comp p hproj).mul hD).congr_of_eventuallyEq
  have hpn := (FiberBundle.continuous_proj ℂ
    (TangentSpace 𝓘(ℂ, ℂ))).continuousAt (x := p)
  filter_upwards [hpn.preimage_mem_nhds (hS.mem_nhds hp)] with q hq
  have he := (b3A_mdifferentiableAt_real
    ((b66f_gen_b66m_sc_slice_contMDiffAt R t a q.1 hq).mdifferentiableAt (by simp))).2 q.2
  exact congrArg (fun v : ℂ => A (b66f_gen_b66m_sc_slice R t a q.1) * v) he.symm

theorem b66f_gen_b66m_relCoef_open (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (a : b66f_Index R) :
    IsOpen ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U)) :=
  (R.atlas.A a).open_target.inter (((rf5_polydisc_isOpen c₀).inter hU).preimage continuous_fst)

theorem b66f_gen_b66m_relCoef_analytic (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (a : b66f_Index R) :
    AnalyticOnNhd ℂ (b66f_gen_b66m_relCoef R θ a)
      ((R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U)) :=
  ((b66f_gen_b66m_relCoef_open R hU a).analyticOn_iff_analyticOnNhd).1
    (b66f_gen_b66m_relCoef_exists R θ a).choose_spec.1

theorem b66f_gen_b66m_parameterLocalForm_smooth (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (h : Fin 10 → ℂ) (a : b66f_Index R)
    (p : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t))
    (hp : p.1.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (b66f_gen_b66m_parameterLocalForm R t θ h a) p := by
  apply b66f_gen_b66m_coordinateForm_smooth R t a
    (fun w => fderiv ℂ (b66f_gen_b66m_relCoef R θ a) (t.val, w) (h, 0)) _ p hp
  intro w hw
  have hfd := (b66f_gen_b66m_relCoef_analytic R hU θ a).fderiv _
    (show (t.val, w) ∈ (R.atlas.A a).target ∩
      Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U) from ⟨hw, t.property, ht⟩)
  have hin : AnalyticAt ℂ (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) w :=
    analyticAt_const.prod analyticAt_id
  exact (ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).analyticAt _
    |>.comp_of_eq (hfd.comp_of_eq hin rfl) rfl

theorem b66f_gen_b66m_sc_tau_derivative_sub (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (a b : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source)
    (w : ℂ) :
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66f_gen_b66m_sc_tau R t ρ u a) p) w -
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66f_gen_b66m_sc_tau R t ρ u b) p) w =
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (fun y : b65z_fibre c₀ R.C t => u a b y.val.2) p) w := by
  have heq : b66f_gen_b66m_sc_tau R t ρ u a - b66f_gen_b66m_sc_tau R t ρ u b =ᶠ[𝓝 p]
      (fun y : b65z_fibre c₀ R.C t => u a b y.val.2) := by
    filter_upwards [(b66f_gen_b66m_sc_open_source R t a).mem_nhds ha,
      (b66f_gen_b66m_sc_open_source R t b).mem_nhds hb] with y hya hyb
    exact b66f_gen_b66m_sc_tau_sub R t ρ hρ hu a b y hya hyb
  have hda := (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a p ha).mdifferentiableAt (by simp)
  have hdb := (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu b p hb).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
  rw [mfderiv_sub hda hdb] at hd
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L w) hd

theorem b66f_gen_b66m_correctedLocalForm_local (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    (β : b66f_Index R → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ)
    (hβ : ∀ a b (p : b65z_fibre c₀ R.C t),
      p.val ∈ (R.atlas.A a).source → p.val ∈ (R.atlas.A b).source → ∀ w : ℂ,
      β a ⟨p, w⟩ - β b ⟨p, w⟩ =
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          (fun y : b65z_fibre c₀ R.C t => u a b y.val.2) p) w)
    (a : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66f_gen_b66m_correctedLocalForm R t ρ u β ⟨p, w⟩ = β a ⟨p, w⟩ -
      (show ℂ →L[ℝ] ℂ from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (b66f_gen_b66m_sc_tau R t ρ u a) p) w := by
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hd := b66f_gen_b66m_sc_tau_derivative_sub R t ρ hρ u hu a p.val p ha hb w
  have hl := hβ a p.val p ha hb w
  dsimp only [b66f_gen_b66m_correctedLocalForm]
  linear_combination hd - hl

theorem b66f_gen_b66m_relCoef_spec (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (a : b66f_Index R)
    (u : b6t_polydisc c₀) (x : b65z_fibre c₀ R.C u) (hu : u.val ∈ U)
    (hx : x.val ∈ (R.atlas.A a).source) (v : ℂ) :
    θ.val u ⟨x, v⟩ = b66f_gen_b66m_relCoef R θ a (u.val, b66f_gen_b66m_sc_slice R u a x) * b66f_gen_b66m_sc_sliceD R u a x v :=
  (b66f_gen_b66m_relCoef_exists R θ a).choose_spec.2 u x hu hx v

theorem b66f_gen_b66m_rs_transition_hasDerivAt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (z : ℂ)
    (hz : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    HasDerivAt (fun w => b66f_transition R a b (t.val, w))
      (fderiv ℂ (b66f_transition R a b) (t.val, z) (0, 1)) z := by
  have hd := (b66f_gen_b66k_transition_analytic R a b _ hz).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (0, 1) z :=
    (hasDerivAt_const z t.val).prodMk (hasDerivAt_id z)
  exact hd.comp_hasDerivAt z hi

theorem b66f_gen_b66m_rs_slice_change (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source) (v : ℂ) :
    b66f_gen_b66m_sc_sliceD R t b p v = b66f_vertical R t a b p.val.2 * b66f_gen_b66m_sc_sliceD R t a p v := by
  set g : ℂ → ℂ := fun w => b66f_transition R a b (t.val, w)
  have hpa := b66f_gen_b66m_sc_slice_value R t a p ha
  have hz : (t.val, b66f_gen_b66m_sc_slice R t a p) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A b).source
      rw [← hpa, (R.atlas.A a).left_inv ha]
      exact hb
  have hg := b66f_gen_b66m_rs_transition_hasDerivAt R t a b _ hz
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66f_gen_b66m_sc_slice R t b =ᶠ[𝓝 p] g ∘ b66f_gen_b66m_sc_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A b y.val).2 =
      (R.atlas.A b ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2))).2
    rw [← b66f_gen_b66m_sc_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (b66f_gen_b66m_sc_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hg.differentiableAt
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66m_sc_slice R t a) p :=
    (b66f_gen_b66m_sc_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66m_sc_slice R t b) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (fderiv ℂ (b66f_transition R a b) (t.val, b66f_gen_b66m_sc_slice R t a p) (0, 1))).comp
        (b66f_gen_b66m_sc_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := g) (f := b66f_gen_b66m_sc_slice R t a) p hg.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66f_gen_b66m_sc_sliceD at hH ⊢
  rw [hH.mfderiv]
  have hv : fderiv ℂ (b66f_transition R a b) (t.val, b66f_gen_b66m_sc_slice R t a p) (0, 1) =
      b66f_vertical R t a b p.val.2 := by
    change _ = fderiv ℂ (b66f_transition R a b) (R.atlas.A a (t, p.val.2)) (0, 1)
    rw [← b66f_gen_b66m_sc_fibre_val R t p]
    exact congrArg (fun u => fderiv ℂ (b66f_transition R a b) u (0, 1)) hpa.symm
  rw [← hv]
  exact mul_comm (b66f_gen_b66m_sc_sliceD R t a p v) _

theorem b66f_gen_b66m_sliceD_one_ne (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (a : b66f_Index R) (x : b65z_fibre c₀ R.C t)
    (hx : x.val ∈ (R.atlas.A a).source) : b66f_gen_b66m_sc_sliceD R t a x 1 ≠ 0 := by
  intro h
  apply (b66f_gen_b66g_slice_coordinate R t a).2 x hx
  ext1
  change b66f_gen_b66m_sc_sliceD R t a x 1 = 0
  exact h

theorem b66f_gen_b66m_relCoef_law (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (a b : b66f_Index R)
    {p₀ : (Fin 10 → ℂ) × ℂ} (hp₀ : p₀ ∈ (R.atlas.A a).target)
    (hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source)
    (hp₀U : p₀.1 ∈ b6t_polydisc c₀ ∩ U) :
    ∀ᶠ p in 𝓝 p₀, b66f_gen_b66m_relCoef R θ a p =
      b66f_gen_b66m_relCoef R θ b (p.1, b66f_transition R a b p) *
        fderiv ℂ (b66f_transition R a b) p (0, 1) := by
  have e1 : ∀ᶠ p in 𝓝 p₀, p ∈ (R.atlas.A a).target :=
    (R.atlas.A a).open_target.mem_nhds hp₀
  have e2 : ∀ᶠ p in 𝓝 p₀, (R.atlas.A a).symm p ∈ (R.atlas.A b).source :=
    ((R.atlas.A a).continuousAt_symm hp₀).preimage_mem_nhds
      ((R.atlas.A b).open_source.mem_nhds hp₀b)
  have e3 : ∀ᶠ p in 𝓝 p₀, p.1 ∈ b6t_polydisc c₀ ∩ U :=
    continuous_fst.continuousAt.preimage_mem_nhds
      (((rf5_polydisc_isOpen c₀).inter hU).mem_nhds hp₀U)
  filter_upwards [e1, e2, e3] with p hpa hpb hpU
  set u : b6t_polydisc c₀ := ⟨p.1, hpU.1⟩
  have hd : p.2 ∈ b66f_domain R u a := by
    change (p.1, p.2) ∈ (R.atlas.A a).target
    exact hpa
  set x := b66f_gen_b66m_sc_pt R u ((R.atlas.A a).symm (u.val, p.2)).2
  have hxv : x.val = (R.atlas.A a).symm p := b66f_gen_b66k_inverse_slice R u a p.2 hd
  have hxa : x.val ∈ (R.atlas.A a).source := by rw [hxv]; exact (R.atlas.A a).map_target hpa
  have hxb : x.val ∈ (R.atlas.A b).source := by rw [hxv]; exact hpb
  have h1 := b66f_gen_b66m_relCoef_spec R θ a u x hpU.2 hxa 1
  have h2 := b66f_gen_b66m_relCoef_spec R θ b u x hpU.2 hxb 1
  have h3 := b66f_gen_b66m_rs_slice_change R u a b x hxa hxb 1
  have hsa : b66f_gen_b66m_sc_slice R u a x = p.2 := by
    change (R.atlas.A a x.val).2 = p.2
    rw [hxv, (R.atlas.A a).right_inv hpa]
  have hsb : b66f_gen_b66m_sc_slice R u b x = b66f_transition R a b p := by
    change (R.atlas.A b x.val).2 = _
    rw [hxv]
    rfl
  have hv : b66f_vertical R u a b x.val.2 = fderiv ℂ (b66f_transition R a b) p (0, 1) := by
    unfold b66f_vertical
    rw [← b66f_gen_b66m_sc_fibre_val R u x, hxv, (R.atlas.A a).right_inv hpa]
  rw [h1, hsa, h3, hsb, hv] at h2
  have hne := b66f_gen_b66m_sliceD_one_ne R u a x hxa
  have := mul_right_cancel₀ hne (h2.trans (mul_assoc _ _ _).symm)
  exact this

theorem b66f_gen_b66m_relCoef_base (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} {t : b6t_polydisc c₀} (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R)
    (hq : ∀ (a : b66f_Index R) (p : b65z_fibre c₀ R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p v))
    (a : b66f_Index R) (x : b65z_fibre c₀ R.C t) (hx : x.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66m_relCoef R θ a (t.val, b66f_gen_b66m_sc_slice R t a x) = q a x.val.2 := by
  have h1 := b66f_gen_b66m_relCoef_spec R θ a t x ht hx 1
  have h2 := hq a x hx (1 : ℂ)
  rw [h1] at h2
  exact mul_right_cancel₀ (b66f_gen_b66m_sliceD_one_ne R t a x hx) h2

theorem b66f_gen_b66m_relCoef_derivative_overlap (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) {t : b6t_polydisc c₀} (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R)
    (hq : ∀ (a : b66f_Index R) (p : b65z_fibre c₀ R.C t),
      p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      θ.val t ⟨p, v⟩ = q a p.val.2 *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p v))
    (h : Fin 10 → ℂ) :
    (∀ a, AnalyticOnNhd ℂ (fun w =>
      fderiv ℂ (b66f_gen_b66m_relCoef R θ a) (t.val, w) (h, 0)) (b66f_domain R t a)) ∧
    ∀ a b w, w ∈ b66f_gen_b66k_refinementDomain R t 1 a b →
      HasDerivAt (fun z => b66f_gen_b66g_contract R q (b66f_cocycle R t h) a b
        ((R.atlas.A a).symm (t.val, z)).2)
        (fderiv ℂ (b66f_gen_b66m_relCoef R θ a) (t.val, w) (h, 0) -
          fderiv ℂ (b66f_gen_b66m_relCoef R θ b)
            (t.val, b66f_transition R a b (t.val, w)) (h, 0) *
              fderiv ℂ (b66f_transition R a b) (t.val, w) (0, 1)) w := by
  have hW : ∀ a w, w ∈ b66f_domain R t a → (t.val, w) ∈ (R.atlas.A a).target ∩
      Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U) := fun a w hw => ⟨hw, t.property, ht⟩
  refine ⟨fun a w hw => ?_, fun a b w hw => ?_⟩
  · have hfd := (b66f_gen_b66m_relCoef_analytic R hU θ a).fderiv _ (hW a w hw)
    have hin : AnalyticAt ℂ (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) w :=
      analyticAt_const.prod analyticAt_id
    exact (ContinuousLinearMap.apply ℂ ℂ ((h, 0) : (Fin 10 → ℂ) × ℂ)).analyticAt _ |>.comp_of_eq
      (hfd.comp_of_eq hin rfl) rfl
  · set p₀ : (Fin 10 → ℂ) × ℂ := (t.val, w)
    set τ := b66f_transition R a b
    obtain ⟨hm, hτd, -, -⟩ := b66f_gen_b66m_rs_transition_mem R t a b w hw
    have hτa : AnalyticAt ℂ τ p₀ := b66f_gen_b66k_transition_analytic R a b p₀ hm
    have hp₀b : (R.atlas.A a).symm p₀ ∈ (R.atlas.A b).source := hm.2
    set αa := b66f_gen_b66m_relCoef R θ a
    set αb := b66f_gen_b66m_relCoef R θ b
    set e := τ p₀
    have hαa := b66f_gen_b66m_relCoef_analytic R hU θ a
    have hαb := b66f_gen_b66m_relCoef_analytic R hU θ b
    have hWb : (t.val, e) ∈ (R.atlas.A b).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U) :=
      hW b e hτd
    -- the transformation law and its derivative in the parameter direction
    have hlaw := b66f_gen_b66m_relCoef_law R hU θ a b hm.1 hp₀b ⟨t.property, ht⟩
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
    have hS : (fun z => b66f_gen_b66g_contract R q (b66f_cocycle R t h) a b
        ((R.atlas.A a).symm (t.val, z)).2) =ᶠ[𝓝 w]
        fun z => αb (t.val, τ (t.val, z)) * fderiv ℂ τ (t.val, z) (h, 0) := by
      filter_upwards [b66f_gen_b66m_rs_overlap_eventually R t a b w hw] with z hz
      have hzb : (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2).val ∈ (R.atlas.A b).source :=
        hz.1.2
      have hqb := b66f_gen_b66m_relCoef_base R ht θ q hq b _ hzb
      have hsl : b66f_gen_b66m_sc_slice R t b (b66f_gen_b66m_sc_pt R t ((R.atlas.A a).symm (t.val, z)).2) =
          τ (t.val, z) := hz.2.2
      rw [hsl] at hqb
      have hqb' : αb (t.val, τ (t.val, z)) = q b ((R.atlas.A a).symm (t.val, z)).2 := hqb
      simp only [b66f_gen_b66g_contract, b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk, hz.1, ↓reduceIte,
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

theorem b66f_gen_b66m_cochain_real_derivative (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (u : b66f_Cochain R) (a b : b66f_Index R)
    (p : b65z_fibre c₀ R.C t) (ha : p.val ∈ (R.atlas.A a).source)
    (d : ℂ)
    (hd : HasDerivAt (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      d (b66f_gen_b66m_sc_slice R t a p)) (w : ℂ) :
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun y : b65z_fibre c₀ R.C t => u a b y.val.2) p) w =
        d * b66f_gen_b66m_sc_sliceD R t a p w := by
  let f : ℂ → ℂ := fun z => u a b ((R.atlas.A a).symm (t.val, z)).2
  have heq : (fun y : b65z_fibre c₀ R.C t => u a b y.val.2) =ᶠ[𝓝 p]
      f ∘ b66f_gen_b66m_sc_slice R t a := by
    filter_upwards [(b66f_gen_b66m_sc_open_source R t a).mem_nhds ha] with y hy
    exact congrArg (u a b) (b66f_gen_b66m_sc_inv_slice R t a y hy).symm
  have hs := (b66f_gen_b66m_sc_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hD := (HasMFDerivAt.comp (g := f) (f := b66f_gen_b66m_sc_slice R t a) p
    hd.hasFDerivAt.hasMFDerivAt hs.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  refine ((b3A_mdifferentiableAt_real hD.mdifferentiableAt).2 w).trans ?_
  rw [hD.mfderiv]
  change b66f_gen_b66m_sc_sliceD R t a p w • d = d * b66f_gen_b66m_sc_sliceD R t a p w
  exact mul_comm (b66f_gen_b66m_sc_sliceD R t a p w) d

theorem b66f_gen_b66m_parameterLocalForm_overlap (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ) (a b : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source)
    (w : ℂ) :
    b66f_gen_b66m_parameterLocalForm R t θ h a ⟨p, w⟩ -
      b66f_gen_b66m_parameterLocalForm R t θ h b ⟨p, w⟩ =
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun y : b65z_fibre c₀ R.C t =>
        b66f_gen_b66g_contract R q (b66f_cocycle R t h) a b y.val.2) p) w := by
  have hz : b66f_gen_b66m_sc_slice R t a p ∈ b66f_gen_b66k_refinementDomain R t 1 a b := by
    refine ⟨b66f_gen_b66m_sc_slice_domain R t a p ha, ?_⟩
    rw [b66f_gen_b66m_sc_inv_slice R t a p ha, one_smul, ← b66f_gen_b66m_sc_fibre_val R t p]
    exact hb
  have hd := (b66f_gen_b66m_relCoef_derivative_overlap R hU ht θ q hq h).2 a b _ hz
  rw [b66f_gen_b66m_cochain_real_derivative R t _ a b p ha _ hd w]
  have hsb : b66f_transition R a b (t.val, b66f_gen_b66m_sc_slice R t a p) =
      b66f_gen_b66m_sc_slice R t b p := by
    change (R.atlas.A b ((R.atlas.A a).symm
      (t.val, (R.atlas.A a p.val).2))).2 = _
    rw [← b66f_gen_b66m_sc_slice_value R t a p ha, (R.atlas.A a).left_inv ha]
    rfl
  have hv : fderiv ℂ (b66f_transition R a b)
      (t.val, b66f_gen_b66m_sc_slice R t a p) (0, 1) = b66f_vertical R t a b p.val.2 := by
    unfold b66f_vertical
    rw [← b66f_gen_b66m_sc_fibre_val R t p, b66f_gen_b66m_sc_slice_value R t a p ha]
    rfl
  simp only [b66f_gen_b66m_parameterLocalForm]
  rw [hsb, hv, b66f_gen_b66m_rs_slice_change R t a b p ha hb w]
  ring

theorem b66f_gen_b66m_correctedParameterForm_local (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (a : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (w : ℂ) :
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, w⟩ =
    b66f_gen_b66m_parameterLocalForm R t θ h a ⟨p, w⟩ -
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) a) p) w := by
  apply b66f_gen_b66m_correctedLocalForm_local R t ρ hρ _
    (b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h))
    (b66f_gen_b66m_parameterLocalForm R t θ h)
    (b66f_gen_b66m_parameterLocalForm_overlap R t hU ht θ q hq h) a p ha w

theorem b66f_gen_b66m_correctedParameterForm_smooth (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) :
    ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞
      (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h)) := by
  intro p
  let a : b66f_Index R := p.1.val
  have hp : p.1.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  have hu := b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)
  let S : Set (b65z_fibre c₀ R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  have hS : IsOpen S := b66f_gen_b66m_sc_open_source R t a
  have hτ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) a) S :=
    fun y hy => (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a y hy).contMDiffWithinAt
  have hD := b66f_gen_b66m_realDifferential_smooth R t _ S hS hτ p hp
  have hβ := b66f_gen_b66m_parameterLocalForm_smooth R t hU ht θ h a p hp
  apply (hβ.sub hD).congr_of_eventuallyEq
  have hproj := (FiberBundle.continuous_proj ℂ
    (TangentSpace 𝓘(ℂ, ℂ))).continuousAt (x := p)
  filter_upwards [hproj.preimage_mem_nhds (hS.mem_nhds hp)] with y hy
  exact (b66f_gen_b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ
    a y.1 hy y.2)

theorem b66f_gen_b66m_correctedParameterScalarForm_smooth (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (L : ℂ →L[ℝ] ℝ) :
    b3Forms_IsSmooth (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L) :=
  b66m_scalarTangentForm_smooth _ _ _ L
    (b66f_gen_b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ)

theorem b66f_gen_b66m_coordinateForm_local_primitive (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (a : b66f_Index R) (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A (b66f_domain R t a))
    (p : b65z_fibre c₀ R.C t) (hp : p.val ∈ (R.atlas.A a).source) :
    ∃ (V : Set (b65z_fibre c₀ R.C t)) (F : b65z_fibre c₀ R.C t → ℂ),
      IsOpen V ∧ p ∈ V ∧
      (∀ y ∈ V, y.val ∈ (R.atlas.A a).source ∧
        ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F y) ∧
      ∀ y ∈ V, ∀ w : ℂ,
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y) w =
          A (b66f_gen_b66m_sc_slice R t a y) * b66f_gen_b66m_sc_sliceD R t a y w := by
  let z := b66f_gen_b66m_sc_slice R t a p
  have hdom : IsOpen (b66f_domain R t a) :=
    (R.atlas.A a).open_target.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hdom z
    (b66f_gen_b66m_sc_slice_domain R t a p hp)
  obtain ⟨G, hG⟩ := (show DifferentiableOn ℂ A (Metric.ball z r) from
    fun w hw => (hA w (hball hw)).differentiableAt.differentiableWithinAt).isExactOn_ball
  let S : Set (b65z_fibre c₀ R.C t) := {y | y.val ∈ (R.atlas.A a).source}
  let V : Set (b65z_fibre c₀ R.C t) := S ∩ (b66f_gen_b66m_sc_slice R t a) ⁻¹' Metric.ball z r
  have hS : IsOpen S := b66f_gen_b66m_sc_open_source R t a
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact inter_mem (hS.mem_nhds hy.1)
      ((b66f_gen_b66m_sc_slice_contMDiffAt R t a y hy.1).continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds hy.2))
  have hGc : ∀ w ∈ Metric.ball z r, ContDiffAt ℂ ω G w := by
    intro w hw
    have hd : DifferentiableOn ℂ G (Metric.ball z r) :=
      fun v hv => (hG v hv).differentiableAt.differentiableWithinAt
    exact (hd.analyticOnNhd Metric.isOpen_ball w hw).contDiffAt
  refine ⟨V, G ∘ b66f_gen_b66m_sc_slice R t a, hV, ⟨hp, Metric.mem_ball_self hr⟩,
    fun y hy => ⟨hy.1, (hGc _ hy.2).contMDiffAt.comp y
      (b66f_gen_b66m_sc_slice_contMDiffAt R t a y hy.1)⟩, ?_⟩
  intro y hy w
  have hs := (b66f_gen_b66m_sc_slice_contMDiffAt R t a y hy.1).mdifferentiableAt (by simp)
  have hd := HasMFDerivAt.comp y (hG _ hy.2).hasFDerivAt.hasMFDerivAt hs.hasMFDerivAt
  refine ((b3A_mdifferentiableAt_real hd.mdifferentiableAt).2 w).trans ?_
  rw [hd.mfderiv]
  change b66f_gen_b66m_sc_sliceD R t a y w • A (b66f_gen_b66m_sc_slice R t a y) = _
  exact mul_comm _ _

theorem b66f_gen_b66m_correctedParameterForm_local_primitive (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (p : b65z_fibre c₀ R.C t) :
    ∃ (V : Set (b65z_fibre c₀ R.C t)) (G : b65z_fibre c₀ R.C t → ℂ),
      IsOpen V ∧ p ∈ V ∧
      (∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G y) ∧
      ∀ y ∈ V, ∀ w : ℂ,
        b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
          (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨y, w⟩ =
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G y) w := by
  let a : b66f_Index R := p.val
  have hp : p.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
  obtain ⟨V, F, hV, hpV, hF, hdF⟩ := b66f_gen_b66m_coordinateForm_local_primitive R t a
    (fun w => fderiv ℂ (b66f_gen_b66m_relCoef R θ a) (t.val, w) (h, 0))
    ((b66f_gen_b66m_relCoef_derivative_overlap R hU ht θ q hq h).1 a) p hp
  let T := b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) a
  have hu := b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)
  have hT : ∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ T y :=
    fun y hy => b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a y (hF y hy).1
  have hFr : ∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F y :=
    fun y hy => (b3A_contMDiffWithinAt_real (hF y hy).2.contMDiffWithinAt).of_le (by simp)
  refine ⟨V, F - T, hV, hpV, fun y hy => (hFr y hy).sub (hT y hy), ?_⟩
  intro y hy w
  rw [b66f_gen_b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ a y (hF y hy).1 w]
  have hd := mfderiv_sub ((hFr y hy).mdifferentiableAt (by simp))
    ((hT y hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) hd
  calc
    _ = (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F y) w -
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) T y) w := by
      rw [hdF y hy w]
      rfl
    _ = _ := he.symm

theorem b66f_gen_b66m_correctedParameterScalarForm_d (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (L : ℂ →L[ℝ] ℝ) :
    b3Forms_d (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L) = 0 :=
  b66m_scalarTangentForm_d _ _ _ L
    (b66f_gen_b66m_correctedParameterForm_local_primitive R t hU ht θ q hqf hq h ρ hρ)

def b66f_gen_b66m_correctedParameterClosedForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (L : ℂ →L[ℝ] ℝ) :
    b3Forms_closed ℂ (b65z_fibre c₀ R.C t) 0 :=
  ⟨⟨b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L,
      b66f_gen_b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ L⟩,
    LinearMap.mem_ker.mpr (Subtype.ext
      (b66f_gen_b66m_correctedParameterScalarForm_d R t θ q h ρ hU ht hqf hq hρ L))⟩

def b66f_gen_b66m_correctedParameterHolPairing (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (L : ℂ →L[ℝ] ℝ) :
    b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℝ] ℝ :=
  ((b3Forms_closedPairing (b3Rest_b (Module.finrank_self ℂ)))
    (b66f_gen_b66m_correctedParameterClosedForm R t θ q h ρ hU ht hqf hq hρ L)).comp
      (b3Forms_reClosed (Module.finrank_self ℂ))

def b66f_gen_b66m_contractionSmooth01 (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hqf : q ∈ b66f_forms R t 1) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) : b4c_Smooth01 ℂ (b65z_fibre c₀ R.C t) :=
  ⟨b66f_gen_b66m_sc_gamma R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)),
    b66f_gen_b66m_sc_gamma_mem R t ρ hρ (b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h))⟩

theorem b66f_gen_b66m_correctedParameterScalarForm_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (L : ℂ →L[ℝ] ℝ)
    (p : b65z_fibre c₀ R.C t) (v : ℂ) :
    b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L p (fun _ => v) =
      L (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, v⟩) := rfl

theorem b66f_gen_b66m_correctedLocalForm_antilinear (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (u : b66f_Cochain R)
    (β : b66f_Index R → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ)
    (hβ : ∀ a (p : b65z_fibre c₀ R.C t) (w : ℂ),
      β a ⟨p, Complex.I • w⟩ = Complex.I * β a ⟨p, w⟩)
    (p : b65z_fibre c₀ R.C t) (w : ℂ) :
    (b66f_gen_b66m_correctedLocalForm R t ρ u β ⟨p, w⟩ + Complex.I *
      b66f_gen_b66m_correctedLocalForm R t ρ u β ⟨p, Complex.I • w⟩) / 2 =
      -b66f_gen_b66m_sc_gamma R t ρ u ⟨p, w⟩ := by
  simp only [b66f_gen_b66m_correctedLocalForm, b66f_gen_b66m_sc_gamma, b4c_dbar, hβ]
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul, smul_eq_mul]
  ring_nf

theorem b66f_gen_b66m_correctedParameterForm_antilinear (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (p : b65z_fibre c₀ R.C t) (w : ℂ) :
    (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, w⟩ + Complex.I *
      b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, Complex.I • w⟩) / 2 =
      -b66f_gen_b66m_sc_gamma R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) ⟨p, w⟩ := by
  apply b66f_gen_b66m_correctedLocalForm_antilinear
  intro a y v
  simp only [b66f_gen_b66m_parameterLocalForm, smul_eq_mul]
  rw [b66m_rs_clm_apply (b66f_gen_b66m_sc_sliceD R t a y) (Complex.I * v),
    b66m_rs_clm_apply (b66f_gen_b66m_sc_sliceD R t a y) v]
  ring

theorem b66f_gen_b66m_contraction_re01 (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hqf : q ∈ b66f_forms R t 1) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) :
    RiemannRochAna_re01 (b66f_gen_b66m_contractionSmooth01 R t q h ρ hqf hρ) =
      (-1 / 2 : ℝ) • (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM +
        b3Forms_star (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)) := by
  funext p
  ext v
  have hv : v = fun _ => v 0 := by funext i; fin_cases i; rfl
  rw [hv]
  change (b66f_gen_b66m_sc_gamma R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) ⟨p, v 0⟩).re = _
  simp only [Pi.smul_apply, Pi.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, b3Forms_star, b3Forms_starPt_apply,
    b66f_gen_b66m_correctedParameterScalarForm_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul]
  have he := congrArg Complex.re (b66f_gen_b66m_correctedParameterForm_antilinear R t θ q h ρ p (v 0))
  simp at he
  linarith

theorem b66f_gen_b66m_pairing_star_reForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (α : b65z_fibre c₀ R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ)
    (η : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) (b3Forms_star α) (b3Forms_reForm η) =
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α (b3Forms_reForm (Complex.I • η)) := by
  have he : b3Forms_wedgeForm (b3Forms_star α) (b3Forms_reForm η) =
      (-1 : ℝ) • b3Forms_wedgeForm α (b3Forms_imForm η) := by
    rw [← b3Forms_star_reForm]
    funext p
    change b3Forms_wedge (b3Forms_starPt (α p)) (b3Forms_reForm η p) =
      (-1 : ℝ) • b3Forms_wedge (α p) (b3Forms_starPt (b3Forms_reForm η p))
    rw [b3Forms_wedge_comm (b3Forms_reForm η p),
      b3Forms_wedge_starPt_comm (Module.finrank_self ℂ)]
    simp only [neg_one_smul]
  rw [b3Forms_pairing, he, b3Forms_integral_smul, b3Rest2_reForm_I,
    b3Forms_pairing_smul_right]
  rfl

theorem b66f_gen_b66m_contraction_dolbeault_pairing (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (η : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_dolbeaultIntegral R t (b66f_gen_b66m_contractionSmooth01 R t q h ρ hqf hρ) η =
      -(b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM) (b3Forms_reForm η) : ℂ) -
      (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
        (b3Forms_reForm (Complex.I • η)) : ℂ) +
      Complex.I * ((b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM)
        (b3Forms_reForm (Complex.I • η)) : ℂ) -
        (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
          (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
          (b3Forms_reForm η) : ℂ)) := by
  let α := b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM
  let δ := b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM
  have hα := b66f_gen_b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
  have hδ := b66f_gen_b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
  change 2 * ((b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (RiemannRochAna_re01 (b66f_gen_b66m_contractionSmooth01 R t q h ρ hqf hρ))
      (b3Forms_reForm η) : ℂ) - Complex.I *
      (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (RiemannRochAna_re01 (b66f_gen_b66m_contractionSmooth01 R t q h ρ hqf hρ))
        (b3Forms_reForm (Complex.I • η)) : ℂ)) = _
  rw [b66f_gen_b66m_contraction_re01 R t θ q h ρ hqf hρ]
  rw [b3Forms_pairing_smul_left, b3Forms_pairing_smul_left,
    b3Forms_pairing_add_left _ hα hδ.star (b3Forms_isSmooth_reForm η),
    b3Forms_pairing_add_left _ hα hδ.star (b3Forms_isSmooth_reForm (Complex.I • η)),
    b66f_gen_b66m_pairing_star_reForm R t _ η, b66f_gen_b66m_pairing_star_reForm R t _ (Complex.I • η),
    b3Rest2_I_I]
  have hn : b3Forms_reForm (-η) = (-1 : ℝ) • b3Forms_reForm η := by
    rw [← b3Forms_reForm_smul, neg_one_smul]
  rw [hn, b3Forms_pairing_smul_right]
  push_cast
  ring

theorem b66f_gen_b66m_polarizedHarmonicForm_functional (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) [Fintype ι] [DecidableEq ι]
    (A D : b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℝ] ℝ)
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (hy : y ∈ b3_periodF ℂ (b65z_fibre c₀ R.C t)) :
    -(A (b66f_gen_b66m_polarizedHarmonicForm R t b y) : ℂ) -
      (D (Complex.I • b66f_gen_b66m_polarizedHarmonicForm R t b y) : ℂ) +
      Complex.I * ((A (Complex.I • b66f_gen_b66m_polarizedHarmonicForm R t b y) : ℂ) -
        (D (b66f_gen_b66m_polarizedHarmonicForm R t b y) : ℂ)) =
      ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
        ((A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
          Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  let c := (Algebra.TensorProduct.basis ℂ b).equivFun y
  let u := b3Rest2_uR (Module.finrank_self ℂ) b c
  let v := b3Rest2_uI (Module.finrank_self ℂ) b c
  have hv : v = -(Complex.I • u) := by
    simpa only [neg_smul] using b3Rest2_uI_of_mem_F (Module.finrank_self ℂ) b hy
  have hA : A v = -A (Complex.I • u) := by rw [hv, map_neg]
  have hD : D v = -D (Complex.I • u) := by rw [hv, map_neg]
  rw [b66m_complex_real_period_sum]
  have hAu : A u = ∑ i, (c i).re * A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [u, b3Rest2_uR, map_sum, map_smul, smul_eq_mul]
  have hAv : A v = ∑ i, (c i).im * A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [v, b3Rest2_uI, map_sum, map_smul, smul_eq_mul]
  have hDu : D u = ∑ i, (c i).re * D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [u, b3Rest2_uR, map_sum, map_smul, smul_eq_mul]
  have hDv : D v = ∑ i, (c i).im * D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) := by
    simp only [v, b3Rest2_uI, map_sum, map_smul, smul_eq_mul]
  change -(A (-u) : ℂ) - (D (Complex.I • -u) : ℂ) +
    Complex.I * ((A (Complex.I • -u) : ℂ) - (D (-u) : ℂ)) = _
  rw [← hAu, ← hDv, ← hDu, ← hAv, hA, hD]
  simp only [map_neg, smul_neg, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add]
  ring

theorem b66f_gen_b66m_contraction_cech_full_functional (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) [Fintype ι] [DecidableEq ι]
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (hy : y ∈ b3_periodF ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_cechTrace R t ρ hρ (b66f_gen_b66m_sc_cechProjection R t
      ⟨b66f_gen_b66g_contract R q (b66f_cocycle R t h),
        b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)⟩)
      (b66f_gen_b66m_polarizedHarmonicForm R t b y) =
    ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
      ((b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
        (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
      Complex.I * (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
        (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  rw [b66f_gen_b66m_cechTrace_cycle]
  change b66f_gen_b66m_dolbeaultIntegral R t (b66f_gen_b66m_contractionSmooth01 R t q h ρ hqf hρ) _ = _
  rw [b66f_gen_b66m_contraction_dolbeault_pairing R t θ q h ρ hU ht hqf hq hρ]
  exact b66f_gen_b66m_polarizedHarmonicForm_functional R t b
    (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
    (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM) y hy

theorem b66f_gen_b66m_complexPeriodFunctional_tmul (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (A D : b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℝ] ℝ)
    (c : ℂ) (l : b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_complexPeriodFunctional R t A D (c ⊗ₜ[ℤ] l) =
      c * ((A (b3Rest2_θ (Module.finrank_self ℂ) l) : ℂ) +
        Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) l) : ℂ)) := by
  rw [b66f_gen_b66m_complexPeriodFunctional, LinearMap.liftBaseChange_tmul]
  rfl

theorem b66f_gen_b66m_complexPeriodFunctional_coords (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) [Fintype ι] [DecidableEq ι]
    (A D : b3_HolForm ℂ (b65z_fibre c₀ R.C t) →ₗ[ℝ] ℝ)
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_complexPeriodFunctional R t A D y =
      ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun y i *
        ((A (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ) +
          Complex.I * (D (b3Rest2_θ (Module.finrank_self ℂ) (b i)) : ℂ)) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis ℂ b).sum_equivFun y]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, b3Rest2_tmulBasis (Module.finrank_self ℂ) b,
    b66f_gen_b66m_complexPeriodFunctional_tmul]
  simp only [one_mul, smul_eq_mul]

theorem b66f_gen_b66m_contraction_cech_functional (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {ι : Type} (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t))) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) [Fintype ι] [DecidableEq ι]
    (y : ℂ ⊗[ℤ] b3_periodLattice ℂ (b65z_fibre c₀ R.C t))
    (hy : y ∈ b3_periodF ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66m_cechTrace R t ρ hρ (b66f_gen_b66m_sc_cechProjection R t
      ⟨b66f_gen_b66g_contract R q (b66f_cocycle R t h),
        b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)⟩)
      (b66f_gen_b66m_polarizedHarmonicForm R t b y) =
    b66f_gen_b66m_complexPeriodFunctional R t
      (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
      (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM) y := by
  rw [b66f_gen_b66m_contraction_cech_full_functional R t b θ q h ρ hU ht hqf hq hρ y hy,
    b66f_gen_b66m_complexPeriodFunctional_coords R t b]

theorem b66f_gen_b66m_retained_cover (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    ∃ (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
      (a : ℤ → b66f_Index R),
      (∀ k, K.φ k = R.atlas.A (a k)) ∧ ∀ k, a (k + K.N) = a k := by
  have hΓ : Continuous (fun τ => ((t, c τ) : b6t_polydisc c₀ × R.C)) :=
    continuous_const.prodMk hc
  have hΓp : Function.Periodic (fun τ => ((t, c τ) : b6t_polydisc c₀ × R.C)) 1 :=
    fun τ => by simp only [hcp τ]
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b63e_exists_chartCover R.atlas.A (fun q => (R.atlas.hA q).1) _ hΓ hΓp
  let K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)) := {
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

theorem b66f_gen_b66m_retained_loopClass (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {c : ℝ → R.C} (hc : Continuous c)
    (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ))) :
    b6m_loopClass (b65z_fibre c₀ R.C t)
      (K.loopF (b6t_polydisc c₀) (Subset.refl _) t (R.hincl t) K.cond_u₀) =
      b63e_fibreLoopClass c₀ R.C t hc hcp := by
  rw [b63e_loopClass_eq_fibreLoopClass_param]
  have hhom : Continuous fun p : unitInterval × ℝ => (K.hom p).2 :=
    continuous_snd.comp K.continuous_hom
  have hhomp : ∀ l, Function.Periodic (fun τ => (K.hom (l, τ)).2) 1 :=
    fun l τ => by simp only [K.hom_periodic l τ]
  have hd : Continuous fun τ => (K.floorLoop t.val ((K.N : ℝ) * τ)).2 := by
    have hh := hhom.comp (continuous_const.prodMk continuous_id :
      Continuous fun τ : ℝ => ((1 : unitInterval), τ))
    exact hh.congr fun τ => congrArg Prod.snd (K.hom_one τ)
  have hdp : Function.Periodic (fun τ => (K.floorLoop t.val ((K.N : ℝ) * τ)).2) 1 :=
    fun τ => by simp only [K.floorLoop_periodic _ τ]
  have he := b63e_fibreLoopClass_homotopy' c₀ R.C t _ hhom hhomp hc hcp hd hdp
    (fun τ => by rw [K.hom_zero]) (fun τ => by rw [K.hom_one])
  apply Eq.trans ?_ he.symm
  apply b63e_fibreLoopClass_congr
  intro τ
  exact congrArg Prod.snd (K.loopF_val (b6t_polydisc c₀) (Subset.refl _)
    t (R.hincl t) K.cond_u₀ τ)

theorem b66f_gen_b66m_closedForm_lattice_pairing (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (α : b65z_fibre c₀ R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) (γ : b3_SmoothLoop ℂ (b65z_fibre c₀ R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (b65z_fibre c₀ R.C t) γ))) =
      b3Forms_lineIntegral α γ.val 0 1 := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  obtain ⟨η, hη, hdη, hdual⟩ := b3Rest2_exists_dual (Module.finrank_self ℂ) γ
  obtain ⟨φ, g, hg, heq⟩ := b3Rest_hodge hη hdη
  have hφ := b3Rest2_θ_eq_of_dual (Module.finrank_self ℂ) γ hη hdual hg heq
  have hp := hdual α hα hdα
  change b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α η = _ at hp
  rw [heq, hφ, b3Forms_pairing_add_right _ hα (b3Forms_isSmooth_reForm _) hg.d,
    b3Forms_pairing_comm _ (b3Forms_d (b3Forms_fun (E := ℂ) g)) α,
    b3Forms_integral_wedge_d_eq_zero _ b3Forms_oriented_complex hg hα hdα,
    neg_zero, add_zero] at hp
  exact hp

theorem b66f_gen_b66m_correctedParameterScalarForm_lattice_pairing (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (L : ℂ →L[ℝ] ℝ)
    (γ : b3_SmoothLoop ℂ (b65z_fibre c₀ R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L)
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (b65z_fibre c₀ R.C t) γ))) =
      L (b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) γ.val
        (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
          (b66f_gen_b66m_parameterLocalForm R t θ h))) := by
  rw [b66f_gen_b66m_closedForm_lattice_pairing R t _
    (b66f_gen_b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ L)
    (b66f_gen_b66m_correctedParameterScalarForm_d R t θ q h ρ hU ht hqf hq hρ L)]
  exact b66m_scalarTangentForm_lineIntegral _ _ _ L
    (b66f_gen_b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ) γ.val γ.property.2

theorem b66f_gen_b66m_flat_loop_period (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀)
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1) :
    b63e_periodFunction c₀ R.C (b6t_polydisc c₀) (Subset.refl _) R.P θ s
      (b63e_fibreLoopClass c₀ R.C s hc hcp) =
      fun u => if hu : u ∈ b6t_polydisc c₀ then
        (R.P ⟨u, hu⟩ (b63e_fibreLoopClass c₀ R.C ⟨u, hu⟩ hc hcp)).val
          (b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
            θ ⟨u, hu⟩) else 0 := by
  funext u
  unfold b63e_periodFunction
  split_ifs with hu
  · rw [b63e_fibreLoopClass_transport]
  · rfl

theorem b66f_gen_b66m_pathIntegral_differential (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (f : b65z_fibre c₀ R.C t → ℂ)
    (γ : ℝ → b65z_fibre c₀ R.C t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (hf : ∀ s : ℝ, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 f (γ s)) :
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) γ
      (fun p => (show ℂ →L[ℝ] ℂ from
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f p.1) p.2) = f (γ 1) - f (γ 0) := by
  have hd : ∀ s : ℝ, HasDerivAt (f ∘ γ)
      ((show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s))
        (b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s)) s := by
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
        (b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s)) MeasureTheory.volume 0 1 := by
    have heq : (fun s =>
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f (γ s))
          (b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s)) = deriv (f ∘ γ) :=
      funext fun s => (hd s).deriv.symm
    rw [heq]
    exact (hc.continuous_deriv (by simp)).intervalIntegrable _ _
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

theorem b66f_gen_b66m_correctedParameterForm_pathIntegral (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (a : b66f_Index R) (γ : ℝ → b65z_fibre c₀ R.C t)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
    (hsrc : ∀ s : ℝ, (γ s).val ∈ (R.atlas.A a).source) :
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) γ
      (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h)) =
      b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) γ (b66f_gen_b66m_parameterLocalForm R t θ h a) -
        (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) a (γ 1) -
          b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) a (γ 0)) := by
  let u := b66f_gen_b66g_contract R q (b66f_cocycle R t h)
  let F := b66f_gen_b66m_sc_tau R t ρ u a
  let D : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ := fun p =>
    (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F p.1) p.2
  have hu := b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)
  have hF : ∀ s, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F (γ s) :=
    fun s => b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a (γ s) (hsrc s)
  have hd := b66f_gen_b66m_pathIntegral_differential R t F γ hγ
    (fun s => (hF s).of_le (by simp))
  have hvel := b3A_continuous_velocity γ hγ
  have hβ : Continuous (fun s => b66f_gen_b66m_parameterLocalForm R t θ h a
      ⟨γ s, b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s⟩) :=
    continuous_iff_continuousAt.2 fun s =>
      (b66f_gen_b66m_parameterLocalForm_smooth R t hU ht θ h a _ (hsrc s)).continuousAt.comp
        hvel.continuousAt
  have hD : Continuous (fun s => D ⟨γ s, b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s⟩) := by
    apply continuous_iff_continuousAt.2
    intro s
    have hFs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F
        {y | y.val ∈ (R.atlas.A a).source} :=
      fun y hy => (b66f_gen_b66m_sc_tau_smooth R t ρ hρ hu a y hy).contMDiffWithinAt
    have hc : ContinuousAt D ⟨γ s, b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s⟩ :=
      (b66f_gen_b66m_realDifferential_smooth R t F _ (b66f_gen_b66m_sc_open_source R t a)
        hFs ⟨γ s, b3_velocity ℂ (b65z_fibre c₀ R.C t) γ s⟩ (hsrc s)).continuousAt
    exact hc.comp (f := fun r =>
      (⟨γ r, b3_velocity ℂ (b65z_fibre c₀ R.C t) γ r⟩ :
        TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t))) hvel.continuousAt
  change _ = _ - (F (γ 1) - F (γ 0))
  rw [← hd]
  unfold b3_pathIntegral
  rw [← intervalIntegral.integral_sub (hβ.intervalIntegrable _ _) (hD.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _
  exact b66f_gen_b66m_correctedParameterForm_local R t hU ht θ q hqf hq h ρ hρ a
    (γ s) (hsrc s) _

theorem b66f_gen_b66m_parameterLocalForm_segment_integral (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (h : Fin 10 → ℂ) {c : ℝ → R.C}
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) (k : ℤ) :
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t)
      (K.segF (b6t_polydisc c₀) (Subset.refl _) t k)
      (b66f_gen_b66m_parameterLocalForm R t θ h (a k)) =
    ∫ s in (0 : ℝ)..1,
      fderiv ℂ (b66f_gen_b66m_relCoef R θ (a k))
        (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k)) (h, 0) *
          (K.bb k t.val - K.a k) := by
  apply b63e_slice_segment_integral c₀ R.C (b6t_polydisc c₀)
    (Subset.refl _) t (R.hincl t) (K.mem_atlas k) (K.fp k)
    (b66f_gen_b66m_parameterLocalForm R t θ h (a k))
    (fun z => fderiv ℂ (b66f_gen_b66m_relCoef R θ (a k)) z (h, 0)) ?_
    (K.a k) (K.bb k t.val) (fun s hs => K.ball_sub k (K.segment_mem K.cond_u₀ k hs)) ?_
  · intro p hp w
    have hpa : p.val ∈ (R.atlas.A (a k)).source := by rwa [← hφ k]
    have hf : (fun y : b65z_fibre c₀ R.C t => (K.φ k y.val).2) =
        b66f_gen_b66m_sc_slice R t (a k) := by
      funext y
      rw [hφ k]
      rfl
    rw [hf, hφ k, b66f_gen_b66m_sc_slice_value R t (a k) p hpa]
    rfl
  · intro s hs
    have hp := K.ball_sub k (K.segment_mem K.cond_u₀ k hs)
    rw [hφ k] at hp
    have han := b66f_gen_b66m_relCoef_analytic R hU θ (a k) _ ⟨hp, t.property, ht⟩
    exact han.fderiv.continuousAt.clm_apply continuousAt_const

theorem b66f_gen_b66m_endpoint_cocycle (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {c : ℝ → R.C} (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (k : ℤ) (h : Fin 10 → ℂ) :
    fderiv ℂ (K.bb k) t.val h =
      b66f_cocycle R t h (a (k + 1)) (a k) (K.v (k + 1) t.val).2 := by
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
  have hd := ((b66f_gen_b66k_transition_analytic R _ _ _ htrans).differentiableAt.hasFDerivAt).comp
    t.val (hasFDerivAt_prodMk_left (𝕜 := ℂ) t.val (K.a (k + 1)))
  have hfun : K.bb k = (b66f_transition R (a (k + 1)) (a k)) ∘
      (fun u : Fin 10 → ℂ => (u, K.a (k + 1))) := by
    funext u
    simp only [b63e_Cover.bb, b63e_Cover.v, b66f_transition, Function.comp_apply, hφ]
  rw [hfun, hd.fderiv]
  change fderiv ℂ (b66f_transition R (a (k + 1)) (a k))
    (t.val, K.a (k + 1)) (h, 0) = b66f_cocycle R t h (a (k + 1)) (a k) x
  simp only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, x) ∈ (R.atlas.A (a (k + 1))).source ∩
      (R.atlas.A (a k)).source from ⟨ha, hb⟩), hcoord]

theorem b66f_gen_b66m_endpoint_contraction (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {c : ℝ → R.C} (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ)
    (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) (q : b66f_Coeff R)
    (hA : ∀ k (p : b65z_fibre c₀ R.C t), p.val ∈ (K.φ k).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = A k (K.φ k p.val) * b66f_gen_b66m_sc_sliceD R t (a k) p w)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (k : ℤ) (h : Fin 10 → ℂ) :
    A k (t.val, K.bb k t.val) * fderiv ℂ (K.bb k) t.val h =
      b66f_gen_b66g_contract R q (b66f_cocycle R t h) (a (k + 1)) (a k)
        (K.v (k + 1) t.val).2 := by
  let p := b66f_gen_b66m_sc_pt R t (K.v (k + 1) t.val).2
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
  have hn : b66f_gen_b66m_sc_sliceD R t (a k) p 1 ≠ 0 := by
    intro hz
    apply (b66f_gen_b66g_slice_coordinate R t (a k)).2 p hpa
    ext1
    exact hz
  have heq := (hA k p hpk 1).symm.trans (hq (a k) p hpa 1)
  rw [hcoord] at heq
  have heq' := mul_right_cancel₀ hn heq
  rw [heq', b66f_gen_b66m_endpoint_cocycle R t K a hφ k h]
  rfl

theorem b66f_gen_b66m_retained_period_derivative (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) :
    ∃ A : ℤ → (Fin 10 → ℂ) × ℂ → ℂ,
      (∀ k, AnalyticOn ℂ (A k)
        ((K.φ k).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U)) ∧
        ∀ (u : b6t_polydisc c₀) (p : b65z_fibre c₀ R.C u), u.val ∈ U →
          p.val ∈ (K.φ k).source → ∀ w : ℂ,
          θ.val u ⟨p, w⟩ = A k (K.φ k p.val) * (show ℂ from
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
              (fun y : b65z_fibre c₀ R.C u => (K.φ k y.val).2) p w)) ∧
      ∀ h : Fin 10 → ℂ,
        fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc c₀ then
          (R.P ⟨u, hu⟩ (b63e_fibreLoopClass c₀ R.C ⟨u, hu⟩ hc hcp)).val
            (b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
              θ ⟨u, hu⟩) else 0) t.val h =
        (∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
          fderiv ℂ (A k) (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k))
            (h, 0) * (K.bb k t.val - K.a k)) +
        ∑ k ∈ Finset.range K.N,
          b66f_gen_b66g_contract R q (b66f_cocycle R t h) (a (k + 1)) (a k)
            (K.v (k + 1) t.val).2 := by
  obtain ⟨A, hA, hb, _, heq⟩ := b66m_moving_period_integrals c₀ R.C
    (b6t_polydisc c₀) (Subset.refl _) (rf5_polydisc_isOpen c₀)
    R.hincl R.P R.hP U hU θ t ht hc hcp K
  refine ⟨A, hA, fun h => ?_⟩
  have hd := b66m_polygon_period_fderiv (Finset.range K.N)
    (fun k : ℕ => A k) (fun k : ℕ => K.bb k) (fun k : ℕ => K.a k) t.val _
    (fun k _ => hb k) (fun k _ => ?_) heq h
  · rw [hd]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    apply b66f_gen_b66m_endpoint_contraction R t K a hφ A (b63e_relFormAt c₀ R.C
      (b6t_polydisc c₀) (Subset.refl _) θ t) q
    · intro j p hp w
      have he := (hA j).2 t p ht hp w
      have hf : (fun y : b65z_fibre c₀ R.C t => (K.φ j y.val).2) =
          b66f_gen_b66m_sc_slice R t (a j) := by
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
        (((rf5_polydisc_isOpen c₀).inter hU).preimage continuous_fst)).mem_nhds
        ⟨hp, t.property, ht⟩)

theorem b66f_gen_b66m_relCoef_unique (R : b65z_SharedFamily c₀ g₀) {U : Set (Fin 10 → ℂ)}
    (hU : IsOpen U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (a : b66f_Index R) (A : (Fin 10 → ℂ) × ℂ → ℂ)
    (hA : ∀ (u : b6t_polydisc c₀) (p : b65z_fibre c₀ R.C u), u.val ∈ U →
      p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
        θ.val u ⟨p, w⟩ = A (R.atlas.A a p.val) * b66f_gen_b66m_sc_sliceD R u a p w)
    (z : (Fin 10 → ℂ) × ℂ)
    (hz : z ∈ (R.atlas.A a).target ∩ Prod.fst ⁻¹' (b6t_polydisc c₀ ∩ U)) :
    A =ᶠ[𝓝 z] b66f_gen_b66m_relCoef R θ a := by
  filter_upwards [(b66f_gen_b66m_relCoef_open R hU a).mem_nhds hz] with y hy
  let u : b6t_polydisc c₀ := ⟨y.1, hy.2.1⟩
  let p := b66f_gen_b66m_sc_pt R u ((R.atlas.A a).symm (u.val, y.2)).2
  have hp : p.val = (R.atlas.A a).symm y :=
    b66f_gen_b66k_inverse_slice R u a y.2 hy.1
  have hpa : p.val ∈ (R.atlas.A a).source := by
    rw [hp]
    exact (R.atlas.A a).map_target hy.1
  have hcoord : R.atlas.A a p.val = y := by
    rw [hp, (R.atlas.A a).right_inv hy.1]
  have he := (hA u p hy.2.2 hpa 1).symm.trans
    (b66f_gen_b66m_relCoef_spec R θ a u p hy.2.2 hpa 1)
  have hs : (u.val, b66f_gen_b66m_sc_slice R u a p) = y := by
    change (u.val, (R.atlas.A a p.val).2) = y
    rw [← b66f_gen_b66m_sc_slice_value R u a p hpa]
    exact hcoord
  rw [hcoord, hs] at he
  exact mul_right_cancel₀ (b66f_gen_b66m_sliceD_one_ne R u a p hpa) he

theorem b66f_gen_b66m_retained_coefficient_derivative (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (U : Set (Fin 10 → ℂ)) (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k)) :
    ∀ h : Fin 10 → ℂ,
        fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc c₀ then
          (R.P ⟨u, hu⟩ (b63e_fibreLoopClass c₀ R.C ⟨u, hu⟩ hc hcp)).val
            (b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
              θ ⟨u, hu⟩) else 0) t.val h =
        (∑ k ∈ Finset.range K.N, ∫ s in (0 : ℝ)..1,
          fderiv ℂ (b66f_gen_b66m_relCoef R θ (a k)) (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k))
            (h, 0) * (K.bb k t.val - K.a k)) +
        ∑ k ∈ Finset.range K.N,
          b66f_gen_b66g_contract R q (b66f_cocycle R t h) (a (k + 1)) (a k)
            (K.v (k + 1) t.val).2 := by
  obtain ⟨A, hA, hd⟩ := b66f_gen_b66m_retained_period_derivative R t U hU ht θ q hq hc hcp K a hφ
  intro h
  rw [hd h]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le zero_le_one] at hr
  have heq := b66f_gen_b66m_relCoef_unique R hU θ (a k) (A k) ?_
    (t.val, K.a k + (r : ℂ) * (K.bb k t.val - K.a k)) ?_
  · exact congrArg (fun L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ =>
      L (h, 0) * (K.bb k t.val - K.a k)) (heq.fderiv_eq (𝕜 := ℂ))
  · intro u p hu hp w
    have hp' : p.val ∈ (K.φ k).source := by rwa [hφ k]
    have he := (hA k).2 u p hu hp' w
    have hf : (fun y : b65z_fibre c₀ R.C u => (K.φ k y.val).2) =
        b66f_gen_b66m_sc_slice R u (a k) := by
      funext y
      rw [hφ k]
      rfl
    rw [hf, hφ k] at he
    exact he
  · refine ⟨?_, t.property, ht⟩
    rw [← hφ k]
    exact K.ball_sub k (K.segment_mem K.cond_u₀ k hr)

theorem b66f_gen_b66m_real_integral_reparam (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ)
    (hθ : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ θ)
    (hlin : ∀ (p : b65z_fibre c₀ R.C t) (c : ℝ) (v : ℂ),
      θ ⟨p, c • v⟩ = c • θ ⟨p, v⟩)
    (γ : ℝ → b65z_fibre c₀ R.C t) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ)
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

theorem b66f_gen_b66m_real_floorLoop_pathIntegral (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ)
    (hθ : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ θ)
    (hlin : ∀ (p : b65z_fibre c₀ R.C t) (c : ℝ) (v : ℂ),
      θ ⟨p, c • v⟩ = c • θ ⟨p, v⟩) (N : ℕ) (γ : ℤ → ℝ → b65z_fibre c₀ R.C t) (z : ℤ → b65z_fibre c₀ R.C t)
    (hγ : ∀ k, b3A_IsGoodPath (E := ℂ) (γ k) (z k) (z (k + 1))) :
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) (fun t ↦ γ ⌊(N : ℝ) * t⌋ (Int.fract ((N : ℝ) * t))) θ =
      ∑ k ∈ Finset.range N, b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) (γ k) θ := by
  set L : ℝ → b65z_fibre c₀ R.C t := fun u ↦ γ ⌊u⌋ (Int.fract u)
  have hL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 L := b3Rest_floorPath_contMDiff γ z hγ
  have hσ : ContDiff ℝ 1 (fun t : ℝ ↦ (N : ℝ) * t) := contDiff_const.mul contDiff_id
  have h1 := b66f_gen_b66m_real_integral_reparam R t θ hθ hlin L hL (fun t : ℝ ↦ (N : ℝ) * t) hσ 0 1
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
    b66f_gen_b66m_real_integral_reparam R t θ hθ hlin (γ k) (hγ k).1 (fun t ↦ t - k) (contDiff_id.sub contDiff_const)]
  simp only [sub_self, add_sub_cancel_left]
  rfl

theorem b66f_gen_b66m_correctedParameterForm_real_smul (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (p : b65z_fibre c₀ R.C t) (c : ℝ) (v : ℂ) :
    b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
      (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, c • v⟩ =
      c • b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h) ⟨p, v⟩ := by
  obtain ⟨V, G, _, hp, _, hG⟩ :=
    b66f_gen_b66m_correctedParameterForm_local_primitive R t hU ht θ q hqf hq h ρ hρ p
  rw [hG p hp (c • v), hG p hp v]
  exact (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G p).map_smul c v

theorem b66f_gen_b66m_polygon_potential_endpoints (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (u : b66f_Cochain R) (hu : u ∈ b66f_gen_b66g_scalarCycles R t)
    {c : ℝ → R.C} (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    (∑ k ∈ Finset.range K.N,
      (b66f_gen_b66m_sc_tau R t ρ u (a k)
        (b66f_gen_b66m_sc_pt R t (K.v (k + 1) t.val).2) -
      b66f_gen_b66m_sc_tau R t ρ u (a k)
        (b66f_gen_b66m_sc_pt R t (K.v k t.val).2))) =
      -∑ k ∈ Finset.range K.N,
        u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 := by
  let p : ℤ → b65z_fibre c₀ R.C t := fun k => b66f_gen_b66m_sc_pt R t (K.v k t.val).2
  have hp : ∀ k, (p k).val = K.v k t.val := by
    intro k
    apply Prod.ext
    · rw [K.v_u₀]
      rfl
    · rfl
  let F : ℕ → ℂ := fun k => b66f_gen_b66m_sc_tau R t ρ u (a k) (p k)
  have hperiod : F K.N = F 0 := by
    have haN : a (K.N : ℤ) = a 0 := by simpa using ha 0
    have hpN : p (K.N : ℤ) = p 0 := by
      apply Subtype.ext
      rw [hp, hp]
      simpa using K.v_add 0 t.val
    simp only [F, haN, hpN, Nat.cast_zero]
  have hterm : ∀ k : ℕ,
      b66f_gen_b66m_sc_tau R t ρ u (a k) (p (k + 1)) -
        b66f_gen_b66m_sc_tau R t ρ u (a k) (p k) =
      -u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 + (F (k + 1) - F k) := by
    intro k
    have hpa : (p (k + 1)).val ∈ (R.atlas.A (a k)).source := by
      rw [hp, ← hφ k]
      exact (K.cond_u₀ k).2.1
    have hpb : (p (k + 1)).val ∈ (R.atlas.A (a (k + 1))).source := by
      rw [hp, ← hφ (k + 1)]
      exact (K.φ (k + 1)).map_target (K.ball_sub (k + 1) (K.cond_u₀ (k + 1)).1)
    have he := b66f_gen_b66m_sc_tau_sub R t ρ hρ hu (a (k + 1)) (a k)
      (p (k + 1)) hpb hpa
    change _ - _ = u (a (k + 1)) (a k) (K.v (k + 1) t.val).2 at he
    simp only [F, Nat.cast_add, Nat.cast_one]
    linear_combination -he
  change (∑ k ∈ Finset.range K.N,
    (b66f_gen_b66m_sc_tau R t ρ u (a k) (p (k + 1)) -
      b66f_gen_b66m_sc_tau R t ρ u (a k) (p k))) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_range_sub F, hperiod, sub_self, add_zero]

theorem b66f_gen_b66m_correctedParameterForm_polygon_period (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    fderiv ℂ (fun u => if hu : u ∈ b6t_polydisc c₀ then
      (R.P ⟨u, hu⟩ (b63e_fibreLoopClass c₀ R.C ⟨u, hu⟩ hc hcp)).val
        (b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
          θ ⟨u, hu⟩) else 0) t.val h =
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t)
      (K.loopF (b6t_polydisc c₀) (Subset.refl _) t (R.hincl t) K.cond_u₀).1
      (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h)) := by
  let γ := K.segF (b6t_polydisc c₀) (Subset.refl _) t
  let B := b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
    (b66f_gen_b66m_parameterLocalForm R t θ h)
  have hg := K.segF_good (b6t_polydisc c₀) (Subset.refl _) t (R.hincl t) K.cond_u₀
  have hp : ∀ k, (b66f_gen_b66m_sc_pt R t (K.v k t.val).2).val = K.v k t.val := by
    intro k
    apply Prod.ext
    · rw [K.v_u₀]
      rfl
    · rfl
  have hsrc : ∀ k s, (γ k s).val ∈ (R.atlas.A (a k)).source := by
    intro k s
    change (K.segF (b6t_polydisc c₀) (Subset.refl _) t k s).val ∈ _
    rw [K.segF_val _ _ _ K.cond_u₀, ← hφ k]
    exact (K.φ k).map_target (K.ball_sub k (K.w_mem K.cond_u₀ k s))
  have hzero : ∀ k, γ k 0 = b66f_gen_b66m_sc_pt R t (K.v k t.val).2 := by
    intro k
    apply Subtype.ext
    change (K.segF (b6t_polydisc c₀) (Subset.refl _) t k 0).val = _
    rw [K.segF_val _ _ _ K.cond_u₀, K.seg_zero k (by norm_num)]
    exact (hp k).symm
  have hone : ∀ k, γ k 1 = b66f_gen_b66m_sc_pt R t (K.v (k + 1) t.val).2 := by
    intro k
    apply Subtype.ext
    change (K.segF (b6t_polydisc c₀) (Subset.refl _) t k 1).val = _
    rw [K.segF_val _ _ _ K.cond_u₀, K.seg_one K.cond_u₀ k (by norm_num)]
    exact (hp (k + 1)).symm
  have hs : ∀ k : ℤ, b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) (γ k) B =
      (∫ s in (0 : ℝ)..1, fderiv ℂ (b66f_gen_b66m_relCoef R θ (a k))
        (t.val, K.a k + (s : ℂ) * (K.bb k t.val - K.a k)) (h, 0) *
          (K.bb k t.val - K.a k)) -
      (b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) (a k)
        (b66f_gen_b66m_sc_pt R t (K.v (k + 1) t.val).2) -
      b66f_gen_b66m_sc_tau R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h)) (a k)
        (b66f_gen_b66m_sc_pt R t (K.v k t.val).2)) := by
    intro k
    have he := b66f_gen_b66m_correctedParameterForm_pathIntegral R t hU ht θ q hqf hq h ρ hρ
      (a k) (γ k) (hg k).1 (hsrc k)
    rw [hone, hzero] at he
    change b3_pathIntegral ℂ (b65z_fibre c₀ R.C t) (γ k) B = _ at he
    rw [b66f_gen_b66m_parameterLocalForm_segment_integral R t hU ht θ h K a hφ k] at he
    exact he
  rw [b66f_gen_b66m_retained_coefficient_derivative R t U hU ht θ q hq hc hcp K a hφ h]
  symm
  change b3_pathIntegral ℂ (b65z_fibre c₀ R.C t)
    (fun s => γ ⌊(K.N : ℝ) * s⌋ (Int.fract ((K.N : ℝ) * s))) B = _
  rw [b66f_gen_b66m_real_floorLoop_pathIntegral R t B
    (b66f_gen_b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ)
    (b66f_gen_b66m_correctedParameterForm_real_smul R t hU ht θ q hqf hq h ρ hρ)
    K.N γ (fun k => γ k 0) hg]
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, b66f_gen_b66m_polygon_potential_endpoints R t ρ hρ _
    (b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)) K a hφ ha]
  ring

theorem b66f_gen_b66m_correctedParameterForm_flat_period (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (hU : IsOpen U) (ht : t.val ∈ U)
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    {c : ℝ → R.C} (hc : Continuous c) (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    fderiv ℂ (b63e_periodFunction c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
      R.P θ s (b63e_fibreLoopClass c₀ R.C s hc hcp)) t.val h =
    b3_pathIntegral ℂ (b65z_fibre c₀ R.C t)
      (K.loopF (b6t_polydisc c₀) (Subset.refl _) t (R.hincl t) K.cond_u₀).1
      (b66f_gen_b66m_correctedLocalForm R t ρ (b66f_gen_b66g_contract R q (b66f_cocycle R t h))
        (b66f_gen_b66m_parameterLocalForm R t θ h)) := by
  rw [b66f_gen_b66m_flat_loop_period R s θ hc hcp]
  exact b66f_gen_b66m_correctedParameterForm_polygon_period R t hU ht θ q hqf hq h ρ hρ
    hc hcp K a hφ ha

theorem b66f_gen_b66m_correctedParameterScalarForm_flat_pairing (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (s : b6t_polydisc c₀)
    (L : ℂ →L[ℝ] ℝ) {c : ℝ → R.C} (hc : Continuous c)
    (hcp : Function.Periodic c 1)
    (K : b63e_Cover c₀ R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66f_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (b66f_gen_b66m_correctedParameterScalarForm R t θ q h ρ L)
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (b65z_fibre c₀ R.C t)
          (K.loopF (b6t_polydisc c₀) (Subset.refl _) t (R.hincl t) K.cond_u₀)))) =
      L (fderiv ℂ (b63e_periodFunction c₀ R.C (b6t_polydisc c₀) (Subset.refl _)
        R.P θ s (b63e_fibreLoopClass c₀ R.C s hc hcp)) t.val h) := by
  rw [b66f_gen_b66m_correctedParameterScalarForm_lattice_pairing R t θ q h ρ hU ht hqf hq hρ]
  rw [b66f_gen_b66m_correctedParameterForm_flat_period R s t hU ht θ q hqf hq h ρ hρ hc hcp K a hφ ha]

theorem b66f_gen_b66m_correctedParameterHolPairing_flat (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (s : b6t_polydisc c₀)
    (L : ℂ →L[ℝ] ℝ) (x : b66f_gen_b66g_Homology R s) :
    b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ L
      (b3Rest2_θ (Module.finrank_self ℂ)
        (R.P t (b6m_H1Equiv (b6m_transport c₀ R.C s t) x))) =
      L (fderiv ℂ (b63e_periodFunction c₀ R.C (b6t_polydisc c₀)
        (Subset.refl _) R.P θ s x) t.val h) := by
  obtain ⟨γ, rfl⟩ := b6m_smooth_loopClass_surjective (b65z_fibre c₀ R.C s) x
  let c : ℝ → R.C := fun τ => (γ.val τ).val.2
  have hc : Continuous c :=
    continuous_snd.comp (continuous_subtype_val.comp γ.property.2.continuous)
  have hcp : Function.Periodic c 1 := fun τ => by
    change (γ.val (τ + 1)).val.2 = (γ.val τ).val.2
    rw [γ.property.1 τ]
  obtain ⟨K, a, hφ, ha⟩ := b66f_gen_b66m_retained_cover R t hc hcp
  have he : b6m_loopClass (b65z_fibre c₀ R.C s) γ =
      b63e_fibreLoopClass c₀ R.C s hc hcp :=
    b63e_loopClass_eq_fibreLoopClass_param c₀ R.C (b6t_polydisc c₀)
      (Subset.refl _) s γ
  rw [he, b63e_fibreLoopClass_transport]
  rw [← b66f_gen_b66m_retained_loopClass R t hc hcp K, R.hP]
  exact b66f_gen_b66m_correctedParameterScalarForm_flat_pairing R t θ q h ρ hU ht hqf hq hρ
    s L hc hcp K a hφ ha

theorem b66f_gen_b66m_complexPeriodFunctional_flat (R : b65z_SharedFamily c₀ g₀) (s : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U) (t : b6t_polydisc c₀) (q : b66f_Coeff R) (h : Fin 10 → ℂ) (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ) (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1) (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w) (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source}) (x : ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) :
    b66f_gen_b66m_complexPeriodFunctional R t
      (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM)
      (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM)
      ((b66f_gen_b66m_fullTransport R s t).baseChange ℂ x) =
      fderiv ℂ (b66f_gen_b66m_flatPeriod R s θ x) t.val h := by
  have hd (x : ℂ ⊗[ℤ] b66f_gen_b66g_Homology R s) :
      DifferentiableAt ℂ (b66f_gen_b66m_flatPeriod R s θ x) t.val :=
    (b66f_gen_b66m_flatPeriod_analytic R s θ hU x t.val ⟨t.property, ht⟩).differentiableAt
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, fderiv_add (hd x) (hd y)]
    rfl
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, b66f_gen_b66m_complexPeriodFunctional_tmul,
      b66f_gen_b66m_flatPeriod_tmul]
    change c * ((b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
        (b3Rest2_θ (Module.finrank_self ℂ)
          (R.P t (b6m_H1Equiv (b6m_transport c₀ R.C s t) x))) : ℂ) +
      Complex.I * (b66f_gen_b66m_correctedParameterHolPairing R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
        (b3Rest2_θ (Module.finrank_self ℂ)
          (R.P t (b6m_H1Equiv (b6m_transport c₀ R.C s t) x))) : ℂ)) = _
    rw [b66f_gen_b66m_correctedParameterHolPairing_flat R t θ q h ρ hU ht hqf hq hρ,
      b66f_gen_b66m_correctedParameterHolPairing_flat R t θ q h ρ hU ht hqf hq hρ]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm Complex.I, Complex.re_add_im]
    have hd' : DifferentiableAt ℂ
        (b63e_periodFunction c₀ R.C (b6t_polydisc c₀) (Subset.refl _) R.P θ s x) t.val := by
      simpa only [b66f_gen_b66m_flatPeriod_tmul, one_smul] using hd (1 ⊗ₜ[ℤ] x)
    rw [fderiv_const_smul hd']
    rfl

theorem b66f_gen_b66m_contraction_cech_primitive_functional (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)))
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (h : Fin 10 → ℂ)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66f_forms R t 1)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p w)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (n : ℂ ⊗[ℤ] b60_Lattice) (hn : n ∈ b60_F (b65z_period R s m t.val)) :
    b66f_gen_b66m_cechTrace R t ρ hρ (b66f_gen_b66m_sc_cechProjection R t
      ⟨b66f_gen_b66g_contract R q (b66f_cocycle R t h),
        b66f_gen_b66m_rs_contract_mem R t hqf (b66f_gen_b66k_cocycle_mem R t h)⟩)
      (b66f_gen_b66m_polarizedHarmonicForm R t b (b66f_gen_b66m_primitiveFullVector R s t m n)) =
      fderiv ℂ (b66f_gen_b66m_flatPeriod R s θ (b66f_gen_b66m_primitiveHomology R s m n)) t.val h := by
  rw [b66f_gen_b66m_contraction_cech_functional R t b θ q h ρ hU ht hqf hq hρ _
    (b66f_gen_b66m_primitiveFullVector_mem hg R s t m hJ hpol n hn),
    ← b66f_gen_b66m_primitiveHomology_transport R s t m n]
  exact b66f_gen_b66m_complexPeriodFunctional_flat R s θ t q h ρ hU ht hqf hq hρ _

theorem b66f_gen_b66m_relative_extension_chartForm (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm c₀ R.C (b6t_polydisc c₀) (Subset.refl _) U)
    (q : b66f_Coeff R) (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (hw : w.val = b66f_chartForm R t q)
    (hq : ∀ a (p : b65z_fibre c₀ R.C t), p.val ∈ (R.atlas.A a).source → ∀ v : ℂ,
      θ.val t ⟨p, v⟩ = q a p.val.2 * b66f_gen_b66m_sc_sliceD R t a p v) :
    b63e_relFormAt c₀ R.C (b6t_polydisc c₀) (Subset.refl _) θ t = w := by
  apply Subtype.ext
  rw [hw]
  funext p
  have hp : p.1.val = (t, p.1.val.2) := Prod.ext p.1.property rfl
  have ha : p.1.val ∈ (R.atlas.A (t, p.1.val.2)).source := by
    rw [hp]
    exact (R.atlas.hA _).1
  exact hq (t, p.1.val.2) p.1 ha p.2

theorem b66f_gen_b66m_normalized_contraction_trace (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g₀ i)))  (R : b65z_SharedFamily c₀ g₀)
    (s t : b6t_polydisc c₀)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c₀ R.C R.hC (b6t_polydisc c₀) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (b3_periodLattice ℂ (b65z_fibre c₀ R.C t)))
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
    (q : b66f_primitiveForms R t) (w : b3_HolForm ℂ (b65z_fibre c₀ R.C t))
    (i k : Fin 3) (h : Fin 10 → ℂ)
    (hw : w.val = b66f_chartForm R t q.val)
    (hp : ∀ x : b63l_parameterLattice c₀ R.C R.hC (b6t_polydisc c₀)
      (Subset.refl _) s,
      (b63e_transportMap c₀ R.C R.hC (b6t_polydisc c₀)
        (Subset.refl _) R.P s t x).val w =
        b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period R s m t.val) (0, i))) :
    b66f_gen_b66m_cechTrace R t ρ hρ (b66f_gen_b66m_sc_cechProjection R t
      ⟨b66f_gen_b66g_contract R q.val (b66f_cocycle R t h),
        b66f_gen_b66m_rs_contract_mem R t q.property.1 (b66f_gen_b66k_cocycle_mem R t h)⟩)
      (b66f_gen_b66m_polarizedHarmonicForm R t b (b66f_gen_b66m_primitiveFullVector R s t m
        (b60_frame (b65z_period R s m t.val) (1, k)))) =
      (2 / (Complex.I * (Real.sqrt 3 : ℂ))) *
        (fderiv ℂ (b65z_period R s m) t.val h) (finProdFinEquiv (k, i)) := by
  obtain ⟨U, hU, ht, _, θ, hq⟩ :=
    b66f_coefficient_relative_extension R t ⟨q.val, q.property.1⟩
  rw [b66f_gen_b66m_contraction_cech_primitive_functional hg R s t m hJ hpol b θ q.val h ρ
    hU ht q.property.1 hq hρ _ (Submodule.subset_span ⟨(1, k), rfl⟩)]
  exact b66f_gen_b66m_normalized_graph_derivative hg R s t m hJ hpol θ hU ht w i k h
    (b66f_gen_b66m_relative_extension_chartForm R t θ q.val w hw hq) hp

end HodgeLean.Foundations.Program
