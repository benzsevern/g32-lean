import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


variable {c₀ : Fin 10 → ℂ} {g₀ : Fin 13 → b4b_Group}

theorem b66f_gen_b66g_average_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (P : b66f_Coeff R) :
    b66f_average R t P =
      (Fintype.card b4b_Group : ℂ)⁻¹ • ∑ g : b4b_Group, b66f_pull R t 2 g P := by
  unfold b66f_average
  rw [LinearMap.smul_apply, LinearMap.sum_apply]

theorem b66f_gen_b66g_pull_product (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q r : b66f_Coeff R) (g : b4b_Group) :
    b66f_pull R t 2 g (b66f_product R q r) =
      b66f_product R (b66f_pull R t 1 g q) (b66f_pull R t 1 g r) := by
  funext a x
  simp only [b66f_pull, LinearMap.coe_mk, AddHom.coe_mk, b66f_product]
  split_ifs <;> ring_nf

def b66f_gen_b66k_boundaries (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_Cochain R) :=
  Submodule.span ℂ {c | ∃ v : b66f_Index R → ℂ → ℂ,
    (∀ a, AnalyticOnNhd ℂ (v a) (b66f_domain R t a)) ∧ c = b66f_boundary R t v}
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_Cochain R) ∈ b66f_gen_b66k_boundaries R t := Submodule.zero_mem _

abbrev b66f_gen_b66k_Quotient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :=
  b66f_Cochain R ⧸ b66f_gen_b66k_boundaries R t
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_gen_b66k_Quotient R t) = 0 := rfl

def b66f_gen_b66k_refinementDomain (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) : Set ℂ :=
  {z | (t.val, z) ∈ (R.atlas.A a).target ∧
    (t, g • ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A b).source}
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) :
    b66f_gen_b66k_refinementDomain R t g a b ⊆ b66f_domain R t a := fun _ h => h.1

def b66f_gen_b66k_holomorphicCochains (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_Cochain R) :=
  Submodule.span ℂ {u |
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 a b)) ∧
    ∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0}
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_Cochain R) ∈ b66f_gen_b66k_holomorphicCochains R t := Submodule.zero_mem _

def b66f_gen_b66k_differential (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_Cochain R →ₗ[ℂ]
      (b66f_Index R → b66f_Index R → b66f_Index R → R.C → ℂ) where
  toFun u a b c x :=
    if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩ (R.atlas.A c).source then
      u a c x - u b c x - b66f_vertical R t b c x * u a b x else 0
  map_add' u v := by
    funext a b c x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' k u := by
    funext a b c x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> ring
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66k_differential R t 0 = 0 := map_zero _

def b66f_gen_b66k_cechH1 (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_gen_b66k_Quotient R t) :=
  (b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t)).map
    (b66f_gen_b66k_boundaries R t).mkQ
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_gen_b66k_Quotient R t) ∈ b66f_gen_b66k_cechH1 R t := Submodule.zero_mem _

def b66f_gen_b66g_scalarBoundary (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v : b66f_Index R → ℂ → ℂ) : b66f_Cochain R := fun a b x =>
  if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source then
    v a (R.atlas.A a (t, x)).2 - v b (R.atlas.A b (t, x)).2 else 0
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_gen_b66g_scalarBoundary R t 0 = 0 := by
  funext a b x
  simp [b66f_gen_b66g_scalarBoundary]

def b66f_gen_b66g_scalarBoundaries (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_Cochain R) :=
  Submodule.span ℂ {u | ∃ v : b66f_Index R → ℂ → ℂ,
    (∀ a, AnalyticOnNhd ℂ (v a) (b66f_domain R t a)) ∧
      u = b66f_gen_b66g_scalarBoundary R t v}
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_Cochain R) ∈ b66f_gen_b66g_scalarBoundaries R t := Submodule.zero_mem _

abbrev b66f_gen_b66g_scalarQuotient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :=
  b66f_Cochain R ⧸ b66f_gen_b66g_scalarBoundaries R t
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_gen_b66g_scalarQuotient R t) = 0 := rfl

def b66f_gen_b66g_scalarCycles (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_Cochain R) :=
  Submodule.span ℂ {u |
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66f_gen_b66k_refinementDomain R t 1 a b)) ∧
    (∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0) ∧
    ∀ a b c x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → (t, x) ∈ (R.atlas.A c).source →
      u a c x = u b c x + u a b x}
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_Cochain R) ∈ b66f_gen_b66g_scalarCycles R t := Submodule.zero_mem _

def b66f_gen_b66g_H1O (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    Submodule ℂ (b66f_gen_b66g_scalarQuotient R t) :=
  (b66f_gen_b66g_scalarCycles R t).map (b66f_gen_b66g_scalarBoundaries R t).mkQ
example (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (0 : b66f_gen_b66g_scalarQuotient R t) ∈ b66f_gen_b66g_H1O R t := Submodule.zero_mem _

def b66f_gen_b66g_contract (R : b65z_SharedFamily c₀ g₀) (q : b66f_Coeff R)
    (u : b66f_Cochain R) : b66f_Cochain R := fun a b x => q b x * u a b x
example (R : b65z_SharedFamily c₀ g₀) (q : b66f_Coeff R) : b66f_gen_b66g_contract R q 0 = 0 := by
  funext a b x
  exact mul_zero _

theorem b66f_gen_b66g_forms_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (m : ℕ)
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

theorem b66f_gen_b66g_holomorphic_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
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

theorem b66f_gen_b66k_inverse_parameter (R : b65z_SharedFamily c₀ g₀) (a : b66f_Index R)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (R.atlas.A a).target) :
    ((R.atlas.A a).symm u).1.val = u.1 := by
  rw [← R.atlas.hparam a _ ((R.atlas.A a).map_target hu),
    (R.atlas.A a).right_inv hu]

theorem b66f_gen_b66k_inverse_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (z : ℂ) (hz : (t.val, z) ∈ (R.atlas.A a).target) :
    (t, ((R.atlas.A a).symm (t.val, z)).2) = (R.atlas.A a).symm (t.val, z) := by
  apply Prod.ext
  · exact Subtype.ext (b66f_gen_b66k_inverse_parameter R a _ hz).symm
  · rfl

theorem b66f_gen_b66k_transition_analytic (R : b65z_SharedFamily c₀ g₀) (a b : b66f_Index R)
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    AnalyticAt ℂ (b66f_transition R a b) u := by
  have hc := (contDiffGroupoid ω 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)).compatible
    (R.atlas.hA a).2 (R.atlas.hA b).2
  have hd := (mem_groupoid_of_pregroupoid.mp hc).1
  have hd' : ContDiffOn ℂ ω ((R.atlas.A a).symm.trans (R.atlas.A b))
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using hd
  exact analyticAt_snd.comp (hd'.contDiffAt (((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu)).analyticAt

theorem b66f_gen_b66g_transition_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
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

theorem b66f_gen_b66g_overlap_eventually (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
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

theorem b66f_gen_b66g_chart_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (b : b66f_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) ∧
    ((R.atlas.A b).symm (t.val, (R.atlas.A b (t, x)).2)).2 = x := by
  have h1 : R.atlas.A b (t, x) = (t.val, (R.atlas.A b (t, x)).2) :=
    Prod.ext (R.atlas.hparam b _ hb) rfl
  refine ⟨h1, ?_⟩
  rw [← h1, (R.atlas.A b).left_inv hb]

theorem b66f_gen_b66g_target_coefficient (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (a b : b66f_Index R) (z : ℂ)
    (hz : z ∈ b66f_gen_b66k_refinementDomain R t 1 a b)
    (hq : AnalyticOnNhd ℂ (fun z => q b ((R.atlas.A b).symm (t.val, z)).2)
      (b66f_domain R t b)) :
    AnalyticAt ℂ (fun w => q b ((R.atlas.A a).symm (t.val, w)).2) z := by
  obtain ⟨_, hdom, han, _⟩ := b66f_gen_b66g_transition_mem R t a b z hz
  have h1 : AnalyticAt ℂ (fun w =>
      q b ((R.atlas.A b).symm (t.val, b66f_transition R a b (t.val, w))).2) z :=
    AnalyticAt.comp (f := fun w => b66f_transition R a b (t.val, w)) (hq _ hdom) han
  apply h1.congr
  filter_upwards [b66f_gen_b66g_overlap_eventually R t a b z hz] with w ⟨hmem, _, hb⟩
  rw [← hb, (b66f_gen_b66g_chart_slice R t b _ hmem.2).2]

theorem b66f_gen_b66g_kernel_spec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {u : b66f_Cochain R} (hu : u ∈ LinearMap.ker (b66f_gen_b66k_differential R t))
    (a b c : b66f_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source) (hc : (t, x) ∈ (R.atlas.A c).source) :
    u a c x = u b c x + b66f_vertical R t b c x * u a b x := by
  have h := congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hu) a) b) c) x
  simp only [b66f_gen_b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩
      (R.atlas.A c).source from ⟨⟨ha, hb⟩, hc⟩)] at h
  linear_combination h

theorem b66f_gen_b66g_contract_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) {u : b66f_Cochain R}
    (hu : u ∈ b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t)) :
    b66f_gen_b66g_contract R q u ∈ b66f_gen_b66g_scalarCycles R t := by
  obtain ⟨hqa, hql, _⟩ := b66f_gen_b66g_forms_spec R t 1 hq
  obtain ⟨hua, huz⟩ := b66f_gen_b66g_holomorphic_spec R t hu.1
  apply Submodule.subset_span
  refine ⟨fun a b z hz => ?_, fun a b x hx => ?_, fun a b c x ha hb hc => ?_⟩
  · exact (b66f_gen_b66g_target_coefficient R t q a b z hz (hqa b)).mul (hua a b z hz)
  · simp only [b66f_gen_b66g_contract, huz a b x hx, mul_zero]
  · simp only [b66f_gen_b66g_contract]
    rw [b66f_gen_b66g_kernel_spec R t hu.2 a b c x ha hb hc, hql b c x hb hc, pow_one]
    ring

theorem b66f_gen_b66k_boundary_add (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (v w : b66f_Index R → ℂ → ℂ) :
    b66f_boundary R t (v + w) = b66f_boundary R t v + b66f_boundary R t w := by
  funext a b x
  simp only [b66f_boundary, Pi.add_apply]
  split_ifs <;> ring

theorem b66f_gen_b66k_boundary_smul (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (k : ℂ) (v : b66f_Index R → ℂ → ℂ) :
    b66f_boundary R t (k • v) = k • b66f_boundary R t v := by
  funext a b x
  simp only [b66f_boundary, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem b66f_gen_b66k_boundary_representation (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (c : b66f_Cochain R)
    (hc : c ∈ b66f_gen_b66k_boundaries R t) :
    ∃ v : b66f_Index R → ℂ → ℂ,
      (∀ a, AnalyticOnNhd ℂ (v a) (b66f_domain R t a)) ∧ c = b66f_boundary R t v := by
  induction hc using Submodule.span_induction with
  | mem c hc => exact hc
  | zero =>
    refine ⟨0, fun a z hz => analyticAt_const, ?_⟩
    funext a b x
    simp [b66f_boundary]
  | add c d hc hd hc' hd' =>
    obtain ⟨v, hv, rfl⟩ := hc'
    obtain ⟨w, hw, rfl⟩ := hd'
    exact ⟨v + w, fun a => (hv a).add (hw a), (b66f_gen_b66k_boundary_add R t v w).symm⟩
  | smul k c hc hc' =>
    obtain ⟨v, hv, rfl⟩ := hc'
    refine ⟨k • v, ?_, (b66f_gen_b66k_boundary_smul R t k v).symm⟩
    intro a
    simpa only [Pi.smul_apply] using (hv a).const_smul (c := k)

theorem b66f_gen_b66g_contract_boundary (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) {u : b66f_Cochain R}
    (hu : u ∈ b66f_gen_b66k_boundaries R t) :
    b66f_gen_b66g_contract R q u ∈ b66f_gen_b66g_scalarBoundaries R t := by
  obtain ⟨hqa, hql, _⟩ := b66f_gen_b66g_forms_spec R t 1 hq
  obtain ⟨v, hv, rfl⟩ := b66f_gen_b66k_boundary_representation R t u hu
  apply Submodule.subset_span
  refine ⟨fun a z => q a ((R.atlas.A a).symm (t.val, z)).2 * v a z,
    fun a => (hqa a).mul (hv a), ?_⟩
  funext a b x
  simp only [b66f_gen_b66g_contract, b66f_boundary, b66f_gen_b66g_scalarBoundary]
  split_ifs with hx
  · rw [(b66f_gen_b66g_chart_slice R t a x hx.1).2, (b66f_gen_b66g_chart_slice R t b x hx.2).2,
      hql a b x hx.1 hx.2, pow_one]
    ring
  · exact mul_zero _

theorem b66f_gen_b66g_cup_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    (∃ C : b66f_gen_b66k_cechH1 R t →ₗ[ℂ] (b66f_forms R t 1 →ₗ[ℂ] b66f_gen_b66g_H1O R t),
      ∀ (u : b66f_Cochain R)
      (_hu : u ∈ b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t))
      (c : b66f_gen_b66k_cechH1 R t) (_hc : c.val = (b66f_gen_b66k_boundaries R t).mkQ u)
      (q : b66f_forms R t 1),
      (C c q).val = (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R q.val u)) ∧
    ∀ q r : b66f_forms R t 1, b66f_product R q.val r.val ∈ b66f_forms R t 2 := by
  constructor
  · let Z := b66f_gen_b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66f_gen_b66k_differential R t)
    let Φ : Z →ₗ[ℂ] (b66f_forms R t 1 →ₗ[ℂ] b66f_gen_b66g_H1O R t) :=
      LinearMap.mk₂ ℂ (fun (u : Z) (q : b66f_forms R t 1) =>
        (⟨(b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R q.val u.val),
          Submodule.mem_map_of_mem (b66f_gen_b66g_contract_mem R t q.property u.property)⟩ :
            b66f_gen_b66g_H1O R t))
        (fun u w q => by
          apply Subtype.ext
          change (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R q.val (u.val + w.val)) =
            (b66f_gen_b66g_scalarBoundaries R t).mkQ _ + (b66f_gen_b66g_scalarBoundaries R t).mkQ _
          rw [← map_add]
          congr 1
          funext a b x
          simp only [b66f_gen_b66g_contract, Pi.add_apply]
          ring)
        (fun k u q => by
          apply Subtype.ext
          change (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R q.val (k • u.val)) =
            k • (b66f_gen_b66g_scalarBoundaries R t).mkQ _
          rw [← map_smul]
          congr 1
          funext a b x
          simp only [b66f_gen_b66g_contract, Pi.smul_apply, smul_eq_mul]
          ring)
        (fun u q r => by
          apply Subtype.ext
          change (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R (q.val + r.val) u.val) =
            (b66f_gen_b66g_scalarBoundaries R t).mkQ _ + (b66f_gen_b66g_scalarBoundaries R t).mkQ _
          rw [← map_add]
          congr 1
          funext a b x
          simp only [b66f_gen_b66g_contract, Pi.add_apply]
          ring)
        (fun k u q => by
          apply Subtype.ext
          change (b66f_gen_b66g_scalarBoundaries R t).mkQ (b66f_gen_b66g_contract R (k • q.val) u.val) =
            k • (b66f_gen_b66g_scalarBoundaries R t).mkQ _
          rw [← map_smul]
          congr 1
          funext a b x
          simp only [b66f_gen_b66g_contract, Pi.smul_apply, smul_eq_mul]
          ring)
    let f : Z →ₗ[ℂ] b66f_gen_b66k_Quotient R t := (b66f_gen_b66k_boundaries R t).mkQ ∘ₗ Z.subtype
    have hker : LinearMap.ker f ≤ LinearMap.ker Φ := by
      intro u hu
      have hb : u.val ∈ b66f_gen_b66k_boundaries R t :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hu)
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro q
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero _).mpr (b66f_gen_b66g_contract_boundary R t q.property hb)
    have hrange : LinearMap.range f = b66f_gen_b66k_cechH1 R t := by
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
    obtain ⟨hqa, hql, hqz⟩ := b66f_gen_b66g_forms_spec R t 1 q.property
    obtain ⟨hra, hrl, hrz⟩ := b66f_gen_b66g_forms_spec R t 1 r.property
    apply Submodule.subset_span
    refine ⟨fun a => (hqa a).mul (hra a), fun a b x ha hb => ?_, fun a x hx => ?_⟩
    · simp only [b66f_product]
      rw [hql a b x ha hb, hrl a b x ha hb]
      ring
    · simp only [b66f_product, hqz a x hx, zero_mul]

def b66f_gen_b66g_slice (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (a : b66f_Index R) :
    b65z_fibre c₀ R.C t → ℂ := fun y => (R.atlas.A a y.val).2

def b66f_gen_b66g_sliceD (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (a : b66f_Index R)
    (p : b65z_fibre c₀ R.C t) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t a) p

def b66f_gen_b66g_ofForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ) : b66f_Coeff R := fun a x =>
  if (t, x) ∈ (R.atlas.A a).source then
    θ ⟨(⟨(t, x), rfl⟩ : b65z_fibre c₀ R.C t),
      ((b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹ : ℂ)⟩ else 0

def b66f_gen_b66g_toForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) :
    b66f_Coeff R →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ) where
  toFun q P := q P.proj.val P.proj.val.2 * b66f_gen_b66g_sliceD R t P.proj.val P.proj P.2
  map_add' q r := by
    funext P
    simp only [Pi.add_apply]
    ring
  map_smul' c q := by
    funext P
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem b66f_gen_b66g_slice_value (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    R.atlas.A a y.val = (t.val, (R.atlas.A a y.val).2) := by
  refine Prod.ext ?_ rfl
  rw [R.atlas.hparam a _ hy]
  exact congrArg Subtype.val y.property

def b66f_gen_b66k_totalDeck (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group)
    (q : b6t_polydisc c₀ × R.C) : b6t_polydisc c₀ × R.C :=
  (q.1, g • q.2)

def b66f_gen_b66k_deckTransition (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group)
    (a b : b66f_Index R) (u : (Fin 10 → ℂ) × ℂ) : ℂ :=
  (R.atlas.A b (b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u))).2

theorem b66f_gen_b66k_totalDeck_holomorphic (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (b66f_gen_b66k_totalDeck R g) := by
  apply b6a_lift_contMDiff c₀ R.C R.atlas.f R.atlas.n R.atlas.hn
    R.atlas.A R.atlas.hA R.atlas.hparam
    (fun q hq => (R.atlas.hfree q hq).2) R.atlas.hmark
  · exact continuous_fst.prodMk ((R.hC g).comp continuous_snd)
  · intro q
    rfl
  · intro q
    exact R.atlas.hgal.1 g q.2

theorem b66f_gen_b66k_deckTransition_analytic (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group)
    (a b : b66f_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source) :
    AnalyticAt ℂ (b66f_gen_b66k_deckTransition R g a b) u := by
  have hi : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (R.atlas.A a).symm u :=
    contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (R.atlas.hA a).2) ha
  have hg := (b66f_gen_b66k_totalDeck_holomorphic R g).contMDiffAt.comp u hi
  have hc : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (R.atlas.A b)
      (b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u)) :=
    contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (R.atlas.hA b).2) hb
  exact analyticAt_snd.comp ((hc.comp u hg).contDiffAt.analyticAt)

theorem b66f_gen_b66k_deckCoordinate_analytic (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (g : b4b_Group) (a b : b66f_Index R) :
    AnalyticOnNhd ℂ (b66f_deckCoordinate R t g a b)
      (b66f_gen_b66k_refinementDomain R t g a b) := by
  intro z hz
  have hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66f_gen_b66k_totalDeck
    rw [← b66f_gen_b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd : ContDiffAt ℂ ω (b66f_gen_b66k_deckTransition R g a b) (t.val, z) :=
    (b66f_gen_b66k_deckTransition_analytic R g a b _ hz.1 hb).contDiffAt
  apply ((hd.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt).congr
  have hn := (continuous_const.prodMk continuous_id).continuousAt
    ((R.atlas.A a).open_target.mem_nhds hz.1)
  filter_upwards [hn] with w hw
  change b66f_gen_b66k_deckTransition R g a b (t.val, w) = b66f_deckCoordinate R t g a b w
  unfold b66f_deckCoordinate b66f_gen_b66k_deckTransition b66f_gen_b66k_totalDeck
  rw [← b66f_gen_b66k_inverse_slice R t a w hw]

theorem b66f_gen_b66g_slice_coordinate_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun p : b65z_fibre c₀ R.C t => (R.atlas.A a p.val).2)
      {p | p.val ∈ (R.atlas.A a).source} ∧
    ∀ p : b65z_fibre c₀ R.C t, p.val ∈ (R.atlas.A a).source →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun y : b65z_fibre c₀ R.C t => (R.atlas.A a y.val).2) p ≠ 0 := by
  set F : b65z_fibre c₀ R.C t → ℂ := fun y => (R.atlas.A a y.val).2
  have hchart : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (R.atlas.A a) (R.atlas.A a).source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (R.atlas.hA a).2)
  have hsnd : ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
      (Prod.snd : (Fin 10 → ℂ) × ℂ → ℂ) := contDiff_snd.contMDiff
  have hF : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F {p | p.val ∈ (R.atlas.A a).source} :=
    hsnd.comp_contMDiffOn (hchart.comp (R.hincl t).contMDiffOn (fun p hp => hp))
  refine ⟨hF, fun p hp hzero => ?_⟩
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
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
    have h1 := b66f_gen_b66g_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66f_gen_b66g_slice_value R t a (e.symm w₂) hw₂.2
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

theorem b66f_gen_b66g_slice_contMDiffAt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (y : b65z_fibre c₀ R.C t) (hy : y.val ∈ (R.atlas.A a).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66f_gen_b66g_slice R t a) y :=
  (b66f_gen_b66g_slice_coordinate_aux R t a).1.contMDiffAt
    (((R.atlas.A a).open_source.preimage continuous_subtype_val).mem_nhds hy)

theorem b66f_gen_b66g_fibre_val (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (y : b65z_fibre c₀ R.C t) : y.val = (t, y.val.2) :=
  Prod.ext y.property rfl

theorem b66f_gen_b66g_mem_source (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (p : b65z_fibre c₀ R.C t) :
    p.val ∈ (R.atlas.A a).source ↔ (t, p.val.2) ∈ (R.atlas.A a).source := by
  rw [← b66f_gen_b66g_fibre_val R t p]

theorem b66f_gen_b66g_pullback_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (g : b4b_Group) (a : b66f_Index R)
    (p : b65z_fibre c₀ R.C t) (ha : p.val ∈ (R.atlas.A a).source) (v : ℂ) :
    b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q) ⟨p, v⟩ =
      b66f_pull R t 1 g q a p.val.2 * b66f_gen_b66g_sliceD R t a p v := by
  set c : b66f_Index R := (g • p).val
  set D := b66f_deckCoordinate R t g a c
  have hc : (g • p).val ∈ (R.atlas.A c).source := (R.atlas.hA c).1
  have hpa := b66f_gen_b66g_slice_value R t a p ha
  have hsym : (R.atlas.A a).symm (t.val, b66f_gen_b66g_slice R t a p) = p.val := by
    change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) = p.val
    rw [← hpa, (R.atlas.A a).left_inv ha]
  have hz : b66f_gen_b66g_slice R t a p ∈ b66f_gen_b66k_refinementDomain R t g a c := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · rw [hsym]
      exact hc
  have hD : HasDerivAt D (deriv D (b66f_gen_b66g_slice R t a p)) (b66f_gen_b66g_slice R t a p) :=
    (b66f_gen_b66k_deckCoordinate_analytic R t g a c _ hz).differentiableAt.hasDerivAt
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66f_gen_b66g_slice R t c ∘ (fun x : b65z_fibre c₀ R.C t => g • x) =ᶠ[𝓝 p]
      D ∘ b66f_gen_b66g_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A c (t, g • y.val.2)).2 =
      (R.atlas.A c (t, g • ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2)).2)).2
    rw [← b66f_gen_b66g_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t a) p :=
    (b66f_gen_b66g_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hmc : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t c) (g • p) :=
    (b66f_gen_b66g_slice_contMDiffAt R t c (g • p) hc).mdifferentiableAt (by simp)
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : b65z_fibre c₀ R.C t => g • x) p :=
    ((R.hG t g) p).mdifferentiableAt (by simp)
  have hmD : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) D (b66f_gen_b66g_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hD.differentiableAt
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b66f_gen_b66g_slice R t c ∘ (fun x : b65z_fibre c₀ R.C t => g • x)) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv D (b66f_gen_b66g_slice R t a p))).comp
        (b66f_gen_b66g_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := D) (f := b66f_gen_b66g_slice R t a) p hD.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  have hchain := mfderiv_comp_apply p hmc hmg v
  rw [hH.mfderiv] at hchain
  have hsrc : (t, p.val.2) ∈ (R.atlas.A a).source := (b66f_gen_b66g_mem_source R t a p).mp ha
  have hval : (R.atlas.A a (t, p.val.2)).2 = b66f_gen_b66g_slice R t a p := by
    change _ = (R.atlas.A a p.val).2
    rw [← b66f_gen_b66g_fibre_val R t p]
  change q (g • p).val (g • p).val.2 *
      b66f_gen_b66g_sliceD R t c (g • p) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : b65z_fibre c₀ R.C t => g • x) p v) =
    (if (t, p.val.2) ∈ (R.atlas.A a).source then q (t, g • p.val.2) (g • p.val.2) *
      deriv (b66f_deckCoordinate R t g a (t, g • p.val.2)) (R.atlas.A a (t, p.val.2)).2 ^ 1
      else 0) * b66f_gen_b66g_sliceD R t a p v
  rw [ite_eq_left hsrc, pow_one, hval]
  have k : b66f_gen_b66g_sliceD R t c (g • p)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun x : b65z_fibre c₀ R.C t => g • x) p v) =
      deriv D (b66f_gen_b66g_slice R t a p) * b66f_gen_b66g_sliceD R t a p v :=
    hchain.symm.trans (mul_comm (b66f_gen_b66g_sliceD R t a p v) _)
  refine (congrArg (fun w => q (g • p).val (g • p).val.2 * w) k).trans ?_
  change q c (g • p.val.2) * (deriv D (b66f_gen_b66g_slice R t a p) * b66f_gen_b66g_sliceD R t a p v) =
    q c (g • p.val.2) * deriv D (b66f_gen_b66g_slice R t a p) * b66f_gen_b66g_sliceD R t a p v
  ring

theorem b66f_gen_b66g_slice_ne (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (p : b65z_fibre c₀ R.C t) (ha : p.val ∈ (R.atlas.A a).source) :
    b66f_gen_b66g_sliceD R t a p 1 ≠ 0 := by
  intro h0
  apply (b66f_gen_b66g_slice_coordinate_aux R t a).2 p ha
  apply ContinuousLinearMap.ext
  intro (v : ℂ)
  have hz : b66f_gen_b66g_sliceD R t a p = 0 :=
    ContinuousLinearMap.ext_ring (by rw [h0]; rfl)
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hz

theorem b66f_gen_b66g_clm_apply (L : ℂ →L[ℂ] ℂ) (v : ℂ) : L v = v * L 1 := by
  have : v = v • (1 : ℂ) := by simp
  conv_lhs => rw [this]
  rw [map_smul, smul_eq_mul]

theorem b66f_gen_b66g_pull_one (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (g : b4b_Group) :
    b66f_pull R t 1 g q = b66f_gen_b66g_ofForm R t
      (b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q)) := by
  funext a x
  unfold b66f_gen_b66g_ofForm
  split_ifs with h
  · have hap := b66f_gen_b66g_pullback_apply R t q g a ⟨(t, x), rfl⟩ h
      ((b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    have hne := b66f_gen_b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [hap, b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change _ = b66f_pull R t 1 g q a x * (_ * _)
    field_simp
  · change (if (t, x) ∈ (R.atlas.A a).source then _ else 0) = 0
    rw [ite_eq_right h]

def b66f_gen_b66g_chartD (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (x₀ y : b65z_fibre c₀ R.C t) :
    ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x₀) y

theorem b66f_gen_b66g_slice_chart (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a : b66f_Index R) (x₀ y : b65z_fibre c₀ R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (hya : y.val ∈ (R.atlas.A a).source) :
    AnalyticAt ℂ (b66f_gen_b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ∧
    deriv (b66f_gen_b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
      (extChartAt 𝓘(ℂ, ℂ) x₀ y) ≠ 0 ∧
    ∀ v : ℂ, b66f_gen_b66g_sliceD R t a y v =
      deriv (b66f_gen_b66g_slice R t a ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
        (extChartAt 𝓘(ℂ, ℂ) x₀ y) * b66f_gen_b66g_chartD R t x₀ y v := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set h := b66f_gen_b66g_slice R t a ∘ e.symm
  have hyt : e y ∈ e.target := e.map_source hy
  have hinv : e.symm (e y) = y := e.left_inv hy
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have hsym : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e y) :=
    (contMDiffOn_extChartAt_symm x₀ (e y) hyt).contMDiffAt
      (extChartAt_target_mem_nhds' hyt)
  have hsl : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b66f_gen_b66g_slice R t a) (e.symm (e y)) := by
    rw [hinv]
    exact b66f_gen_b66g_slice_contMDiffAt R t a y hya
  have hh : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω h (e y) := hsl.comp (e y) hsym
  have han : AnalyticAt ℂ h (e y) := (contMDiffAt_iff_contDiffAt.mp hh).analyticAt
  have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e y) := by
    refine inter_mem (extChartAt_target_mem_nhds' hyt) ?_
    apply (continuousAt_extChartAt_symm'' hyt).preimage_mem_nhds
    rw [hinv]
    exact hopen.mem_nhds hya
  have hinj : InjOn h (e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source}) := by
    intro w₁ hw₁ w₂ hw₂ hw
    have h1 := b66f_gen_b66g_slice_value R t a (e.symm w₁) hw₁.2
    have h2 := b66f_gen_b66g_slice_value R t a (e.symm w₂) hw₂.2
    have hv : (e.symm w₁).val = (e.symm w₂).val := by
      apply (R.atlas.A a).injOn hw₁.2 hw₂.2
      rw [h1, h2]
      exact congrArg (fun z => (t.val, z)) hw
    have hy' : e.symm w₁ = e.symm w₂ := Subtype.ext hv
    rw [← e.right_inv hw₁.1, ← e.right_inv hw₂.1, hy']
  refine ⟨han, rf8_deriv_ne_zero_of_injOn hU han hinj, fun v => ?_⟩
  have heq : b66f_gen_b66g_slice R t a =ᶠ[𝓝 y] h ∘ e := by
    filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy'
    simp only [h, Function.comp_apply, e.left_inv hy']
  have hmd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) h (e y) :=
    mdifferentiableAt_iff_differentiableAt.mpr han.differentiableAt
  have hme : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e y :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℂ, ℂ)])
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t a) y
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv h (e y))).comp
        (b66f_gen_b66g_chartD R t x₀ y)) :=
    (HasMFDerivAt.comp (g := h) (f := e) y
      han.differentiableAt.hasDerivAt.hasFDerivAt.hasMFDerivAt
      hme.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66f_gen_b66g_sliceD
  rw [hH.mfderiv]
  exact mul_comm (b66f_gen_b66g_chartD R t x₀ y v) _

theorem b66f_gen_b66g_fibre_mk (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (p : b65z_fibre c₀ R.C t) : (⟨(t, p.val.2), rfl⟩ : b65z_fibre c₀ R.C t) = p :=
  Subtype.ext (b66f_gen_b66g_fibre_val R t p).symm

theorem b66f_gen_b66g_lin_smul' {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
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

theorem b66f_gen_b66g_lin_smul {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ}
    (hlin : ∀ (x : X) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x : X) (c w : ℂ) :
    θ ⟨x, c * w⟩ = c * θ ⟨x, w⟩ :=
  b66f_gen_b66g_lin_smul' hlin x c w

theorem b66f_gen_b66g_form_chart (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ}
    (hlin : ∀ (x : b65z_fibre c₀ R.C t) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x₀ y : b65z_fibre c₀ R.C t)
    (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (v : ℂ) :
    θ ⟨y, v⟩ = b66f_gen_b66g_chartD R t x₀ y v * b4cov_coef θ x₀ 1 (extChartAt 𝓘(ℂ, ℂ) x₀ y) := by
  have h1 : b4cov_vec x₀ y (b66f_gen_b66g_chartD R t x₀ y v) = v :=
    (congrArg (b4cov_vec x₀ y) (b4cov_triv_eq_mfderiv x₀ y hy v).symm).trans
      (b4cov_vec_triv x₀ y hy v)
  have h2 : b4cov_vec x₀ y (b66f_gen_b66g_chartD R t x₀ y v) =
      b66f_gen_b66g_chartD R t x₀ y v • b4cov_vec x₀ y (1 : ℂ) := by
    rw [← b4cov_vec_smul x₀ y hy, smul_eq_mul, mul_one]
  have h3 : b4cov_coef θ x₀ 1 (extChartAt 𝓘(ℂ, ℂ) x₀ y) = θ ⟨y, b4cov_vec x₀ y (1 : ℂ)⟩ := by
    rw [b4cov_coef, (extChartAt 𝓘(ℂ, ℂ) x₀).left_inv hy]
  rw [h3]
  refine Eq.trans ?_ (b66f_gen_b66g_lin_smul' hlin y _ _)
  rw [← h2, h1]

theorem b66f_gen_b66g_transition_hasDerivAt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (z : ℂ)
    (hz : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    HasDerivAt (fun w => b66f_transition R a b (t.val, w))
      (fderiv ℂ (b66f_transition R a b) (t.val, z) (0, 1)) z := by
  have hd := (b66f_gen_b66k_transition_analytic R a b _ hz).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (0, 1) z :=
    (hasDerivAt_const z t.val).prodMk (hasDerivAt_id z)
  exact hd.comp_hasDerivAt z hi

theorem b66f_gen_b66g_slice_change (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (a b : b66f_Index R) (p : b65z_fibre c₀ R.C t)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : p.val ∈ (R.atlas.A b).source) (v : ℂ) :
    b66f_gen_b66g_sliceD R t b p v = b66f_vertical R t a b p.val.2 * b66f_gen_b66g_sliceD R t a p v := by
  set g : ℂ → ℂ := fun w => b66f_transition R a b (t.val, w)
  have hpa := b66f_gen_b66g_slice_value R t a p ha
  have hz : (t.val, b66f_gen_b66g_slice R t a p) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨?_, ?_⟩
    · change (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A a).target
      rw [← hpa]
      exact (R.atlas.A a).map_source ha
    · change (R.atlas.A a).symm (t.val, (R.atlas.A a p.val).2) ∈ (R.atlas.A b).source
      rw [← hpa, (R.atlas.A a).left_inv ha]
      exact hb
  have hg := b66f_gen_b66g_transition_hasDerivAt R t a b _ hz
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
    (R.atlas.A a).open_source.preimage continuous_subtype_val
  have heq : b66f_gen_b66g_slice R t b =ᶠ[𝓝 p] g ∘ b66f_gen_b66g_slice R t a := by
    filter_upwards [hopen.mem_nhds ha] with y hy
    change (R.atlas.A b y.val).2 =
      (R.atlas.A b ((R.atlas.A a).symm (t.val, (R.atlas.A a y.val).2))).2
    rw [← b66f_gen_b66g_slice_value R t a y hy, (R.atlas.A a).left_inv hy]
  have hmg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (b66f_gen_b66g_slice R t a p) :=
    mdifferentiableAt_iff_differentiableAt.mpr hg.differentiableAt
  have hma : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t a) p :=
    (b66f_gen_b66g_slice_contMDiffAt R t a p ha).mdifferentiableAt (by simp)
  have hH : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b66f_gen_b66g_slice R t b) p
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (fderiv ℂ (b66f_transition R a b) (t.val, b66f_gen_b66g_slice R t a p) (0, 1))).comp
        (b66f_gen_b66g_sliceD R t a p)) :=
    (HasMFDerivAt.comp (g := g) (f := b66f_gen_b66g_slice R t a) p hg.hasFDerivAt.hasMFDerivAt
      hma.hasMFDerivAt).congr_of_eventuallyEq_abuse heq
  unfold b66f_gen_b66g_sliceD at hH ⊢
  rw [hH.mfderiv]
  have hv : fderiv ℂ (b66f_transition R a b) (t.val, b66f_gen_b66g_slice R t a p) (0, 1) =
      b66f_vertical R t a b p.val.2 := by
    change _ = fderiv ℂ (b66f_transition R a b) (R.atlas.A a (t, p.val.2)) (0, 1)
    rw [← b66f_gen_b66g_fibre_val R t p]
    exact congrArg (fun u => fderiv ℂ (b66f_transition R a b) u (0, 1)) hpa.symm
  rw [← hv]
  exact mul_comm (b66f_gen_b66g_sliceD R t a p v) _

theorem b66f_gen_b66g_ofForm_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ}
    (hθ : θ ∈ b3_HolForm ℂ (b65z_fibre c₀ R.C t)) :
    b66f_gen_b66g_ofForm R t θ ∈ b66f_forms R t 1 := by
  have hlin := hθ.2
  apply Submodule.subset_span
  refine ⟨fun a z₀ hz₀ => ?_, fun a b x ha hb => ?_, fun a x hx => ?_⟩
  · let y₀ : b65z_fibre c₀ R.C t :=
      ⟨(R.atlas.A a).symm (t.val, z₀), Subtype.ext (b66f_gen_b66k_inverse_parameter R a _ hz₀)⟩
    have hy₀a : y₀.val ∈ (R.atlas.A a).source := (R.atlas.A a).map_target hz₀
    set e := extChartAt 𝓘(ℂ, ℂ) y₀
    set h := b66f_gen_b66g_slice R t a ∘ e.symm
    obtain ⟨han, hder, _⟩ :=
      b66f_gen_b66g_slice_chart R t a y₀ y₀ (mem_extChartAt_source y₀) hy₀a
    have hz : h (e y₀) = z₀ := by
      change (R.atlas.A a (e.symm (e y₀)).val).2 = z₀
      rw [e.left_inv (mem_extChartAt_source y₀)]
      change (R.atlas.A a ((R.atlas.A a).symm (t.val, z₀))).2 = z₀
      rw [(R.atlas.A a).right_inv hz₀]
    rw [← hz]
    refine (analyticAt_comp_iff_of_deriv_ne_zero han hder).mp ?_
    have hex : e y₀ ∈ e.target := e.map_source (mem_extChartAt_source y₀)
    have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
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
    obtain ⟨_, _, hD⟩ := b66f_gen_b66g_slice_chart R t a y₀ (e.symm s) hy hs.2
    have hpt : ((R.atlas.A a).symm (t.val, h s)).2 = (e.symm s).val.2 := by
      change ((R.atlas.A a).symm (t.val, (R.atlas.A a (e.symm s).val).2)).2 = _
      rw [← b66f_gen_b66g_slice_value R t a _ hs.2, (R.atlas.A a).left_inv hs.2]
    change _ = b66f_gen_b66g_ofForm R t θ a ((R.atlas.A a).symm (t.val, h s)).2
    rw [hpt]
    unfold b66f_gen_b66g_ofForm
    rw [ite_eq_left ((b66f_gen_b66g_mem_source R t a _).mp hs.2), b66f_gen_b66g_fibre_mk R t (e.symm s)]
    have hne := b66f_gen_b66g_slice_ne R t a (e.symm s) hs.2
    have h1 := hD 1
    rw [e.right_inv hs.1] at h1
    rw [b66f_gen_b66g_form_chart R t hlin y₀ (e.symm s) hy, e.right_inv hs.1,
      b66f_gen_b66g_clm_apply (b66f_gen_b66g_chartD R t y₀ (e.symm s)), h1]
    rw [h1] at hne
    have hc : b66f_gen_b66g_chartD R t y₀ (e.symm s) 1 ≠ 0 := right_ne_zero_of_mul hne
    field_simp
    rfl
  · unfold b66f_gen_b66g_ofForm
    rw [ite_eq_left ha, ite_eq_left hb, pow_one]
    have hch := b66f_gen_b66g_slice_change R t a b ⟨(t, x), rfl⟩ ha hb 1
    have hna := b66f_gen_b66g_slice_ne R t a ⟨(t, x), rfl⟩ ha
    have hnb := b66f_gen_b66g_slice_ne R t b ⟨(t, x), rfl⟩ hb
    have e1 : (b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹ =
        b66f_vertical R t a b x * (b66f_gen_b66g_sliceD R t b ⟨(t, x), rfl⟩ 1)⁻¹ := by
      rw [hch] at hnb ⊢
      have hv : b66f_vertical R t a b x ≠ 0 := left_ne_zero_of_mul hnb
      field_simp
    rw [e1]
    exact b66f_gen_b66g_lin_smul hlin _ _ _
  · unfold b66f_gen_b66g_ofForm
    rw [ite_eq_right hx]

theorem b66f_gen_b66g_toForm_lin (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (q : b66f_Coeff R) (x : b65z_fibre c₀ R.C t) (c v w : ℂ) :
    b66f_gen_b66g_toForm R t q ⟨x, c * v + w⟩ =
      c * b66f_gen_b66g_toForm R t q ⟨x, v⟩ + b66f_gen_b66g_toForm R t q ⟨x, w⟩ := by
  change q x.val x.val.2 * b66f_gen_b66g_sliceD R t x.val x (c * v + w) =
    c * (q x.val x.val.2 * b66f_gen_b66g_sliceD R t x.val x v) +
      q x.val x.val.2 * b66f_gen_b66g_sliceD R t x.val x w
  rw [b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) (c * v + w),
    b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) v, b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) w]
  ring

theorem b66f_gen_b66g_chartD_vec (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (x₀ y : b65z_fibre c₀ R.C t) (hy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).source) (u : ℂ) :
    b66f_gen_b66g_chartD R t x₀ y (b4cov_vec x₀ y u) = u :=
  (b4cov_triv_eq_mfderiv x₀ y hy (b4cov_vec x₀ y u)).symm.trans (b4cov_triv_vec x₀ y hy u)

theorem b66f_gen_b66g_toForm_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) (a : b66f_Index R)
    (p : b65z_fibre c₀ R.C t) (ha : p.val ∈ (R.atlas.A a).source) (v : ℂ) :
    b66f_gen_b66g_toForm R t q ⟨p, v⟩ = q a p.val.2 * b66f_gen_b66g_sliceD R t a p v := by
  obtain ⟨_, hql, _⟩ := b66f_gen_b66g_forms_spec R t 1 hq
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hlaw := hql a p.val p.val.2 ((b66f_gen_b66g_mem_source R t a p).mp ha)
    ((b66f_gen_b66g_mem_source R t p.val p).mp hb)
  change q p.val p.val.2 * b66f_gen_b66g_sliceD R t p.val p v = _
  rw [b66f_gen_b66g_slice_change R t a p.val p ha hb v, hlaw, pow_one]
  ring

theorem b66f_gen_b66g_toForm_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) :
    b66f_gen_b66g_toForm R t q ∈ b3_HolForm ℂ (b65z_fibre c₀ R.C t) := by
  obtain ⟨hqa, _, _⟩ := b66f_gen_b66g_forms_spec R t 1 hq
  have hF : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  apply b4cov_mem_holForm_of_coef hF
  · intro x c v w
    exact b66f_gen_b66g_toForm_lin R t q x c v w
  · intro x₀
    set e := extChartAt 𝓘(ℂ, ℂ) x₀
    set a := x₀.val
    set u : ℂ := b4cov_lineEquiv hF 1
    set h := b66f_gen_b66g_slice R t a ∘ e.symm
    have hx₀ : x₀.val ∈ (R.atlas.A a).source := (R.atlas.hA a).1
    obtain ⟨han, _, _⟩ := b66f_gen_b66g_slice_chart R t a x₀ x₀ (mem_extChartAt_source x₀) hx₀
    have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a).source} :=
      (R.atlas.A a).open_source.preimage continuous_subtype_val
    have hex : e x₀ ∈ e.target := e.map_source (mem_extChartAt_source x₀)
    have hU : e.target ∩ e.symm ⁻¹' {y | y.val ∈ (R.atlas.A a).source} ∈ 𝓝 (e x₀) := by
      refine inter_mem (extChartAt_target_mem_nhds' hex) ?_
      apply (continuousAt_extChartAt_symm'' hex).preimage_mem_nhds
      rw [e.left_inv (mem_extChartAt_source x₀)]
      exact hopen.mem_nhds hx₀
    have hval : h (e x₀) = b66f_gen_b66g_slice R t a x₀ := by
      simp only [h, Function.comp_apply, e.left_inv (mem_extChartAt_source x₀)]
    have hdom : h (e x₀) ∈ b66f_domain R t a := by
      rw [hval]
      change (t.val, (R.atlas.A a x₀.val).2) ∈ (R.atlas.A a).target
      rw [← b66f_gen_b66g_slice_value R t a x₀ hx₀]
      exact (R.atlas.A a).map_source hx₀
    have hQ : AnalyticAt ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2) (h (e x₀)) :=
      hqa a _ hdom
    have hR : AnalyticAt ℂ (fun s => q a ((R.atlas.A a).symm (t.val, h s)).2 *
        (deriv h s * u)) (e x₀) :=
      (AnalyticAt.comp (f := h) hQ han).mul (han.deriv.mul analyticAt_const)
    apply hR.congr
    filter_upwards [hU] with s hs
    have hy : e.symm s ∈ e.source := e.map_target hs.1
    obtain ⟨_, _, hD⟩ := b66f_gen_b66g_slice_chart R t a x₀ (e.symm s) hy hs.2
    change q a ((R.atlas.A a).symm (t.val, h s)).2 * (deriv h s * u) =
      q (e.symm s).val (e.symm s).val.2 *
        b66f_gen_b66g_sliceD R t (e.symm s).val (e.symm s) (b4cov_vec x₀ (e.symm s) u)
    have hpt : ((R.atlas.A a).symm (t.val, h s)).2 = (e.symm s).val.2 := by
      change ((R.atlas.A a).symm (t.val, (R.atlas.A a (e.symm s).val).2)).2 = _
      rw [← b66f_gen_b66g_slice_value R t a _ hs.2, (R.atlas.A a).left_inv hs.2]
    have k1 : b66f_gen_b66g_sliceD R t a (e.symm s) (b4cov_vec x₀ (e.symm s) u) = deriv h s * u := by
      refine (hD _).trans ?_
      rw [b66f_gen_b66g_chartD_vec R t x₀ _ hy, e.right_inv hs.1]
    have hap := b66f_gen_b66g_toForm_apply R t hq a (e.symm s) hs.2 (b4cov_vec x₀ (e.symm s) u)
    refine Eq.trans ?_ hap.symm
    rw [k1, hpt]

theorem b66f_gen_b66g_pull_one_mem (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) (g : b4b_Group) :
    b66f_pull R t 1 g q ∈ b66f_forms R t 1 := by
  rw [b66f_gen_b66g_pull_one]
  exact b66f_gen_b66g_ofForm_mem R t (b3_pullback_mem_holForm _ (R.hG t g) _ (b66f_gen_b66g_toForm_mem R t hq))

theorem b66f_gen_b66g_form_one {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {θ : TangentBundle 𝓘(ℂ, ℂ) X → ℂ}
    (hlin : ∀ (x : X) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) (x : X) (w : ℂ) :
    θ ⟨x, w⟩ = w * θ ⟨x, (1 : ℂ)⟩ := by
  have h := b66f_gen_b66g_lin_smul hlin x w 1
  rw [mul_one] at h
  exact h

theorem b66f_gen_b66g_toForm_ofForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {θ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ}
    (hlin : ∀ (x : b65z_fibre c₀ R.C t) (a : ℂ) (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      θ ⟨x, a • v + w⟩ = a * θ ⟨x, v⟩ + θ ⟨x, w⟩) :
    b66f_gen_b66g_toForm R t (b66f_gen_b66g_ofForm R t θ) = θ := by
  funext P
  obtain ⟨p, v⟩ := P
  have hb : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hsrc := (b66f_gen_b66g_mem_source R t p.val p).mp hb
  change b66f_gen_b66g_ofForm R t θ p.val p.val.2 * b66f_gen_b66g_sliceD R t p.val p v = θ ⟨p, v⟩
  suffices hw : ∀ w : ℂ, b66f_gen_b66g_ofForm R t θ p.val p.val.2 * b66f_gen_b66g_sliceD R t p.val p w =
      θ ⟨p, w⟩ from hw v
  intro v
  unfold b66f_gen_b66g_ofForm
  rw [ite_eq_left hsrc, b66f_gen_b66g_fibre_mk R t p]
  have hne := b66f_gen_b66g_slice_ne R t p.val p hb
  rw [b66f_gen_b66g_form_one hlin p, b66f_gen_b66g_form_one hlin p v, b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t p.val p) v]
  field_simp

theorem b66f_gen_b66g_toForm_pull (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) (g : b4b_Group) :
    b66f_gen_b66g_toForm R t (b66f_pull R t 1 g q) =
      b3_pullback ℂ ℂ (fun x : b65z_fibre c₀ R.C t => g • x) (b66f_gen_b66g_toForm R t q) := by
  rw [b66f_gen_b66g_pull_one]
  exact b66f_gen_b66g_toForm_ofForm R t
    (b3_pullback_mem_holForm _ (R.hG t g) _ (b66f_gen_b66g_toForm_mem R t hq)).2

theorem b66f_gen_b66g_pull_pull (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) (g h : b4b_Group) :
    b66f_pull R t 1 g (b66f_pull R t 1 h q) = b66f_pull R t 1 (h * g) q := by
  rw [b66f_gen_b66g_pull_one R t (b66f_pull R t 1 h q), b66f_gen_b66g_toForm_pull R t hq,
    b4cov_pullback_comp _ _ (R.hG t g) (R.hG t h), b66f_gen_b66g_pull_one]
  have hc : ((fun x : b65z_fibre c₀ R.C t => h • x) ∘ fun x => g • x) = fun x => (h * g) • x :=
    funext fun x => (mul_smul h g x).symm
  rw [hc]

theorem b66f_gen_b66g_average_product (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q r : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) (hr : r ∈ b66f_forms R t 1) :
    b66f_average R t (b66f_product R q r) ∈ b66f_forms R t 2 ∧
    ∀ g : b4b_Group, b66f_pull R t 2 g (b66f_average R t (b66f_product R q r)) =
      b66f_average R t (b66f_product R q r) := by
  constructor
  · rw [b66f_gen_b66g_average_apply]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => ?_)
    rw [b66f_gen_b66g_pull_product]
    exact (b66f_gen_b66g_cup_aux R t).2 ⟨_, b66f_gen_b66g_pull_one_mem R t hq g⟩ ⟨_, b66f_gen_b66g_pull_one_mem R t hr g⟩
  · intro g
    rw [b66f_gen_b66g_average_apply, map_smul, map_sum]
    congr 1
    have hre := Equiv.sum_comp (Equiv.mulRight g)
      (fun h => b66f_pull R t 2 h (b66f_product R q r))
    refine Eq.trans ?_ hre
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [b66f_gen_b66g_pull_product, b66f_gen_b66g_pull_product, b66f_gen_b66g_pull_product, b66f_gen_b66g_pull_pull R t hq,
      b66f_gen_b66g_pull_pull R t hr]
    rfl

theorem b66f_gen_b66e_forms_analytic (D : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (m : ℕ)
    (Q : b66f_Coeff D) (hQ : Q ∈ b66f_forms D t m) (a : b66f_Index D) :
    AnalyticOnNhd ℂ (fun z => Q a ((D.atlas.A a).symm (t.val, z)).2)
      (b66f_domain D t a) := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ => exact hQ.1 a
  | zero => exact analyticOnNhd_const
  | add Q Q' _ _ h h' => exact h.add h'
  | smul c Q _ h => exact fun z hz => analyticAt_const.mul (h z hz)

theorem b66f_gen_b66e_centre_mem (D : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (x : D.C) :
    (D.atlas.A (t, x) (t, x)).2 ∈ b66f_domain D t (t, x) := by
  have hs := (D.atlas.hA (t, x)).1
  have hp := D.atlas.hparam (t, x) (t, x) hs
  have hm := (D.atlas.A (t, x)).map_source hs
  change (t.val, (D.atlas.A (t, x) (t, x)).2) ∈ (D.atlas.A (t, x)).target
  rw [← hp]
  exact hm

theorem b66f_gen_b66e_residueSum_sum (D : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset D.C) (v : b66f_Index D → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain D t a → MeromorphicAt (v a) z)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → b66f_Coeff D)
    (hQ : ∀ k, Q k ∈ b66f_forms D t 2) :
    b66f_residueSum D t S v (∑ k ∈ s, c k • Q k) =
      ∑ k ∈ s, c k * b66f_residueSum D t S v (Q k) := by
  unfold b66f_residueSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hz := b66f_gen_b66e_centre_mem D t x
  have hfun : (fun z => v (t, x) z *
      (∑ k ∈ s, c k • Q k) (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2) =
      ∑ k ∈ s, fun z => c k * (v (t, x) z *
        Q k (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, TauCeti.Contour.residue_sum]
  · simp only [TauCeti.Contour.residue_const_mul]
  · intro k _
    exact analyticAt_const.meromorphicAt.mul
      ((hmero _ _ hz).mul (b66f_gen_b66e_forms_analytic D t 2 (Q k) (hQ k) _ _ hz).meromorphicAt)

theorem b66f_gen_b66g_ofForm_toForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t 1) :
    b66f_gen_b66g_ofForm R t (b66f_gen_b66g_toForm R t q) = q := by
  obtain ⟨_, _, hqz⟩ := b66f_gen_b66g_forms_spec R t 1 hq
  funext a x
  unfold b66f_gen_b66g_ofForm
  split_ifs with h
  · have hap := b66f_gen_b66g_toForm_apply R t hq a ⟨(t, x), rfl⟩ h
      ((b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩ 1)⁻¹)
    refine hap.trans ?_
    have hne := b66f_gen_b66g_slice_ne R t a ⟨(t, x), rfl⟩ h
    rw [b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t a ⟨(t, x), rfl⟩)]
    change q a x * (_ * _) = q a x
    field_simp
  · exact (hqz a x h).symm


end HodgeLean.Foundations.Program
