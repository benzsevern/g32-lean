import HodgeLean.Foundations.Program.CodifferentialComparisonScalarProofs
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

def b66f_gen_b66m_cechTrace (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (ρ : SmoothPartitionOfUnity (b66f_Index R) 𝓘(ℝ, ℂ) (b65z_fibre c₀ R.C t) univ)
    (hρ : ρ.IsSubordinate fun c => {y | y.val ∈ (R.atlas.A c).source})
    (c : b66f_gen_b66g_H1O R t) (θ : b3_HolForm ℂ (b65z_fibre c₀ R.C t)) : ℂ :=
  b66f_gen_b66m_dolbeaultTrace R t (Classical.choose (b66f_gen_b66m_sc_comparison R t ρ hρ) c) θ

theorem b66f_gen_b66k_deck_parameter_holomorphic (R : b65z_SharedFamily c₀ g₀)
    (t : b6t_polydisc c₀) (h : Fin 10 → ℂ) (g : b4b_Group)
    (a b : b66f_Index R) :
    AnalyticOnNhd ℂ
      (fun z => -fderiv ℂ (b66f_gen_b66k_deckTransition R g a b) (t.val, z) (h, 0))
      (b66f_gen_b66k_refinementDomain R t g a b) := by
  intro z hz
  have hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66f_gen_b66k_totalDeck
    rw [← b66f_gen_b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd : ContDiffAt ℂ ω (b66f_gen_b66k_deckTransition R g a b) (t.val, z) :=
    (b66f_gen_b66k_deckTransition_analytic R g a b _ hz.1 hb).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => -fderiv ℂ (b66f_gen_b66k_deckTransition R g a b) u (h, 0)) (t.val, z) :=
    ((hd.fderiv_right (by simp)).clm_apply contDiffAt_const).neg
  exact (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt

theorem b66f_gen_b66k_deck_overlap_nhds (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group)
    (a b : b66f_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source) :
    ∀ᶠ v in 𝓝 u, v ∈ (R.atlas.A a).target ∧
      b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm v) ∈ (R.atlas.A b).source := by
  have hcont := (b66f_gen_b66k_totalDeck_holomorphic R g).continuous.continuousAt.comp
    ((R.atlas.A a).continuousAt_symm ha)
  filter_upwards [(R.atlas.A a).open_target.mem_nhds ha,
    hcont ((R.atlas.A b).open_source.mem_nhds hb)] with v hv hv'
  exact ⟨hv, hv'⟩

theorem b66f_gen_b66k_deck_square (R : b65z_SharedFamily c₀ g₀) (g : b4b_Group)
    (a b c d : b66f_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source)
    (hc : (R.atlas.A a).symm u ∈ (R.atlas.A c).source) :
    (fun v => b66f_transition R b d (v.1, b66f_gen_b66k_deckTransition R g a b v)) =ᶠ[𝓝 u]
      (fun v => b66f_gen_b66k_deckTransition R g c d (v.1, b66f_transition R a c v)) := by
  have hn : ∀ᶠ v in 𝓝 u, (R.atlas.A a).symm v ∈ (R.atlas.A c).source :=
    ((R.atlas.A a).continuousAt_symm ha) ((R.atlas.A c).open_source.mem_nhds hc)
  filter_upwards [b66f_gen_b66k_deck_overlap_nhds R g a b u ha hb, hn] with v hv hv'
  have hp := b66f_gen_b66k_inverse_parameter R a v hv.1
  have ht : (v.1, b66f_transition R a c v) =
      R.atlas.A c ((R.atlas.A a).symm v) := by
    apply Prod.ext
    · exact hp.symm.trans (R.atlas.hparam c _ hv').symm
    · rfl
  have hg : (v.1, b66f_gen_b66k_deckTransition R g a b v) =
      R.atlas.A b (b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm v)) := by
    apply Prod.ext
    · exact hp.symm.trans (R.atlas.hparam b _ hv.2).symm
    · rfl
  change (R.atlas.A d ((R.atlas.A b).symm
    (v.1, b66f_gen_b66k_deckTransition R g a b v))).2 =
    (R.atlas.A d (b66f_gen_b66k_totalDeck R g ((R.atlas.A c).symm
      (v.1, b66f_transition R a c v)))).2
  rw [hg, ht, (R.atlas.A b).left_inv hv.2, (R.atlas.A c).left_inv hv']

theorem b66f_gen_b66k_deck_vertical (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (z : ℂ)
    (hz : z ∈ b66f_gen_b66k_refinementDomain R t g a b) :
    deriv (b66f_deckCoordinate R t g a b) z =
      fderiv ℂ (b66f_gen_b66k_deckTransition R g a b) (t.val, z) (0, 1) := by
  have hb : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66f_gen_b66k_totalDeck
    rw [← b66f_gen_b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd := (b66f_gen_b66k_deckTransition_analytic R g a b _ hz.1 hb).differentiableAt
  have he : b66f_deckCoordinate R t g a b =ᶠ[𝓝 z]
      (fun w => b66f_gen_b66k_deckTransition R g a b (t.val, w)) := by
    have hn := (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_target.mem_nhds hz.1)
    filter_upwards [hn] with w hw
    unfold b66f_deckCoordinate b66f_gen_b66k_deckTransition b66f_gen_b66k_totalDeck
    rw [← b66f_gen_b66k_inverse_slice R t a w hw]
  have hd' := hd.hasFDerivAt.comp z
    (hasFDerivAt_const (c := t.val) z |>.prodMk (hasFDerivAt_id z))
  rw [he.deriv_eq]
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hd'.fderiv

theorem b66f_gen_b66k_deck_invariant_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) :
    ∃ v : b66f_Index R → b66f_Index R → ℂ → ℂ,
      (∀ a b, AnalyticOnNhd ℂ (v a b) (b66f_gen_b66k_refinementDomain R t g a b)) ∧
      ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * v a b (R.atlas.A a (t, x)).2 -
            v c d (R.atlas.A c (t, x)).2 := by
  refine ⟨fun a b z => -fderiv ℂ (b66f_gen_b66k_deckTransition R g a b) (t.val, z) (h, 0),
    b66f_gen_b66k_deck_parameter_holomorphic R t h g, ?_⟩
  intro a b c d x ha hc hb hd
  let u := R.atlas.A a (t, x)
  let w := R.atlas.A b (t, g • x)
  let q := R.atlas.A c (t, x)
  have hau : u ∈ (R.atlas.A a).target := (R.atlas.A a).map_source ha
  have hbu : b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm u) ∈
      (R.atlas.A b).source := by
    simpa only [u, (R.atlas.A a).left_inv ha, b66f_gen_b66k_totalDeck] using hb
  have hcu : (R.atlas.A a).symm u ∈ (R.atlas.A c).source := by
    simpa only [u, (R.atlas.A a).left_inv ha] using hc
  have hac : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A c)).source := ⟨hau, hcu⟩
  have hbd : w ∈ ((R.atlas.A b).symm.trans (R.atlas.A d)).source := by
    refine ⟨(R.atlas.A b).map_source hb, ?_⟩
    change (R.atlas.A b).symm w ∈ (R.atlas.A d).source
    simpa only [w, (R.atlas.A b).left_inv hb] using hd
  have hcq : q ∈ (R.atlas.A c).target := (R.atlas.A c).map_source hc
  have hdq : b66f_gen_b66k_totalDeck R g ((R.atlas.A c).symm q) ∈
      (R.atlas.A d).source := by
    simpa only [q, (R.atlas.A c).left_inv hc, b66f_gen_b66k_totalDeck] using hd
  have hw : (u.1, b66f_gen_b66k_deckTransition R g a b u) = w := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam b _ hb).symm
    · exact congrArg (fun y => (R.atlas.A b (b66f_gen_b66k_totalDeck R g y)).2)
        ((R.atlas.A a).left_inv ha)
  have hq : (u.1, b66f_transition R a c u) = q := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam c _ hc).symm
    · exact congrArg (fun y => (R.atlas.A c y).2) ((R.atlas.A a).left_inv ha)
  have h1 := b66k_chain_parameter (b66f_gen_b66k_deckTransition R g a b)
    (b66f_transition R b d) u h
    (b66f_gen_b66k_deckTransition_analytic R g a b u hau hbu).differentiableAt
    (by rw [hw]; exact (b66f_gen_b66k_transition_analytic R b d w hbd).differentiableAt)
  have h2 := b66k_chain_parameter (b66f_transition R a c)
    (b66f_gen_b66k_deckTransition R g c d) u h
    (b66f_gen_b66k_transition_analytic R a c u hac).differentiableAt
    (by rw [hq]; exact (b66f_gen_b66k_deckTransition_analytic R g c d q hcq hdq).differentiableAt)
  rw [hw] at h1
  rw [hq] at h2
  have he := congrArg (fun L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ => L (h, 0))
    (b66f_gen_b66k_deck_square R g a b c d u hau hbu hcu).fderiv_eq
  rw [h1, h2] at he
  have hz : (R.atlas.A c (t, x)).2 ∈ b66f_gen_b66k_refinementDomain R t g c d := by
    constructor
    · rw [← R.atlas.hparam c _ hc]
      exact hcq
    · have hpair : (t.val, (R.atlas.A c (t, x)).2) = q := by
        exact Prod.ext (R.atlas.hparam c _ hc).symm rfl
      rw [hpair, show q = R.atlas.A c (t, x) from rfl, (R.atlas.A c).left_inv hc]
      exact hd
  rw [b66f_gen_b66k_deck_vertical R t g c d _ hz]
  simp only [b66f_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, g • x) ∈ (R.atlas.A b).source ∩ (R.atlas.A d).source from ⟨hb, hd⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A c).source from ⟨ha, hc⟩),
    b66f_vertical]
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = u :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  have hpc : (t.val, (R.atlas.A c (t, x)).2) = q :=
    Prod.ext (R.atlas.hparam c _ hc).symm rfl
  rw [hpa, hpc]
  change fderiv ℂ (b66f_transition R b d) w (h, 0) -
    fderiv ℂ (b66f_gen_b66k_deckTransition R g c d) q (0, 1) *
      fderiv ℂ (b66f_transition R a c) u (h, 0) = _
  linear_combination he

theorem b66f_gen_b66k_deck_invariant (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) :
    ∃ v : b66f_Index R → b66f_Index R → ℂ → ℂ,
      (∀ a b, AnalyticOnNhd ℂ (v a b) (b66f_gen_b66k_refinementDomain R t g a b)) ∧
      ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * v a b (R.atlas.A a (t, x)).2 -
            v c d (R.atlas.A c (t, x)).2 :=
  b66f_gen_b66k_deck_invariant_aux R t h g

example := @b66f_gen_b66k_deck_invariant

def b66f_gen_b66g_pulled (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (g : b4b_Group)
    (v : b66f_Index R → ℂ → ℂ) (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (a b : b66f_Index R) (z : ℂ) : ℂ :=
  v b (b66f_deckCoordinate R t g a b z) / deriv (b66f_deckCoordinate R t g a b) z -
    v a z - V a b z / deriv (b66f_deckCoordinate R t g a b) z

def b66f_gen_b66g_omega (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (g : b4b_Group)
    (v : b66f_Index R → ℂ → ℂ) (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (P : b66f_Coeff R) (a b : b66f_Index R) (z : ℂ) : ℂ :=
  b66f_gen_b66g_pulled R t g v V a b z * P a ((R.atlas.A a).symm (t.val, z)).2

def b66f_gen_b66g_omegaForm (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (g : b4b_Group)
    (v : b66f_Index R → ℂ → ℂ) (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (P : b66f_Coeff R) : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ := fun q =>
  b66f_gen_b66g_omega R t g v V P q.proj.val (g • q.proj).val (R.atlas.A q.proj.val q.proj.val).2 *
    b66f_gen_b66g_sliceD R t q.proj.val q.proj q.2

theorem b66f_gen_b66g_refinement_point (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) :
    (R.atlas.A a (t, x)).2 ∈ b66f_gen_b66k_refinementDomain R t g a b := by
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  refine ⟨?_, ?_⟩
  · rw [hpa]
    exact (R.atlas.A a).map_source ha
  · rw [hpa, (R.atlas.A a).left_inv ha]
    exact hb

theorem b66f_gen_b66g_deck_value (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (x : R.C) (ha : (t, x) ∈ (R.atlas.A a).source) :
    b66f_deckCoordinate R t g a b (R.atlas.A a (t, x)).2 = (R.atlas.A b (t, g • x)).2 := by
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  unfold b66f_deckCoordinate
  rw [hpa, (R.atlas.A a).left_inv ha]

theorem b66f_gen_b66g_refinement_iff (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (z : ℂ) (hz : (t.val, z) ∈ (R.atlas.A a).target) :
    b66f_gen_b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈ (R.atlas.A b).source ↔
      z ∈ b66f_gen_b66k_refinementDomain R t g a b := by
  constructor
  · intro h
    refine ⟨hz, ?_⟩
    unfold b66f_gen_b66k_totalDeck at h
    rwa [← b66f_gen_b66k_inverse_slice R t a z hz] at h
  · intro h
    unfold b66f_gen_b66k_totalDeck
    rw [← b66f_gen_b66k_inverse_slice R t a z hz]
    exact h.2

theorem b66f_gen_b66g_refinement_eventually (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_gen_b66k_refinementDomain R t g a b) :
    ∀ᶠ w in 𝓝 z, w ∈ b66f_gen_b66k_refinementDomain R t g a b := by
  have h := b66f_gen_b66k_deck_overlap_nhds R g a b (t.val, z) hz.1
    ((b66f_gen_b66g_refinement_iff R t g a b z hz.1).mpr hz)
  have hc : Tendsto (fun w : ℂ => ((t.val, w) : (Fin 10 → ℂ) × ℂ)) (𝓝 z) (𝓝 (t.val, z)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [hc.eventually h] with w hw
  exact (b66f_gen_b66g_refinement_iff R t g a b w hw.1).mp hw.2

theorem b66f_gen_b66g_deck_chain (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b c d : b66f_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 * b66f_vertical R t a c x =
      b66f_vertical R t b d (g • x) *
        deriv (b66f_deckCoordinate R t g a b) (R.atlas.A a (t, x)).2 := by
  set z := (R.atlas.A a (t, x)).2
  have hzab := b66f_gen_b66g_refinement_point R t g a b x ha hb
  have hzcd := b66f_gen_b66g_refinement_point R t g c d x hc hd
  have hzac : z ∈ b66f_gen_b66k_refinementDomain R t 1 a c :=
    b66f_gen_b66g_refinement_point R t 1 a c x ha (by rwa [one_smul])
  have hgx : (R.atlas.A b (t, g • x)).2 ∈ b66f_gen_b66k_refinementDomain R t 1 b d :=
    b66f_gen_b66g_refinement_point R t 1 b d (g • x) hb (by rwa [one_smul])
  obtain ⟨hmac, _, _, _⟩ := b66f_gen_b66g_transition_mem R t a c z hzac
  obtain ⟨hmbd, _, _, _⟩ := b66f_gen_b66g_transition_mem R t b d _ hgx
  have hTac := b66f_gen_b66g_transition_hasDerivAt R t a c z hmac
  have hTbd := b66f_gen_b66g_transition_hasDerivAt R t b d _ hmbd
  have hpc : b66f_transition R a c (t.val, z) = (R.atlas.A c (t, x)).2 := by
    change (R.atlas.A c ((R.atlas.A a).symm (t.val, (R.atlas.A a (t, x)).2))).2 = _
    rw [show (t.val, (R.atlas.A a (t, x)).2) = R.atlas.A a (t, x) from
      Prod.ext (R.atlas.hparam a _ ha).symm rfl, (R.atlas.A a).left_inv ha]
  have hDab := (b66f_gen_b66k_deckCoordinate_analytic R t g a b z hzab).differentiableAt.hasDerivAt
  have hDcd := (b66f_gen_b66k_deckCoordinate_analytic R t g c d _ hzcd).differentiableAt.hasDerivAt
  rw [← hpc] at hDcd
  have hL := hDcd.comp z hTac
  have hDv : b66f_deckCoordinate R t g a b z = (R.atlas.A b (t, g • x)).2 :=
    b66f_gen_b66g_deck_value R t g a b x ha
  rw [← hDv] at hTbd
  have hR := hTbd.comp z hDab
  have heq : (b66f_deckCoordinate R t g c d ∘ fun w => b66f_transition R a c (t.val, w)) =ᶠ[𝓝 z]
      ((fun w => b66f_transition R b d (t.val, w)) ∘ b66f_deckCoordinate R t g a b) := by
    have hev1 := b66f_gen_b66g_refinement_eventually R t g a b z hzab
    have hev2 := b66f_gen_b66g_overlap_eventually R t a c z hzac
    filter_upwards [hev1, hev2] with w hw1 hw2
    obtain ⟨hmem, haw, hcw⟩ := hw2
    set y := ((R.atlas.A a).symm (t.val, w)).2
    have hyw : (R.atlas.A a (t, y)).2 = w := by rw [haw]
    simp only [Function.comp_apply]
    rw [← hcw, b66f_gen_b66g_deck_value R t g c d y hmem.2]
    have h1 := b66f_gen_b66g_deck_value R t g a b y hmem.1
    rw [hyw] at h1
    rw [h1]
    change _ = (R.atlas.A d ((R.atlas.A b).symm
      (t.val, (R.atlas.A b (t, g • y)).2))).2
    rw [show (t.val, (R.atlas.A b (t, g • y)).2) = R.atlas.A b (t, g • y) from
      Prod.ext (R.atlas.hparam b _ hw1.2).symm rfl, (R.atlas.A b).left_inv hw1.2]
  have hfin := hL.unique (hR.congr_of_eventuallyEq heq)
  have hva : fderiv ℂ (b66f_transition R a c) (t.val, z) (0, 1) = b66f_vertical R t a c x := by
    change _ = fderiv ℂ (b66f_transition R a c) (R.atlas.A a (t, x)) (0, 1)
    rw [show (t.val, z) = R.atlas.A a (t, x) from Prod.ext (R.atlas.hparam a _ ha).symm rfl]
  have hvb : fderiv ℂ (b66f_transition R b d) (t.val, b66f_deckCoordinate R t g a b z) (0, 1) =
      b66f_vertical R t b d (g • x) := by
    change _ = fderiv ℂ (b66f_transition R b d) (R.atlas.A b (t, g • x)) (0, 1)
    rw [hDv, show (t.val, (R.atlas.A b (t, g • x)).2) = R.atlas.A b (t, g • x) from
      Prod.ext (R.atlas.hparam b _ hb).symm rfl]
  rw [hva, hvb, hpc] at hfin
  exact hfin

theorem b66f_gen_b66g_deck_inverse (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_gen_b66k_refinementDomain R t g a b) :
    b66f_deckCoordinate R t g a b z ∈ b66f_gen_b66k_refinementDomain R t g⁻¹ b a ∧
    (fun w => b66f_deckCoordinate R t g⁻¹ b a (b66f_deckCoordinate R t g a b w)) =ᶠ[𝓝 z]
      id ∧
    deriv (b66f_deckCoordinate R t g⁻¹ b a) (b66f_deckCoordinate R t g a b z) *
      deriv (b66f_deckCoordinate R t g a b) z = 1 := by
  have hx := b66f_gen_b66k_inverse_slice R t a z hz.1
  set x := ((R.atlas.A a).symm (t.val, z)).2
  have hxa : (t, x) ∈ (R.atlas.A a).source := by
    rw [hx]
    exact (R.atlas.A a).map_target hz.1
  have hza : (R.atlas.A a (t, x)).2 = z := by
    rw [hx, (R.atlas.A a).right_inv hz.1]
  have hgx : (t, g • x) ∈ (R.atlas.A b).source := hz.2
  have hmem : b66f_deckCoordinate R t g a b z ∈ b66f_gen_b66k_refinementDomain R t g⁻¹ b a := by
    have h1 := b66f_gen_b66g_deck_value R t g a b x hxa
    rw [hza] at h1
    rw [h1]
    have h2 := b66f_gen_b66g_refinement_point R t g⁻¹ b a (g • x) hgx (by rwa [inv_smul_smul])
    exact h2
  have hid : (fun w => b66f_deckCoordinate R t g⁻¹ b a (b66f_deckCoordinate R t g a b w)) =ᶠ[𝓝 z]
      id := by
    filter_upwards [b66f_gen_b66g_refinement_eventually R t g a b z hz] with w hw
    have hxw := b66f_gen_b66k_inverse_slice R t a w hw.1
    set y := ((R.atlas.A a).symm (t.val, w)).2
    have hya : (t, y) ∈ (R.atlas.A a).source := by
      rw [hxw]
      exact (R.atlas.A a).map_target hw.1
    have hyw : (R.atlas.A a (t, y)).2 = w := by
      rw [hxw, (R.atlas.A a).right_inv hw.1]
    have h1 := b66f_gen_b66g_deck_value R t g a b y hya
    rw [hyw] at h1
    rw [h1, b66f_gen_b66g_deck_value R t g⁻¹ b a (g • y) hw.2, inv_smul_smul, hyw]
    rfl
  refine ⟨hmem, hid, ?_⟩
  have hD := (b66f_gen_b66k_deckCoordinate_analytic R t g a b z hz).differentiableAt.hasDerivAt
  have hE := (b66f_gen_b66k_deckCoordinate_analytic R t g⁻¹ b a _ hmem).differentiableAt.hasDerivAt
  have hc := hE.comp z hD
  have hc' := hc.congr_of_eventuallyEq hid.symm
  have := hc'.unique (hasDerivAt_id z)
  rw [← this]

theorem b66f_gen_b66g_deck_ne (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (a b : b66f_Index R) (z : ℂ) (hz : z ∈ b66f_gen_b66k_refinementDomain R t g a b) :
    deriv (b66f_deckCoordinate R t g a b) z ≠ 0 := by
  intro h0
  have h := (b66f_gen_b66g_deck_inverse R t g a b z hz).2.2
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem b66f_gen_b66g_pulled_law (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    (a b c d : b66f_Index R) (x : R.C) (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    b66f_gen_b66g_pulled R t g v V c d (R.atlas.A c (t, x)).2 =
      b66f_vertical R t a c x * b66f_gen_b66g_pulled R t g v V a b (R.atlas.A a (t, x)).2 := by
  have hch := b66f_gen_b66g_deck_chain R t g a b c d x ha hc hb hd
  have hne1 := b66f_gen_b66g_deck_ne R t g a b _ (b66f_gen_b66g_refinement_point R t g a b x ha hb)
  have hne2 := b66f_gen_b66g_deck_ne R t g c d _ (b66f_gen_b66g_refinement_point R t g c d x hc hd)
  have hac := hv a c x hx ha hc
  have hbd := hv b d (g • x) hgx hb hd
  have hdi := hV a b c d x ha hc hb hd
  simp only [b66f_boundary, ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩
      (R.atlas.A c).source from ⟨ha, hc⟩),
    ite_eq_left (show (t, g • x) ∈ (R.atlas.A b).source ∩
      (R.atlas.A d).source from ⟨hb, hd⟩)] at hac hbd
  unfold b66f_gen_b66g_pulled
  rw [b66f_gen_b66g_deck_value R t g a b x ha, b66f_gen_b66g_deck_value R t g c d x hc]
  rw [hac, hbd] at hdi
  set A' := deriv (b66f_deckCoordinate R t g a b) (R.atlas.A a (t, x)).2
  set C' := deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2
  set vb := v b (R.atlas.A b (t, g • x)).2
  set Vab := V a b (R.atlas.A a (t, x)).2
  rw [← sub_eq_zero]
  have hE : A' * v d (R.atlas.A d (t, g • x)).2 - A' * C' * v c (R.atlas.A c (t, x)).2 -
      A' * V c d (R.atlas.A c (t, x)).2 - b66f_vertical R t a c x * C' * vb +
      b66f_vertical R t a c x * A' * C' * v a (R.atlas.A a (t, x)).2 +
      b66f_vertical R t a c x * C' * Vab = 0 := by
    linear_combination (-A') * hdi - (vb - Vab) * hch
  have hq : v d (R.atlas.A d (t, g • x)).2 / C' - v c (R.atlas.A c (t, x)).2 -
      V c d (R.atlas.A c (t, x)).2 / C' -
      b66f_vertical R t a c x * (vb / A' - v a (R.atlas.A a (t, x)).2 - Vab / A') =
      (A' * v d (R.atlas.A d (t, g • x)).2 - A' * C' * v c (R.atlas.A c (t, x)).2 -
      A' * V c d (R.atlas.A c (t, x)).2 - b66f_vertical R t a c x * C' * vb +
      b66f_vertical R t a c x * A' * C' * v a (R.atlas.A a (t, x)).2 +
      b66f_vertical R t a c x * C' * Vab) / (A' * C') := by
    field_simp
    ring
  rw [hq, hE, zero_div]

theorem b66f_gen_b66g_omega_law (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2)
    (a b c d : b66f_Index R) (x : R.C) (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hc : (t, x) ∈ (R.atlas.A c).source)
    (hb : (t, g • x) ∈ (R.atlas.A b).source) (hd : (t, g • x) ∈ (R.atlas.A d).source) :
    b66f_gen_b66g_omega R t g v V P a b (R.atlas.A a (t, x)).2 =
      b66f_vertical R t a c x * b66f_gen_b66g_omega R t g v V P c d (R.atlas.A c (t, x)).2 := by
  have hlaw := b66f_gen_b66g_pulled_law R t h g S v hv V hV a b c d x hx hgx ha hc hb hd
  obtain ⟨_, hPl, _⟩ := b66f_gen_b66g_forms_spec R t 2 hP
  unfold b66f_gen_b66g_omega
  rw [(b66f_gen_b66g_chart_slice R t a x ha).2, (b66f_gen_b66g_chart_slice R t c x hc).2, hlaw,
    hPl a c x ha hc]
  ring

theorem b66f_gen_b66g_omegaForm_apply (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2)
    (p : b65z_fibre c₀ R.C t) (hp1 : p.val.2 ∉ S) (hp2 : g • p.val.2 ∉ S) (a b : b66f_Index R)
    (ha : p.val ∈ (R.atlas.A a).source) (hb : (g • p).val ∈ (R.atlas.A b).source) (w : ℂ) :
    b66f_gen_b66g_omegaForm R t g v V P ⟨p, w⟩ =
      b66f_gen_b66g_omega R t g v V P a b (R.atlas.A a p.val).2 * b66f_gen_b66g_sliceD R t a p w := by
  have hc : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
  have hd : (g • p).val ∈ (R.atlas.A (g • p).val).source := (R.atlas.hA (g • p).val).1
  have ha' := (b66f_gen_b66g_mem_source R t a p).mp ha
  have hc' := (b66f_gen_b66g_mem_source R t p.val p).mp hc
  have hlaw := b66f_gen_b66g_omega_law R t h g S v hv V hV hP a b p.val (g • p).val p.val.2 hp1 hp2
    ha' hc' hb hd
  rw [← b66f_gen_b66g_fibre_val R t p] at hlaw
  change b66f_gen_b66g_omega R t g v V P p.val (g • p).val (R.atlas.A p.val p.val).2 *
    b66f_gen_b66g_sliceD R t p.val p w = _
  rw [b66f_gen_b66g_slice_change R t a p.val p ha hc w, hlaw]
  ring

theorem b66f_gen_b66g_omegaForm_loc (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2)
    (x₀ : b65z_fibre c₀ R.C t) :
    HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66f_gen_b66g_omegaForm R t g v V P) x₀ =ᶠ[𝓝[≠] 0]
      fun τ => b66f_gen_b66g_omega R t g v V P x₀.val (g • x₀).val
        ((b66f_gen_b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + τ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) *
        deriv (fun σ => (b66f_gen_b66g_slice R t x₀.val ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm)
          (extChartAt 𝓘(ℂ, ℂ) x₀ x₀ + σ * b4cov_lineEquiv (Module.finrank_self ℂ) 1)) τ := by
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set a₀ := x₀.val
  set b₀ := (g • x₀).val
  set chartDirection₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66f_gen_b66g_slice R t a₀ ∘ e.symm
  have hc₀ : chartDirection₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have hx₀e : x₀ ∈ e.source := mem_extChartAt_source x₀
  have hex : e x₀ ∈ e.target := e.map_source hx₀e
  have ha₀ : x₀.val ∈ (R.atlas.A a₀).source := (R.atlas.hA a₀).1
  have hb₀ : (g • x₀).val ∈ (R.atlas.A b₀).source := (R.atlas.hA b₀).1
  have hopen : IsOpen {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a₀).source ∧
      (g • y).val ∈ (R.atlas.A b₀).source} := by
    refine ((R.atlas.A a₀).open_source.preimage continuous_subtype_val).inter ?_
    exact (R.atlas.A b₀).open_source.preimage
      (continuous_subtype_val.comp (R.hG t g).continuous)
  set B : Set (b65z_fibre c₀ R.C t) :=
    (fun x : R.C => (⟨(t, x), rfl⟩ : b65z_fibre c₀ R.C t)) ''
      ((↑S : Set R.C) ∪ (fun x => g⁻¹ • x) '' (↑S : Set R.C)) \ {x₀}
  have hBf : B.Finite :=
    ((S.finite_toSet.union (S.finite_toSet.image _)).image _).sdiff
  have hBc : Bᶜ ∈ 𝓝 x₀ := by
    refine (hBf.isClosed.isOpen_compl).mem_nhds ?_
    intro hx
    exact hx.2 rfl
  have hsc : Tendsto (fun τ : ℂ => e x₀ + τ * chartDirection₀) (𝓝 0) (𝓝 (e x₀)) := by
    have : Continuous (fun τ : ℂ => e x₀ + τ * chartDirection₀) := by fun_prop
    simpa using this.tendsto 0
  have hsymc : Tendsto (fun τ : ℂ => e.symm (e x₀ + τ * chartDirection₀)) (𝓝 0) (𝓝 x₀) := by
    have := (continuousAt_extChartAt_symm'' hex).tendsto.comp hsc
    rwa [e.left_inv hx₀e] at this
  have hev1 : ∀ᶠ τ in 𝓝 (0 : ℂ), e x₀ + τ * chartDirection₀ ∈ e.target :=
    hsc.eventually (extChartAt_target_mem_nhds' hex)
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * chartDirection₀) ∈
      {y : b65z_fibre c₀ R.C t | y.val ∈ (R.atlas.A a₀).source ∧
        (g • y).val ∈ (R.atlas.A b₀).source} :=
    hsymc.eventually (hopen.mem_nhds ⟨ha₀, hb₀⟩)
  have hev3 : ∀ᶠ τ in 𝓝 (0 : ℂ), e.symm (e x₀ + τ * chartDirection₀) ∈ Bᶜ :=
    hsymc.eventually hBc
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with τ h1 h2 h3 h4
  set y := e.symm (e x₀ + τ * chartDirection₀)
  have hy : y ∈ e.source := e.map_target h1
  have hyx : y ≠ x₀ := by
    intro hyx
    have := e.right_inv h1
    rw [show e.symm (e x₀ + τ * chartDirection₀) = y from rfl, hyx] at this
    have h5 : τ * chartDirection₀ = 0 := by linear_combination -this
    exact h4 (mul_eq_zero.mp h5 |>.resolve_right hc₀)
  have hyS : y.val.2 ∉ S ∧ g • y.val.2 ∉ S := by
    constructor
    · intro hS
      exact h3 ⟨⟨y.val.2, Or.inl hS, b66f_gen_b66g_fibre_mk R t y⟩, hyx⟩
    · intro hS
      exact h3 ⟨⟨y.val.2, Or.inr ⟨g • y.val.2, hS, inv_smul_smul g _⟩,
        b66f_gen_b66g_fibre_mk R t y⟩, hyx⟩
  obtain ⟨hyan, _, hD⟩ := b66f_gen_b66g_slice_chart R t a₀ x₀ y hy h2.1
  have hey : e y = e x₀ + τ * chartDirection₀ := e.right_inv h1
  have hdΦ : deriv (fun σ => hh (e x₀ + σ * chartDirection₀)) τ = deriv hh (e x₀ + τ * chartDirection₀) * chartDirection₀ := by
    rw [hey] at hyan
    have hs : HasDerivAt (fun σ : ℂ => e x₀ + σ * chartDirection₀) chartDirection₀ τ := by
      simpa using ((hasDerivAt_id τ).mul_const chartDirection₀).const_add (e x₀)
    exact (hyan.differentiableAt.hasDerivAt.comp τ hs).deriv
  change b4cov_coef (b66f_gen_b66g_omegaForm R t g v V P) x₀ chartDirection₀
    (e x₀ + b4cov_lineEquiv (Module.finrank_self ℂ) τ) = _
  rw [b66g_lineEquiv_apply τ]
  unfold b4cov_coef
  change b66f_gen_b66g_omegaForm R t g v V P ⟨y, b4cov_vec x₀ y chartDirection₀⟩ = _
  refine (b66f_gen_b66g_omegaForm_apply R t h g S v hv V hV hP y hyS.1 hyS.2 a₀ b₀ h2.1 h2.2
    (b4cov_vec x₀ y chartDirection₀)).trans ?_
  have hk : b66f_gen_b66g_sliceD R t a₀ y (b4cov_vec x₀ y chartDirection₀) = deriv hh (e x₀ + τ * chartDirection₀) * chartDirection₀ := by
    refine (hD _).trans ?_
    rw [b66f_gen_b66g_chartD_vec R t x₀ y hy, hey]
  rw [hk, hdΦ]
  rfl

theorem b66f_gen_b66g_omega_mero (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66f_gen_b66k_refinementDomain R t g a b))
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2) (a b : b66f_Index R) (z : ℂ)
    (hz : z ∈ b66f_gen_b66k_refinementDomain R t g a b) :
    MeromorphicAt (b66f_gen_b66g_omega R t g v V P a b) z := by
  obtain ⟨hPa, _, _⟩ := b66f_gen_b66g_forms_spec R t 2 hP
  have hD := b66f_gen_b66k_deckCoordinate_analytic R t g a b z hz
  have hDz : b66f_deckCoordinate R t g a b z ∈ b66f_domain R t b := by
    have := (b66f_gen_b66g_deck_inverse R t g a b z hz).1
    exact this.1
  have h1 : MeromorphicAt (fun w => v b (b66f_deckCoordinate R t g a b w)) z :=
    (hmero b _ hDz).comp_analyticAt hD
  have hd : MeromorphicAt (deriv (b66f_deckCoordinate R t g a b)) z := hD.deriv.meromorphicAt
  unfold b66f_gen_b66g_omega b66f_gen_b66g_pulled
  exact (((h1.div hd).sub (hmero a z hz.1)).sub ((hVa a b z hz).meromorphicAt.div hd)).mul
    (hPa a z hz.1).meromorphicAt

theorem b66f_gen_b66g_omegaForm_res (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66f_gen_b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2)
    (x₀ : b65z_fibre c₀ R.C t) :
    MeromorphicAt (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66f_gen_b66g_omegaForm R t g v V P) x₀) 0 ∧
    TauCeti.Contour.residue
      (HurwitzPrymRR_loc (Module.finrank_self ℂ) (b66f_gen_b66g_omegaForm R t g v V P) x₀) 0 =
      TauCeti.Contour.residue (b66f_gen_b66g_omega R t g v V P x₀.val (g • x₀).val)
        (R.atlas.A x₀.val x₀.val).2 := by
  have hloc := b66f_gen_b66g_omegaForm_loc R t h g S v hv V hV hP x₀
  set e := extChartAt 𝓘(ℂ, ℂ) x₀
  set c₀ := b4cov_lineEquiv (Module.finrank_self ℂ) 1
  set hh := b66f_gen_b66g_slice R t x₀.val ∘ e.symm
  set Φ : ℂ → ℂ := fun σ => hh (e x₀ + σ * c₀)
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have := (b4cov_lineEquiv (Module.finrank_self ℂ)).injective (h0.trans (map_zero _).symm)
    exact one_ne_zero this
  have ha₀ : x₀.val ∈ (R.atlas.A x₀.val).source := (R.atlas.hA x₀.val).1
  obtain ⟨hhan, hhd, _⟩ := b66f_gen_b66g_slice_chart R t x₀.val x₀ x₀ (mem_extChartAt_source x₀) ha₀
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
  have hz : (R.atlas.A x₀.val x₀.val).2 ∈ b66f_gen_b66k_refinementDomain R t g x₀.val (g • x₀).val := by
    have := b66f_gen_b66g_refinement_point R t g x₀.val (g • x₀).val x₀.val.2
      ((b66f_gen_b66g_mem_source R t _ x₀).mp ha₀) hgx
    rwa [← b66f_gen_b66g_fibre_val R t x₀] at this
  have hm := b66f_gen_b66g_omega_mero R t g v hmero V hVa hP x₀.val (g • x₀).val _ hz
  rw [← hΦ0] at hm
  have hcm : MeromorphicAt (fun τ => b66f_gen_b66g_omega R t g v V P x₀.val (g • x₀).val (Φ τ) *
      deriv Φ τ) 0 :=
    (hm.comp_analyticAt hΦ).mul hΦ.deriv.meromorphicAt
  refine ⟨hcm.congr hloc.symm, ?_⟩
  rw [TauCeti.Contour.residue_congr_nhdsNE hloc, ← hΦ0]
  exact b66g_residue_comp hΦ hΦd hm

theorem b66f_gen_b66g_omegaForm_lin (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) (g : b4b_Group)
    (v : b66f_Index R → ℂ → ℂ) (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (P : b66f_Coeff R) (x : b65z_fibre c₀ R.C t) (c u w : ℂ) :
    b66f_gen_b66g_omegaForm R t g v V P ⟨x, c * u + w⟩ =
      c * b66f_gen_b66g_omegaForm R t g v V P ⟨x, u⟩ + b66f_gen_b66g_omegaForm R t g v V P ⟨x, w⟩ := by
  unfold b66f_gen_b66g_omegaForm
  simp only
  rw [b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) (c * u + w),
    b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) u, b66f_gen_b66g_clm_apply (b66f_gen_b66g_sliceD R t x.val x) w]
  ring

def b66f_gen_b66g_pt (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀) : R.C ↪ b65z_fibre c₀ R.C t where
  toFun x := ⟨(t, x), rfl⟩
  inj' _ _ hxy := congrArg (fun p : b65z_fibre c₀ R.C t => p.val.2) hxy

theorem b66f_gen_b66g_omega_analytic (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hreg : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66f_gen_b66k_refinementDomain R t g a b))
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2) (a b : b66f_Index R) (x : R.C)
    (hx : x ∉ S) (hgx : g • x ∉ S)
    (ha : (t, x) ∈ (R.atlas.A a).source) (hb : (t, g • x) ∈ (R.atlas.A b).source) :
    AnalyticAt ℂ (b66f_gen_b66g_omega R t g v V P a b) (R.atlas.A a (t, x)).2 := by
  obtain ⟨hPa, _, _⟩ := b66f_gen_b66g_forms_spec R t 2 hP
  have hz := b66f_gen_b66g_refinement_point R t g a b x ha hb
  have hD := b66f_gen_b66k_deckCoordinate_analytic R t g a b _ hz
  have hDz : b66f_deckCoordinate R t g a b (R.atlas.A a (t, x)).2 ∈ b66f_domain R t b :=
    (b66f_gen_b66g_deck_inverse R t g a b _ hz).1.1
  have hvb : AnalyticAt ℂ (v b) (b66f_deckCoordinate R t g a b (R.atlas.A a (t, x)).2) := by
    apply hreg b _ hDz
    rw [b66f_gen_b66g_deck_value R t g a b x ha, (b66f_gen_b66g_chart_slice R t b _ hb).2]
    exact hgx
  have hva : AnalyticAt ℂ (v a) (R.atlas.A a (t, x)).2 := by
    apply hreg a _ hz.1
    rw [(b66f_gen_b66g_chart_slice R t a x ha).2]
    exact hx
  have hne := b66f_gen_b66g_deck_ne R t g a b _ hz
  unfold b66f_gen_b66g_omega b66f_gen_b66g_pulled
  exact ((((AnalyticAt.comp (f := b66f_deckCoordinate R t g a b) hvb hD).div hD.deriv hne).sub
    hva).sub ((hVa a b _ hz).div hD.deriv hne)).mul (hPa a _ hz.1)

theorem b66f_gen_b66g_omega_residue_sum (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66f_gen_b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2) :
    ∑ x ∈ S ∪ S.image (fun x => g⁻¹ • x), TauCeti.Contour.residue
      (b66f_gen_b66g_omega R t g v V P (t, x) (t, g • x)) (R.atlas.A (t, x) (t, x)).2 = 0 := by
  set θ := b66f_gen_b66g_omegaForm R t g v V P
  have hres := b66f_gen_b66g_omegaForm_res R t h g S v hmero hv V hVa hV hP
  have hlin : HurwitzPrymRR_IsLinear θ := fun x c u w => b66f_gen_b66g_omegaForm_lin R t g v V P x c u w
  let w : b4c_MeroForm ℂ (b65z_fibre c₀ R.C t) (Module.finrank_self ℂ) :=
    ⟨θ, hlin, fun x => (hres x).1⟩
  have hsum := b4c_residue_sum (Module.finrank_self ℂ) w
  set F := S ∪ S.image (fun x => g⁻¹ • x)
  have hsupp : Function.support (fun x => b4c_res (hE := Module.finrank_self ℂ)
      (w : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c₀ R.C t) → ℂ) x) ⊆ ↑(F.map (b66f_gen_b66g_pt R t)) := by
    intro p hp
    by_contra hnot
    apply hp
    have hpF : p.val.2 ∉ F := by
      intro hm
      apply hnot
      refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨p.val.2, hm, ?_⟩)
      exact b66f_gen_b66g_fibre_mk R t p
    have h1 : p.val.2 ∉ S := fun hS => hpF (Finset.mem_union_left _ hS)
    have h2 : g • p.val.2 ∉ S := fun hS => hpF (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨g • p.val.2, hS, inv_smul_smul g _⟩))
    change TauCeti.Contour.residue (HurwitzPrymRR_loc (Module.finrank_self ℂ) θ p) 0 = 0
    rw [(hres p).2]
    apply TauCeti.Contour.residue_eq_zero_of_analyticAt
    have ha : p.val ∈ (R.atlas.A p.val).source := (R.atlas.hA p.val).1
    have hb : (g • p).val ∈ (R.atlas.A (g • p).val).source := (R.atlas.hA (g • p).val).1
    have han := b66f_gen_b66g_omega_analytic R t g S v hreg V hVa hP p.val (g • p).val p.val.2 h1 h2
      ((b66f_gen_b66g_mem_source R t _ p).mp ha) hb
    rwa [← b66f_gen_b66g_fibre_val R t p] at han
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map] at hsum
  refine Eq.trans ?_ hsum
  refine Finset.sum_congr rfl fun x _ => ?_
  exact ((hres (b66f_gen_b66g_pt R t x)).2).symm

theorem b66f_gen_b66g_vertical_self (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (b : b66f_Index R) (x : R.C) (hb : (t, x) ∈ (R.atlas.A b).source) :
    b66f_vertical R t b b x = 1 := by
  have hu : R.atlas.A b (t, x) ∈ (R.atlas.A b).target := (R.atlas.A b).map_source hb
  have he : b66f_transition R b b =ᶠ[𝓝 (R.atlas.A b (t, x))] Prod.snd := by
    filter_upwards [(R.atlas.A b).open_target.mem_nhds hu] with u hu'
    change (R.atlas.A b ((R.atlas.A b).symm u)).2 = u.2
    rw [(R.atlas.A b).right_inv hu']
  unfold b66f_vertical
  rw [he.fderiv_eq, fderiv_snd]
  rfl

theorem b66f_gen_b66g_pull_chart (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2) (g : b4b_Group) (a b : b66f_Index R)
    (y : R.C) (hb : (t, y) ∈ (R.atlas.A b).source) (ha : (t, g • y) ∈ (R.atlas.A a).source) :
    b66f_pull R t 2 g P b y =
      P a (g • y) * deriv (b66f_deckCoordinate R t g b a) (R.atlas.A b (t, y)).2 ^ 2 := by
  obtain ⟨_, hPl, _⟩ := b66f_gen_b66g_forms_spec R t 2 hP
  have hc : (t, g • y) ∈ (R.atlas.A (t, g • y)).source := (R.atlas.hA _).1
  have hch := b66f_gen_b66g_deck_chain R t g b a b (t, g • y) y hb hb ha hc
  rw [b66f_gen_b66g_vertical_self R t b y hb, mul_one] at hch
  change (if (t, y) ∈ (R.atlas.A b).source then P (t, g • y) (g • y) *
    deriv (b66f_deckCoordinate R t g b (t, g • y)) (R.atlas.A b (t, y)).2 ^ 2 else 0) = _
  rw [ite_eq_left hb, hch, hPl a (t, g • y) (g • y) ha hc]
  ring

theorem b66f_gen_b66g_residueSum_extend (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S T : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hreg : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    {m : ℕ} {q : b66f_Coeff R} (hq : q ∈ b66f_forms R t m) (hST : S ⊆ T) :
    b66f_residueSum R t T v q = b66f_residueSum R t S v q := by
  obtain ⟨hqa, _, _⟩ := b66f_gen_b66g_forms_spec R t m hq
  unfold b66f_residueSum
  symm
  refine Finset.sum_subset hST fun x _ hx => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66f_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66f_gen_b66g_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  apply TauCeti.Contour.residue_eq_zero_of_analyticAt
  refine (hreg (t, x) _ hdom ?_).mul (hqa (t, x) _ hdom)
  rw [(b66f_gen_b66g_chart_slice R t (t, x) x hxa).2]
  exact hx

theorem b66f_gen_b66g_residue_pull_inv (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (g : b4b_Group) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (V : b66f_Index R → b66f_Index R → ℂ → ℂ)
    (hVa : ∀ a b, AnalyticOnNhd ℂ (V a b) (b66f_gen_b66k_refinementDomain R t g a b))
    (hV : ∀ (a b c d : b66f_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66f_cocycle R t h b d (g • x) -
          deriv (b66f_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66f_cocycle R t h a c x =
          b66f_vertical R t b d (g • x) * V a b (R.atlas.A a (t, x)).2 -
            V c d (R.atlas.A c (t, x)).2)
    {P : b66f_Coeff R} (hP : P ∈ b66f_forms R t 2)
    (hPg : b66f_pull R t 2 g⁻¹ P ∈ b66f_forms R t 2) :
    b66f_residueSum R t S v (b66f_pull R t 2 g⁻¹ P) = b66f_residueSum R t S v P := by
  obtain ⟨hPa, _, _⟩ := b66f_gen_b66g_forms_spec R t 2 hP
  obtain ⟨hQa, _, _⟩ := b66f_gen_b66g_forms_spec R t 2 hPg
  set Q := b66f_pull R t 2 g⁻¹ P
  set F := S ∪ S.image (fun x => g⁻¹ • x)
  have hzero := b66f_gen_b66g_omega_residue_sum R t h g S v hmero hreg hv V hVa hV hP
  have hterm : ∀ x : R.C, TauCeti.Contour.residue
      (b66f_gen_b66g_omega R t g v V P (t, x) (t, g • x)) (R.atlas.A (t, x) (t, x)).2 =
      TauCeti.Contour.residue (fun w => v (t, g • x) w *
        Q (t, g • x) ((R.atlas.A (t, g • x)).symm (t.val, w)).2)
        (R.atlas.A (t, g • x) (t, g • x)).2 -
      TauCeti.Contour.residue (fun z => v (t, x) z *
        P (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 := by
    intro x
    set a : b66f_Index R := (t, x)
    set b : b66f_Index R := (t, g • x)
    have ha : (t, x) ∈ (R.atlas.A a).source := (R.atlas.hA a).1
    have hb : (t, g • x) ∈ (R.atlas.A b).source := (R.atlas.hA b).1
    set z₀ := (R.atlas.A a (t, x)).2
    set D := b66f_deckCoordinate R t g a b
    have hz := b66f_gen_b66g_refinement_point R t g a b x ha hb
    have hDa := b66f_gen_b66k_deckCoordinate_analytic R t g a b z₀ hz
    have hne := b66f_gen_b66g_deck_ne R t g a b z₀ hz
    have hDz : D z₀ = (R.atlas.A b (t, g • x)).2 := b66f_gen_b66g_deck_value R t g a b x ha
    have hDdom : D z₀ ∈ b66f_domain R t b := (b66f_gen_b66g_deck_inverse R t g a b z₀ hz).1.1
    set f1 : ℂ → ℂ := fun z => v b (D z) / deriv D z * P a ((R.atlas.A a).symm (t.val, z)).2
    set f2 : ℂ → ℂ := fun z => v a z * P a ((R.atlas.A a).symm (t.val, z)).2
    set f3 : ℂ → ℂ := fun z => V a b z / deriv D z * P a ((R.atlas.A a).symm (t.val, z)).2
    have hsplit : b66f_gen_b66g_omega R t g v V P a b = f1 - f2 - f3 := by
      funext z
      simp only [b66f_gen_b66g_omega, b66f_gen_b66g_pulled, f1, f2, f3, Pi.sub_apply, D]
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
    filter_upwards [b66f_gen_b66g_refinement_eventually R t g a b z₀ hz] with z hzz
    obtain ⟨hDzz, _, hinv⟩ := b66f_gen_b66g_deck_inverse R t g a b z hzz
    have hxz := b66f_gen_b66k_inverse_slice R t a z hzz.1
    set y := ((R.atlas.A a).symm (t.val, z)).2
    have hya : (t, y) ∈ (R.atlas.A a).source := by
      rw [hxz]
      exact (R.atlas.A a).map_target hzz.1
    have hyz : (R.atlas.A a (t, y)).2 = z := by rw [hxz, (R.atlas.A a).right_inv hzz.1]
    have hgy : (t, g • y) ∈ (R.atlas.A b).source := hzz.2
    have hDy : D z = (R.atlas.A b (t, g • y)).2 := by
      rw [← hyz]
      exact b66f_gen_b66g_deck_value R t g a b y hya
    have hsy : ((R.atlas.A b).symm (t.val, D z)).2 = g • y := by
      rw [hDy]
      exact (b66f_gen_b66g_chart_slice R t b (g • y) hgy).2
    have hpc := b66f_gen_b66g_pull_chart R t hP g⁻¹ a b (g • y) hgy (by rwa [inv_smul_smul])
    rw [inv_smul_smul] at hpc
    have hpc' : Q b (g • y) = P a y *
        deriv (b66f_deckCoordinate R t g⁻¹ b a) (R.atlas.A b (t, g • y)).2 ^ 2 := hpc
    have hne' := b66f_gen_b66g_deck_ne R t g a b z hzz
    simp only [Fb, f1]
    rw [hsy, hpc', ← hDy]
    have hinv' : deriv (b66f_deckCoordinate R t g⁻¹ b a) (D z) = (deriv D z)⁻¹ :=
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
      b66f_residueSum R t S v P :=
    b66f_gen_b66g_residueSum_extend R t S F v hreg hP Finset.subset_union_left
  have h2 : ∑ x ∈ F, TauCeti.Contour.residue (fun w => v (t, g • x) w *
      Q (t, g • x) ((R.atlas.A (t, g • x)).symm (t.val, w)).2)
        (R.atlas.A (t, g • x) (t, g • x)).2 = b66f_residueSum R t S v Q := by
    have hinj : Set.InjOn (fun x : R.C => g • x) ↑F := fun x _ y _ hxy => smul_left_cancel g hxy
    rw [← b66f_gen_b66g_residueSum_extend R t S (F.image (fun x => g • x)) v hreg hPg ?_]
    · unfold b66f_residueSum
      rw [Finset.sum_image hinj]
    · intro y hy
      refine Finset.mem_image.mpr ⟨g⁻¹ • y, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩), smul_inv_smul g y⟩
  rw [h1, h2] at hsum
  exact sub_eq_zero.mp hsum.symm

theorem b66f_gen_b66g_residueSum_smul (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ) (c : ℂ) (q : b66f_Coeff R) :
    b66f_residueSum R t S v (c • q) = c * b66f_residueSum R t S v q := by
  unfold b66f_residueSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TauCeti.Contour.residue_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem b66f_gen_b66g_residueSum_sum (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    {ι : Type} (s : Finset ι) (q : ι → b66f_Coeff R) (hq : ∀ i, q i ∈ b66f_forms R t 2) :
    b66f_residueSum R t S v (∑ i ∈ s, q i) = ∑ i ∈ s, b66f_residueSum R t S v (q i) := by
  unfold b66f_residueSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hxa : (t, x) ∈ (R.atlas.A (t, x)).source := (R.atlas.hA _).1
  have hdom : (R.atlas.A (t, x) (t, x)).2 ∈ b66f_domain R t (t, x) := by
    show (t.val, (R.atlas.A (t, x) (t, x)).2) ∈ (R.atlas.A (t, x)).target
    rw [← (b66f_gen_b66g_chart_slice R t (t, x) x hxa).1]
    exact (R.atlas.A (t, x)).map_source hxa
  have hm : ∀ i ∈ s, MeromorphicAt (fun z => v (t, x) z *
      q i (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2) (R.atlas.A (t, x) (t, x)).2 :=
    fun i _ => (hmero (t, x) _ hdom).mul
      ((b66f_gen_b66g_forms_spec R t 2 (hq i)).1 (t, x) _ hdom).meromorphicAt
  rw [← TauCeti.Contour.residue_sum s hm]
  congr 1
  funext z
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]

theorem b66f_gen_b66g_invariant_primitive_aux (R : b65z_SharedFamily c₀ g₀) (t : b6t_polydisc c₀)
    (h : Fin 10 → ℂ) (S : Finset R.C) (v : b66f_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66f_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66f_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66f_cocycle R t h a b x = b66f_boundary R t v a b x)
    (q r : b66f_primitiveForms R t) :
    ∃ Q : b66f_forms R t 2,
      Q.val = b66f_average R t (b66f_product R q.val r.val) ∧
      (∀ g : b4b_Group, b66f_pull R t 2 g Q.val = Q.val) ∧
      b66f_residueSum R t S v Q.val =
        b66f_residueSum R t S v (b66f_product R q.val r.val) := by
  have hq : q.val ∈ b66f_forms R t 1 := (Submodule.mem_inf.mp q.property).1
  have hr : r.val ∈ b66f_forms R t 1 := (Submodule.mem_inf.mp r.property).1
  obtain ⟨hmem, hinv⟩ := b66f_gen_b66g_average_product R t hq hr
  refine ⟨⟨_, hmem⟩, rfl, hinv, ?_⟩
  set P := b66f_product R q.val r.val
  have hP : P ∈ b66f_forms R t 2 := (b66f_gen_b66g_cup_aux R t).2 ⟨_, hq⟩ ⟨_, hr⟩
  have hPg : ∀ g : b4b_Group, b66f_pull R t 2 g P ∈ b66f_forms R t 2 := fun g => by
    rw [b66f_gen_b66g_pull_product]
    exact (b66f_gen_b66g_cup_aux R t).2 ⟨_, b66f_gen_b66g_pull_one_mem R t hq g⟩ ⟨_, b66f_gen_b66g_pull_one_mem R t hr g⟩
  have heach : ∀ g : b4b_Group, b66f_residueSum R t S v (b66f_pull R t 2 g P) =
      b66f_residueSum R t S v P := by
    intro g
    obtain ⟨V, hVa, hV⟩ := b66f_gen_b66k_deck_invariant R t h g⁻¹
    have := b66f_gen_b66g_residue_pull_inv R t h g⁻¹ S v hmero hreg hv V hVa hV hP
      (by rw [inv_inv]; exact hPg g)
    rwa [inv_inv] at this
  change b66f_residueSum R t S v (b66f_average R t P) = _
  rw [b66f_gen_b66g_average_apply, b66f_gen_b66g_residueSum_smul,
    b66f_gen_b66g_residueSum_sum R t S v hmero Finset.univ _ hPg]
  simp only [heach, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card b4b_Group : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  rfl

end HodgeLean.Foundations.Program
