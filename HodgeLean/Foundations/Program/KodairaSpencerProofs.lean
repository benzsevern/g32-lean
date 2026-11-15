import HodgeLean.Foundations.Program.KodairaSpencerDefs

noncomputable section
open Set Filter Topology Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan

theorem b66k_transition_analytic (R : rf8_SharedFamily) (a b : b66k_Index R)
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    AnalyticAt ℂ (b66k_transition R a b) u := by
  have hc := (contDiffGroupoid ω 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)).compatible
    (R.atlas.hA a).2 (R.atlas.hA b).2
  have hd := (mem_groupoid_of_pregroupoid.mp hc).1
  have hd' : ContDiffOn ℂ ω ((R.atlas.A a).symm.trans (R.atlas.A b))
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using hd
  exact analyticAt_snd.comp (hd'.contDiffAt (((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu)).analyticAt

theorem b66k_inverse_parameter (R : rf8_SharedFamily) (a : b66k_Index R)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (R.atlas.A a).target) :
    ((R.atlas.A a).symm u).1.val = u.1 := by
  rw [← R.atlas.hparam a _ ((R.atlas.A a).map_target hu),
    (R.atlas.A a).right_inv hu]

theorem b66k_inverse_slice (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) (z : ℂ) (hz : (t.val, z) ∈ (R.atlas.A a).target) :
    (t, ((R.atlas.A a).symm (t.val, z)).2) = (R.atlas.A a).symm (t.val, z) := by
  apply Prod.ext
  · exact Subtype.ext (b66k_inverse_parameter R a _ hz).symm
  · rfl

theorem b66k_cocycle_law_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (a b c : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66k_cocycle R t h a c x = b66k_cocycle R t h b c x +
      b66k_vertical R t b c x * b66k_cocycle R t h a b x := by
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
      L (h, q) = L (h, 0) + q * L (0, 1) := by
    have hp : (h, q) = (h, (0 : ℂ)) + q • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by
      simp
    rw [hp, map_add, map_smul]
    rfl
  simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A c).source from ⟨ha, hc⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A b).source ∩ (R.atlas.A c).source from ⟨hb, hc⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨ha, hb⟩),
    b66k_vertical]
  change fderiv ℂ (b66k_transition R a c) u (h, 0) = _
  rw [hf]
  change fderiv ℂ (b66k_transition R b c) w
    (h, fderiv ℂ (b66k_transition R a b) u (h, 0)) = _
  rw [hl, mul_comm]


theorem b66k_cocycle_holomorphic_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (a b : b66k_Index R) :
    AnalyticOnNhd ℂ
      (fun z => b66k_cocycle R t h a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b) := by
  intro z hz
  have hi := b66k_inverse_slice R t a z hz.1
  have hm : (t.val, z) ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨hz.1, ?_⟩
    change (R.atlas.A a).symm (t.val, z) ∈ (R.atlas.A b).source
    simpa only [one_smul, hi] using hz.2
  have hd : ContDiffAt ℂ ω (b66k_transition R a b) (t.val, z) :=
    (b66k_transition_analytic R a b _ hm).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => fderiv ℂ (b66k_transition R a b) u (h, 0)) (t.val, z) :=
    (hd.fderiv_right (by simp)).clm_apply contDiffAt_const
  apply ContDiffAt.analyticAt
  apply (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq
  have hopen := ((R.atlas.A a).symm.trans (R.atlas.A b)).open_source
  have hev := (continuous_const.prodMk continuous_id).continuousAt
    (hopen.mem_nhds hm)
  filter_upwards [hev] with w hw
  change (t.val, w) ∈ (R.atlas.A a).target ∧
    (R.atlas.A a).symm (t.val, w) ∈ (R.atlas.A b).source at hw
  have hiw := b66k_inverse_slice R t a w hw.1
  have hmem : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈
      (R.atlas.A a).source ∩ (R.atlas.A b).source := by
    rw [hiw]
    exact ⟨(R.atlas.A a).map_target hw.1, hw.2⟩
  simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hmem,
    hiw, (R.atlas.A a).right_inv hw.1]
  rfl

theorem b66k_branch_transition (R : rf8_SharedFamily) (i : Fin 10)
    (a b : b66k_Index R)
    (ha : R.atlas.f a.2 = b6_branch mr_base (Fin.castAdd 3 i))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    b66k_transition R a b u = u.1 i + u.2 ^ R.atlas.n a.2 := by
  have hm := (R.atlas.hmark a (Fin.castAdd 3 i) ha).2 _
    ((R.atlas.A a).map_target hu.1)
  have hf := (R.atlas.hfree b hb).2 ((R.atlas.A a).symm u) hu.2
  rw [hf] at hm
  simp only [b6a_value, Fin.val_castAdd, i.isLt, ↓reduceDIte] at hm
  have hp := b66k_inverse_parameter R a u hu.1
  rw [hp, (R.atlas.A a).right_inv hu.1] at hm
  exact OnePoint.coe_injective hm

theorem b66k_branch_coordinate_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (i : Fin 10) (a b : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base (Fin.castAdd 3 i))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source)
    (hxb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_cocycle R t h a b x = h i ∧
      b66k_vertical R t a b x =
        (R.atlas.n a.2 : ℂ) * (R.atlas.A a (t, x)).2 ^ (R.atlas.n a.2 - 1) := by
  have hu : R.atlas.A a (t, x) ∈
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨(R.atlas.A a).map_source hxa, ?_⟩
    change (R.atlas.A a).symm (R.atlas.A a (t, x)) ∈ (R.atlas.A b).source
    rwa [(R.atlas.A a).left_inv hxa]
  have he : b66k_transition R a b =ᶠ[𝓝 (R.atlas.A a (t, x))]
      (fun u : (Fin 10 → ℂ) × ℂ => u.1 i + u.2 ^ R.atlas.n a.2) := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu]
      with u hu
    exact b66k_branch_transition R i a b ha hb u hu
  have hd := ((ContinuousLinearMap.proj i).hasFDerivAt.comp (R.atlas.A a (t, x))
    (ContinuousLinearMap.fst ℂ (Fin 10 → ℂ) ℂ).hasFDerivAt).add
    ((ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ).hasFDerivAt.pow (R.atlas.n a.2))
  have hf := (hd.congr_of_eventuallyEq he).fderiv
  constructor
  · simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
      ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨hxa, hxb⟩)]
    rw [hf]
    simp
  · unfold b66k_vertical
    rw [hf]
    simp


def b66k_totalDeck (R : rf8_SharedFamily) (g : b4b_Group)
    (q : b6t_polydisc mr_base × R.C) : b6t_polydisc mr_base × R.C :=
  (q.1, g • q.2)

theorem b66k_totalDeck_holomorphic (R : rf8_SharedFamily) (g : b4b_Group) :
    ContMDiff 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (b66k_totalDeck R g) := by
  apply b6a_lift_contMDiff mr_base R.C R.atlas.f R.atlas.n R.atlas.hn
    R.atlas.A R.atlas.hA R.atlas.hparam
    (fun q hq => (R.atlas.hfree q hq).2) R.atlas.hmark
  · exact continuous_fst.prodMk ((R.hC g).comp continuous_snd)
  · intro q
    rfl
  · intro q
    exact R.atlas.hgal.1 g q.2

def b66k_deckTransition (R : rf8_SharedFamily) (g : b4b_Group)
    (a b : b66k_Index R) (u : (Fin 10 → ℂ) × ℂ) : ℂ :=
  (R.atlas.A b (b66k_totalDeck R g ((R.atlas.A a).symm u))).2

theorem b66k_deckTransition_analytic (R : rf8_SharedFamily) (g : b4b_Group)
    (a b : b66k_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source) :
    AnalyticAt ℂ (b66k_deckTransition R g a b) u := by
  have hi : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (R.atlas.A a).symm u :=
    contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (R.atlas.hA a).2) ha
  have hg := (b66k_totalDeck_holomorphic R g).contMDiffAt.comp u hi
  have hc : ContMDiffAt 𝓘(ℂ, (Fin 10 → ℂ) × ℂ)
      𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (R.atlas.A b)
      (b66k_totalDeck R g ((R.atlas.A a).symm u)) :=
    contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (R.atlas.hA b).2) hb
  exact analyticAt_snd.comp ((hc.comp u hg).contDiffAt.analyticAt)

theorem b66k_deck_overlap_nhds (R : rf8_SharedFamily) (g : b4b_Group)
    (a b : b66k_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source) :
    ∀ᶠ v in 𝓝 u, v ∈ (R.atlas.A a).target ∧
      b66k_totalDeck R g ((R.atlas.A a).symm v) ∈ (R.atlas.A b).source := by
  have hcont := (b66k_totalDeck_holomorphic R g).continuous.continuousAt.comp
    ((R.atlas.A a).continuousAt_symm ha)
  filter_upwards [(R.atlas.A a).open_target.mem_nhds ha,
    hcont ((R.atlas.A b).open_source.mem_nhds hb)] with v hv hv'
  exact ⟨hv, hv'⟩

theorem b66k_chain_parameter
    (F G : ((Fin 10 → ℂ) × ℂ) → ℂ) (u : (Fin 10 → ℂ) × ℂ)
    (h : Fin 10 → ℂ) (hF : DifferentiableAt ℂ F u)
    (hG : DifferentiableAt ℂ G (u.1, F u)) :
    fderiv ℂ (fun v => G (v.1, F v)) u (h, 0) =
      fderiv ℂ G (u.1, F u) (h, 0) +
        fderiv ℂ G (u.1, F u) (0, 1) * fderiv ℂ F u (h, 0) := by
  change fderiv ℂ (G ∘ (fun v => (v.1, F v))) u (h, 0) = _
  rw [(hG.hasFDerivAt.comp u (hasFDerivAt_fst.prodMk hF.hasFDerivAt)).fderiv]
  change fderiv ℂ G (u.1, F u) (h, fderiv ℂ F u (h, 0)) = _
  have hp : (h, fderiv ℂ F u (h, 0)) = (h, (0 : ℂ)) +
      fderiv ℂ F u (h, 0) • ((0 : Fin 10 → ℂ), (1 : ℂ)) := by simp
  rw [hp, map_add, map_smul, smul_eq_mul, mul_comm]

theorem b66k_deck_parameter_holomorphic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (g : b4b_Group)
    (a b : b66k_Index R) :
    AnalyticOnNhd ℂ
      (fun z => -fderiv ℂ (b66k_deckTransition R g a b) (t.val, z) (h, 0))
      (b66k_refinementDomain R t g a b) := by
  intro z hz
  have hb : b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66k_totalDeck
    rw [← b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd : ContDiffAt ℂ ω (b66k_deckTransition R g a b) (t.val, z) :=
    (b66k_deckTransition_analytic R g a b _ hz.1 hb).contDiffAt
  have hd' : ContDiffAt ℂ ω
      (fun u => -fderiv ℂ (b66k_deckTransition R g a b) u (h, 0)) (t.val, z) :=
    ((hd.fderiv_right (by simp)).clm_apply contDiffAt_const).neg
  exact (hd'.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt

theorem b66k_deck_vertical (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t g a b) :
    deriv (b66k_deckCoordinate R t g a b) z =
      fderiv ℂ (b66k_deckTransition R g a b) (t.val, z) (0, 1) := by
  have hb : b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66k_totalDeck
    rw [← b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd := (b66k_deckTransition_analytic R g a b _ hz.1 hb).differentiableAt
  have he : b66k_deckCoordinate R t g a b =ᶠ[𝓝 z]
      (fun w => b66k_deckTransition R g a b (t.val, w)) := by
    have hn := (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_target.mem_nhds hz.1)
    filter_upwards [hn] with w hw
    unfold b66k_deckCoordinate b66k_deckTransition b66k_totalDeck
    rw [← b66k_inverse_slice R t a w hw]
  have hd' := hd.hasFDerivAt.comp z
    (hasFDerivAt_const (c := t.val) z |>.prodMk (hasFDerivAt_id z))
  rw [he.deriv_eq]
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hd'.fderiv

theorem b66k_deck_square (R : rf8_SharedFamily) (g : b4b_Group)
    (a b c d : b66k_Index R) (u : (Fin 10 → ℂ) × ℂ)
    (ha : u ∈ (R.atlas.A a).target)
    (hb : b66k_totalDeck R g ((R.atlas.A a).symm u) ∈ (R.atlas.A b).source)
    (hc : (R.atlas.A a).symm u ∈ (R.atlas.A c).source) :
    (fun v => b66k_transition R b d (v.1, b66k_deckTransition R g a b v)) =ᶠ[𝓝 u]
      (fun v => b66k_deckTransition R g c d (v.1, b66k_transition R a c v)) := by
  have hn : ∀ᶠ v in 𝓝 u, (R.atlas.A a).symm v ∈ (R.atlas.A c).source :=
    ((R.atlas.A a).continuousAt_symm ha) ((R.atlas.A c).open_source.mem_nhds hc)
  filter_upwards [b66k_deck_overlap_nhds R g a b u ha hb, hn] with v hv hv'
  have hp := b66k_inverse_parameter R a v hv.1
  have ht : (v.1, b66k_transition R a c v) =
      R.atlas.A c ((R.atlas.A a).symm v) := by
    apply Prod.ext
    · exact hp.symm.trans (R.atlas.hparam c _ hv').symm
    · rfl
  have hg : (v.1, b66k_deckTransition R g a b v) =
      R.atlas.A b (b66k_totalDeck R g ((R.atlas.A a).symm v)) := by
    apply Prod.ext
    · exact hp.symm.trans (R.atlas.hparam b _ hv.2).symm
    · rfl
  change (R.atlas.A d ((R.atlas.A b).symm
    (v.1, b66k_deckTransition R g a b v))).2 =
    (R.atlas.A d (b66k_totalDeck R g ((R.atlas.A c).symm
      (v.1, b66k_transition R a c v)))).2
  rw [hg, ht, (R.atlas.A b).left_inv hv.2, (R.atlas.A c).left_inv hv']

theorem b66k_deck_invariant_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) :
    ∃ v : b66k_Index R → b66k_Index R → ℂ → ℂ,
      (∀ a b, AnalyticOnNhd ℂ (v a b) (b66k_refinementDomain R t g a b)) ∧
      ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * v a b (R.atlas.A a (t, x)).2 -
            v c d (R.atlas.A c (t, x)).2 := by
  refine ⟨fun a b z => -fderiv ℂ (b66k_deckTransition R g a b) (t.val, z) (h, 0),
    b66k_deck_parameter_holomorphic R t h g, ?_⟩
  intro a b c d x ha hc hb hd
  let u := R.atlas.A a (t, x)
  let w := R.atlas.A b (t, g • x)
  let q := R.atlas.A c (t, x)
  have hau : u ∈ (R.atlas.A a).target := (R.atlas.A a).map_source ha
  have hbu : b66k_totalDeck R g ((R.atlas.A a).symm u) ∈
      (R.atlas.A b).source := by
    simpa only [u, (R.atlas.A a).left_inv ha, b66k_totalDeck] using hb
  have hcu : (R.atlas.A a).symm u ∈ (R.atlas.A c).source := by
    simpa only [u, (R.atlas.A a).left_inv ha] using hc
  have hac : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A c)).source := ⟨hau, hcu⟩
  have hbd : w ∈ ((R.atlas.A b).symm.trans (R.atlas.A d)).source := by
    refine ⟨(R.atlas.A b).map_source hb, ?_⟩
    change (R.atlas.A b).symm w ∈ (R.atlas.A d).source
    simpa only [w, (R.atlas.A b).left_inv hb] using hd
  have hcq : q ∈ (R.atlas.A c).target := (R.atlas.A c).map_source hc
  have hdq : b66k_totalDeck R g ((R.atlas.A c).symm q) ∈
      (R.atlas.A d).source := by
    simpa only [q, (R.atlas.A c).left_inv hc, b66k_totalDeck] using hd
  have hw : (u.1, b66k_deckTransition R g a b u) = w := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam b _ hb).symm
    · exact congrArg (fun y => (R.atlas.A b (b66k_totalDeck R g y)).2)
        ((R.atlas.A a).left_inv ha)
  have hq : (u.1, b66k_transition R a c u) = q := by
    apply Prod.ext
    · exact (R.atlas.hparam a _ ha).trans (R.atlas.hparam c _ hc).symm
    · exact congrArg (fun y => (R.atlas.A c y).2) ((R.atlas.A a).left_inv ha)
  have h1 := b66k_chain_parameter (b66k_deckTransition R g a b)
    (b66k_transition R b d) u h
    (b66k_deckTransition_analytic R g a b u hau hbu).differentiableAt
    (by rw [hw]; exact (b66k_transition_analytic R b d w hbd).differentiableAt)
  have h2 := b66k_chain_parameter (b66k_transition R a c)
    (b66k_deckTransition R g c d) u h
    (b66k_transition_analytic R a c u hac).differentiableAt
    (by rw [hq]; exact (b66k_deckTransition_analytic R g c d q hcq hdq).differentiableAt)
  rw [hw] at h1
  rw [hq] at h2
  have he := congrArg (fun L : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ => L (h, 0))
    (b66k_deck_square R g a b c d u hau hbu hcu).fderiv_eq
  rw [h1, h2] at he
  have hz : (R.atlas.A c (t, x)).2 ∈ b66k_refinementDomain R t g c d := by
    constructor
    · rw [← R.atlas.hparam c _ hc]
      exact hcq
    · have hpair : (t.val, (R.atlas.A c (t, x)).2) = q := by
        exact Prod.ext (R.atlas.hparam c _ hc).symm rfl
      rw [hpair, show q = R.atlas.A c (t, x) from rfl, (R.atlas.A c).left_inv hc]
      exact hd
  rw [b66k_deck_vertical R t g c d _ hz]
  simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
    ite_eq_left (show (t, g • x) ∈ (R.atlas.A b).source ∩ (R.atlas.A d).source from ⟨hb, hd⟩),
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A c).source from ⟨ha, hc⟩),
    b66k_vertical]
  have hpa : (t.val, (R.atlas.A a (t, x)).2) = u :=
    Prod.ext (R.atlas.hparam a _ ha).symm rfl
  have hpc : (t.val, (R.atlas.A c (t, x)).2) = q :=
    Prod.ext (R.atlas.hparam c _ hc).symm rfl
  rw [hpa, hpc]
  change fderiv ℂ (b66k_transition R b d) w (h, 0) -
    fderiv ℂ (b66k_deckTransition R g c d) q (0, 1) *
      fderiv ℂ (b66k_transition R a c) u (h, 0) = _
  linear_combination he


theorem b66k_cocycle_mem (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) :
    b66k_cocycle R t h ∈ b66k_holomorphicCochains R t ⊓
      LinearMap.ker (b66k_differential R t) := by
  constructor
  · apply Submodule.subset_span
    refine ⟨b66k_cocycle_holomorphic_aux R t h, ?_⟩
    intro a b x hx
    simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hx]
  · change b66k_differential R t (b66k_cocycle R t h) = 0
    funext a b c x
    simp only [b66k_differential, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs with hx
    · rw [b66k_cocycle_law_aux R t h a b c x hx.1.1 hx.1.2 hx.2]
      ring
    · rfl

def b66k_factor (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (Fin 10 → ℂ) →ₗ[ℂ] b66k_cechH1 R t :=
  (b66k_kodairaSpencer R t).codRestrict _ fun h =>
    ⟨b66k_cocycle R t h, b66k_cocycle_mem R t h, rfl⟩

theorem b66k_factor_comp (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (b66k_cechH1 R t).subtype.comp (b66k_factor R t) = b66k_kodairaSpencer R t := rfl

theorem b66k_boundary_add (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v w : b66k_Index R → ℂ → ℂ) :
    b66k_boundary R t (v + w) = b66k_boundary R t v + b66k_boundary R t w := by
  funext a b x
  simp only [b66k_boundary, Pi.add_apply]
  split_ifs <;> ring

theorem b66k_boundary_smul (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (k : ℂ) (v : b66k_Index R → ℂ → ℂ) :
    b66k_boundary R t (k • v) = k • b66k_boundary R t v := by
  funext a b x
  simp only [b66k_boundary, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem b66k_boundary_representation (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (c : b66k_Cochain R)
    (hc : c ∈ b66k_boundaries R t) :
    ∃ v : b66k_Index R → ℂ → ℂ,
      (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧ c = b66k_boundary R t v := by
  induction hc using Submodule.span_induction with
  | mem c hc => exact hc
  | zero =>
    refine ⟨0, fun a z hz => analyticAt_const, ?_⟩
    funext a b x
    simp [b66k_boundary]
  | add c d hc hd hc' hd' =>
    obtain ⟨v, hv, rfl⟩ := hc'
    obtain ⟨w, hw, rfl⟩ := hd'
    exact ⟨v + w, fun a => (hv a).add (hw a), (b66k_boundary_add R t v w).symm⟩
  | smul k c hc hc' =>
    obtain ⟨v, hv, rfl⟩ := hc'
    refine ⟨k • v, ?_, (b66k_boundary_smul R t k v).symm⟩
    intro a
    simpa only [Pi.smul_apply] using (hv a).const_smul (c := k)

theorem b66k_kernel_splitting (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (hh : b66k_kodairaSpencer R t h = 0) :
    ∃ v : b66k_Index R → ℂ → ℂ,
      (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧
      ∀ (a b : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source → (t, x) ∈ (R.atlas.A b).source →
        v b (R.atlas.A b (t, x)).2 = b66k_cocycle R t h a b x +
          b66k_vertical R t a b x * v a (R.atlas.A a (t, x)).2 := by
  have hm : b66k_cocycle R t h ∈ b66k_boundaries R t := by
    apply (Submodule.Quotient.mk_eq_zero (b66k_boundaries R t)).mp
    exact hh
  obtain ⟨w, hw, he⟩ := b66k_boundary_representation R t _ hm
  refine ⟨-w, fun a => (hw a).neg, ?_⟩
  intro a b x ha hb
  have he' := congrFun (congrFun (congrFun he a) b) x
  simp only [b66k_boundary, ite_eq_left (show
    (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨ha, hb⟩)] at he'
  simp only [Pi.neg_apply]
  linear_combination -he'

theorem b66k_free_transition (R : rf8_SharedFamily) (a b : b66k_Index R)
    (ha : R.atlas.f a.2 ∉ Set.range (b6_branch mr_base))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    b66k_transition R a b u = u.2 := by
  have hfa := (R.atlas.hfree a ha).2 ((R.atlas.A a).symm u)
    ((R.atlas.A a).map_target hu.1)
  have hfb := (R.atlas.hfree b hb).2 ((R.atlas.A a).symm u) hu.2
  apply OnePoint.coe_injective
  change ((R.atlas.A b ((R.atlas.A a).symm u)).2 : OnePoint ℂ) = _
  rw [← hfb, hfa, (R.atlas.A a).right_inv hu.1]

theorem b66k_free_coefficients (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (a b : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 ∉ Set.range (b6_branch mr_base))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source)
    (hxb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_cocycle R t h a b x = 0 ∧ b66k_vertical R t a b x = 1 := by
  have hu : R.atlas.A a (t, x) ∈
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨(R.atlas.A a).map_source hxa, ?_⟩
    change (R.atlas.A a).symm (R.atlas.A a (t, x)) ∈ (R.atlas.A b).source
    rwa [(R.atlas.A a).left_inv hxa]
  have he : b66k_transition R a b =ᶠ[𝓝 (R.atlas.A a (t, x))] Prod.snd := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu]
      with u hu
    exact b66k_free_transition R a b ha hb u hu
  constructor
  · simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
      ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨hxa, hxb⟩)]
    rw [he.fderiv_eq, fderiv_snd]
    rfl
  · unfold b66k_vertical
    rw [he.fderiv_eq, fderiv_snd]
    rfl

theorem b66k_sphere_coefficient_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hinfty : Tendsto (fun z => z⁻¹ ^ 2 * f z) (cocompact ℂ) (𝓝 0)) : f = 0 := by
  let p := dslope f 0
  have hp : Differentiable ℂ p := by
    rw [← differentiableOn_univ] at hf ⊢
    exact (Complex.differentiableOn_dslope (c := 0) Filter.univ_mem).mpr hf
  have hp1 : p 1 = 0 := by
    have he := sub_smul_dslope f 0 1
    simpa only [sub_zero, one_smul, h1, h0] using he
  let q := dslope p 1
  have hq : Differentiable ℂ q := by
    rw [← differentiableOn_univ] at hp ⊢
    exact (Complex.differentiableOn_dslope (c := 1) Filter.univ_mem).mpr hp
  have hfactor (z : ℂ) : f z = z * (z - 1) * q z := by
    have he := sub_smul_dslope f 0 z
    have he' := sub_smul_dslope p 1 z
    simp only [sub_zero, smul_eq_mul, h0, hp1] at he he'
    change (z - 1) * q z = p z at he'
    change z * p z = f z at he
    rw [← he, ← he']
    ring
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  have hlim : Tendsto q (cocompact ℂ) (𝓝 0) := by
    have ht := hinfty.div (tendsto_const_nhds.sub hi)
      (by norm_num : (1 : ℂ) - 0 ≠ 0)
    simp only [sub_zero, div_one] at ht
    apply ht.congr'
    have hz0 : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      rw [← Metric.cobounded_eq_cocompact]
      exact Bornology.eventually_ne_cobounded 0
    have hz1 : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 1 := by
      rw [← Metric.cobounded_eq_cocompact]
      exact Bornology.eventually_ne_cobounded 1
    filter_upwards [hz0, hz1] with z hz0 hz1
    change (z⁻¹ ^ 2 * f z) / (1 - z⁻¹) = q z
    rw [hfactor z]
    field_simp [hz0, sub_ne_zero.mpr hz1]
  funext z
  rw [hfactor z, hq.apply_eq_of_tendsto_cocompact z hlim]
  simp

def b66k_freeCoefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) (x : R.C) : ℂ :=
  v (t, x) (R.atlas.A (t, x) (t, x)).2

theorem b66k_freeCoefficient_eq (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (a : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 ∉ Set.range (b6_branch mr_base))
    (hx : R.atlas.f x ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source) :
    b66k_freeCoefficient R t v x = v a (R.atlas.A a (t, x)).2 := by
  have hself := (R.atlas.hA (t, x)).1
  have he := congrFun (congrFun (congrFun hv a) (t, x)) x
  rw [(b66k_free_coefficients R t h a (t, x) x ha hx hxa hself).1] at he
  simp only [b66k_boundary,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A (t, x)).source from
      ⟨hxa, hself⟩), (b66k_free_coefficients R t h a (t, x) x ha hx hxa hself).2,
    one_mul] at he
  exact (sub_eq_zero.mp he.symm).symm

theorem b66k_freeCoefficient_analytic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (a : b66k_Index R) (ha : R.atlas.f a.2 ∉ Set.range (b6_branch mr_base)) :
    AnalyticOnNhd ℂ
      (fun z => b66k_freeCoefficient R t v ((R.atlas.A a).symm (t.val, z)).2)
      {z | (t.val, z) ∈ (R.atlas.A a).target ∧
        R.atlas.f ((R.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch mr_base)} := by
  intro z hz
  have hcont : ContinuousAt (fun w : ℂ => (R.atlas.A a).symm (t.val, w)) z :=
    ((R.atlas.A a).continuousAt_symm hz.1).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hbranch := (Set.finite_range (b6_branch mr_base)).isClosed.isOpen_compl
  have hn := ((R.atlas.hf.continuous.continuousAt.comp
    (continuous_snd.continuousAt.comp hcont))) (hbranch.mem_nhds hz.2)
  have ht := (continuous_const.prodMk continuous_id).continuousAt
    ((R.atlas.A a).open_target.mem_nhds hz.1)
  apply AnalyticAt.congr (hhol a z hz.1)
  filter_upwards [hn, ht] with w hw hwt
  change R.atlas.f ((R.atlas.A a).symm (t.val, w)).2 ∉
    Set.range (b6_branch mr_base) at hw
  change (t.val, w) ∈ (R.atlas.A a).target at hwt
  have hi := b66k_inverse_slice R t a w hwt
  rw [b66k_freeCoefficient_eq R t h v hv a _ ha hw (by
    rw [hi]
    exact (R.atlas.A a).map_target hwt)]
  rw [hi, (R.atlas.A a).right_inv hwt]

def b66k_averageCoefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) (x : R.C) : ℂ :=
  (Fintype.card b4b_Group : ℂ)⁻¹ * ∑ g : b4b_Group, b66k_freeCoefficient R t v (g • x)

theorem b66k_averageCoefficient_invariant (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (v : b66k_Index R → ℂ → ℂ)
    (g : b4b_Group) (x : R.C) :
    b66k_averageCoefficient R t v (g • x) = b66k_averageCoefficient R t v x := by
  unfold b66k_averageCoefficient
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun k => ?_)
  change b66k_freeCoefficient R t v (k • (g • x)) =
    b66k_freeCoefficient R t v ((k * g) • x)
  rw [mul_smul]

theorem b66k_projection_surjective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Function.Surjective (fun x : R.C => b6a_map mr_base R.atlas.f (t, x)) := by
  obtain ⟨e, he⟩ := b6t_homeomorph mr_base mr_base_mem_chart t.val t.property
  intro y
  obtain ⟨x, hx⟩ := R.atlas.hsurj (e.symm y)
  refine ⟨x, ?_⟩
  change b6t_sphere mr_base t.val (R.atlas.f x) = y
  rw [hx, ← he, e.apply_symm_apply]

theorem b66k_averageCoefficient_fibre (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (v : b66k_Index R → ℂ → ℂ) (x y : R.C)
    (hxy : b6a_map mr_base R.atlas.f (t, x) = b6a_map mr_base R.atlas.f (t, y)) :
    b66k_averageCoefficient R t v x = b66k_averageCoefficient R t v y := by
  obtain ⟨e, he⟩ := b6t_homeomorph mr_base mr_base_mem_chart t.val t.property
  have hf : R.atlas.f x = R.atlas.f y := e.injective (by
    simpa only [he, b6a_map] using hxy)
  obtain ⟨g, hg⟩ := R.atlas.hgal.2 x y hf
  rw [← hg, b66k_averageCoefficient_invariant]

def b66k_descendedCoefficient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) (y : OnePoint ℂ) : ℂ :=
  b66k_averageCoefficient R t v (Function.surjInv (b66k_projection_surjective R t) y)

theorem b66k_descendedCoefficient_apply (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (v : b66k_Index R → ℂ → ℂ) (x : R.C) :
    b66k_descendedCoefficient R t v (b6a_map mr_base R.atlas.f (t, x)) =
      b66k_averageCoefficient R t v x := by
  apply b66k_averageCoefficient_fibre
  exact Function.surjInv_eq (b66k_projection_surjective R t) _

theorem b66k_deckCoordinate_analytic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (g : b4b_Group) (a b : b66k_Index R) :
    AnalyticOnNhd ℂ (b66k_deckCoordinate R t g a b)
      (b66k_refinementDomain R t g a b) := by
  intro z hz
  have hb : b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66k_totalDeck
    rw [← b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hd : ContDiffAt ℂ ω (b66k_deckTransition R g a b) (t.val, z) :=
    (b66k_deckTransition_analytic R g a b _ hz.1 hb).contDiffAt
  apply ((hd.comp z (contDiffAt_const.prodMk contDiffAt_id)).analyticAt).congr
  have hn := (continuous_const.prodMk continuous_id).continuousAt
    ((R.atlas.A a).open_target.mem_nhds hz.1)
  filter_upwards [hn] with w hw
  change b66k_deckTransition R g a b (t.val, w) = b66k_deckCoordinate R t g a b w
  unfold b66k_deckCoordinate b66k_deckTransition b66k_totalDeck
  rw [← b66k_inverse_slice R t a w hw]

theorem b66k_freeCoefficient_branch (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (i : Fin 10) (a : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base (Fin.castAdd 3 i))
    (hx : R.atlas.f x ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source) :
    b66k_freeCoefficient R t v x =
      (R.atlas.n a.2 : ℂ) * (R.atlas.A a (t, x)).2 ^ (R.atlas.n a.2 - 1) *
        v a (R.atlas.A a (t, x)).2 - h i := by
  have hself := (R.atlas.hA (t, x)).1
  have he := congrFun (congrFun (congrFun hv a) (t, x)) x
  have hc := b66k_branch_coordinate_aux R t h i a (t, x) x ha hx hxa hself
  rw [hc.1] at he
  simp only [b66k_boundary,
    ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A (t, x)).source from
      ⟨hxa, hself⟩), hc.2] at he
  unfold b66k_freeCoefficient
  linear_combination he

theorem b66k_action_faithful (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    FaithfulSMul b4b_Group R.C := by
  letI := R.fibreFaithful t
  constructor
  intro g k hgk
  apply eq_of_smul_eq_smul (α := rf8_fibre R.C t)
  intro x
  apply Subtype.ext
  exact Prod.ext rfl (hgk x.val.2)

theorem b66k_mark_stabilizer (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (j : Fin 13) (x : R.C) (hx : R.atlas.f x = b6_branch mr_base j) :
    ∃ k : b4b_Group, k ≠ 1 ∧ k • x = x := by
  obtain ⟨z, hz, hrot⟩ := R.hrot t j
  obtain ⟨e, he⟩ := b6t_homeomorph mr_base mr_base_mem_chart t.val t.property
  have hfz : R.atlas.f z.val.2 = b6_branch mr_base j := by
    apply e.injective
    rw [he, he, b6t_marks mr_base mr_base_mem_chart t.val t.property j]
    change b6t_sphere mr_base t.val (R.atlas.f z.val.2) = _
    simpa only [b63d_projection, b6a_map, z.property] using hz
  obtain ⟨g, hg⟩ := R.atlas.hgal.2 z.val.2 x (hfz.trans hx.symm)
  have hr : b4b_root j ≠ 1 := by
    intro hr
    have ho := b63_root_order j
    rw [hr, orderOf_one] at ho
    split_ifs at ho <;> omega
  refine ⟨g * b4b_root j * g⁻¹, ?_, ?_⟩
  · intro hk
    apply hr
    have := congrArg (fun k : b4b_Group => g⁻¹ * k * g) hk
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, one_mul, mul_one] using this
  · have hzfix : b4b_root j • z.val.2 = z.val.2 := congrArg (fun q => q.val.2) hrot.1
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hzfix]

theorem b66k_mark_order (R : rf8_SharedFamily) (a : b66k_Index R) (j : Fin 13)
    (ha : R.atlas.f a.2 = b6_branch mr_base j) : 1 < R.atlas.n a.2 := by
  have hn := R.atlas.hn a.2
  suffices hne : R.atlas.n a.2 ≠ 1 by omega
  intro hn1
  obtain ⟨k, hk, hkx⟩ := b66k_mark_stabilizer R a.1 j a.2 ha
  letI := b66k_action_faithful R a.1
  have hs : ∀ᶠ y : R.C in 𝓝 a.2, (a.1, y) ∈ (R.atlas.A a).source :=
    (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_source.mem_nhds (R.atlas.hA a).1)
  have hks : ∀ᶠ y : R.C in 𝓝 a.2, (a.1, k • y) ∈ (R.atlas.A a).source := by
    have ht : ContinuousAt (fun y : R.C => (a.1, k • y)) a.2 :=
      (continuous_const.prodMk (R.hC k)).continuousAt
    exact ht (by simpa only [hkx] using
      ((R.atlas.A a).open_source.mem_nhds (R.atlas.hA a).1))
  have hlocal : ∀ᶠ y : R.C in 𝓝 a.2, k • y = y := by
    filter_upwards [hs, hks] with y hy hky
    have hm := (R.atlas.hmark a j ha).2 (a.1, y) hy
    have hmk := (R.atlas.hmark a j ha).2 (a.1, k • y) hky
    have hp : b6a_map mr_base R.atlas.f (a.1, k • y) =
        b6a_map mr_base R.atlas.f (a.1, y) := by
      simp only [b6a_map, R.atlas.hgal.1 k y]
    rw [hm, hmk] at hp
    have hz := b6a_value_injective a.1.val j hp
    rw [hn1, pow_one, pow_one] at hz
    have he : R.atlas.A a (a.1, k • y) = R.atlas.A a (a.1, y) := by
      apply Prod.ext
      · exact (R.atlas.hparam a _ hky).trans (R.atlas.hparam a _ hy).symm
      · exact hz
    exact congrArg Prod.snd ((R.atlas.A a).injOn hky hy he)
  have hall := b4cov_eq_of_eventuallyEq (fun y : R.C => k • y) id
    (R.atlas.hact k) contMDiff_id a.2 hlocal
  apply hk
  apply eq_of_smul_eq_smul (α := R.C)
  intro y
  simpa only [one_smul, id_eq] using congrFun hall y

theorem b66k_freeCoefficient_deck_analytic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ)
    (hz : z ∈ b66k_refinementDomain R t g a b)
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hx : R.atlas.f ((R.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch mr_base)) :
    AnalyticAt ℂ (fun w => b66k_freeCoefficient R t v
      (g • ((R.atlas.A a).symm (t.val, w)).2)) z := by
  have hdom : b66k_deckCoordinate R t g a b z ∈ b66k_domain R t b := by
    have hp : (t.val, b66k_deckCoordinate R t g a b z) =
        R.atlas.A b (t, g • ((R.atlas.A a).symm (t.val, z)).2) :=
      Prod.ext (R.atlas.hparam b _ hz.2).symm rfl
    change (t.val, b66k_deckCoordinate R t g a b z) ∈ (R.atlas.A b).target
    rw [hp]
    exact (R.atlas.A b).map_source hz.2
  apply ((hhol b _ hdom).comp (b66k_deckCoordinate_analytic R t g a b z hz)).congr
  have hcont := ((R.atlas.A a).continuousAt_symm hz.1).comp
    (continuous_const.prodMk continuous_id).continuousAt
  have hbranch := (Set.finite_range (b6_branch mr_base)).isClosed.isOpen_compl
  have hn := (R.atlas.hf.continuous.continuousAt.comp
    (continuous_snd.continuousAt.comp hcont)) (hbranch.mem_nhds hx)
  have hbt : b66k_totalDeck R g ((R.atlas.A a).symm (t.val, z)) ∈
      (R.atlas.A b).source := by
    unfold b66k_totalDeck
    rw [← b66k_inverse_slice R t a z hz.1]
    exact hz.2
  have hnear := (continuous_const.prodMk continuous_id).continuousAt
    (b66k_deck_overlap_nhds R g a b _ hz.1 hbt)
  filter_upwards [hn, hnear] with w hw hwt
  change R.atlas.f ((R.atlas.A a).symm (t.val, w)).2 ∉
    Set.range (b6_branch mr_base) at hw
  change (t.val, w) ∈ (R.atlas.A a).target ∧
    b66k_totalDeck R g ((R.atlas.A a).symm (t.val, w)) ∈ (R.atlas.A b).source at hwt
  have hsource : (t, g • ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A b).source := by
    rw [b66k_totalDeck, ← b66k_inverse_slice R t a w hwt.1] at hwt
    exact hwt.2
  rw [b66k_freeCoefficient_eq R t h v hv b _ hb
    (by simpa only [R.atlas.hgal.1 g _] using hw) hsource]
  rfl

theorem b66k_averageCoefficient_analytic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (a : b66k_Index R) (z : ℂ) (hz : (t.val, z) ∈ (R.atlas.A a).target)
    (hx : R.atlas.f ((R.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch mr_base)) :
    AnalyticAt ℂ (fun w => b66k_averageCoefficient R t v
      ((R.atlas.A a).symm (t.val, w)).2) z := by
  unfold b66k_averageCoefficient
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro g hg
  let x := ((R.atlas.A a).symm (t.val, z)).2
  apply b66k_freeCoefficient_deck_analytic R t h v hv hhol g a (t, g • x) z
  · exact ⟨hz, (R.atlas.hA (t, g • x)).1⟩
  · simpa only [R.atlas.hgal.1 g x] using hx
  · exact hx

theorem b66k_unmarked_of_projection (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (x : R.C)
    (hx : b6a_map mr_base R.atlas.f (t, x) ∉ Set.range (b6_branch t.val)) :
    R.atlas.f x ∉ Set.range (b6_branch mr_base) := by
  rintro ⟨j, hj⟩
  apply hx
  refine ⟨j, ?_⟩
  change b6_branch t.val j = b6t_sphere mr_base t.val (R.atlas.f x)
  rw [← hj, b6t_marks mr_base mr_base_mem_chart t.val t.property j]

theorem b66k_descendedCoefficient_analytic (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (z : ℂ) (hz : (z : OnePoint ℂ) ∉ Set.range (b6_branch t.val)) :
    AnalyticAt ℂ (fun w : ℂ => b66k_descendedCoefficient R t v (w : OnePoint ℂ)) z := by
  obtain ⟨x, hx⟩ := b66k_projection_surjective R t (z : OnePoint ℂ)
  change b6a_map mr_base R.atlas.f (t, x) = (z : OnePoint ℂ) at hx
  have hxf := b66k_unmarked_of_projection R t x (by rwa [hx])
  let a : b66k_Index R := (t, x)
  have hsource := (R.atlas.hA a).1
  have ha : R.atlas.A a (t, x) = (t.val, z) := by
    apply Prod.ext (R.atlas.hparam a _ hsource)
    apply OnePoint.coe_injective
    exact ((R.atlas.hfree a hxf).2 (t, x) hsource).symm.trans hx
  have htarget : (t.val, z) ∈ (R.atlas.A a).target :=
    ha ▸ (R.atlas.A a).map_source hsource
  have hxi : (R.atlas.A a).symm (t.val, z) = (t, x) := by
    rw [← ha, (R.atlas.A a).left_inv hsource]
  apply (b66k_averageCoefficient_analytic R t h v hv hhol a z htarget
    (by simpa only [hxi] using hxf)).congr
  have hn := (continuous_const.prodMk continuous_id).continuousAt
    ((R.atlas.A a).open_target.mem_nhds htarget)
  filter_upwards [hn] with w hw
  change (t.val, w) ∈ (R.atlas.A a).target at hw
  have hi := b66k_inverse_slice R t a w hw
  have hs : (t, ((R.atlas.A a).symm (t.val, w)).2) ∈ (R.atlas.A a).source := by
    rw [hi]
    exact (R.atlas.A a).map_target hw
  have hp : b6a_map mr_base R.atlas.f (t, ((R.atlas.A a).symm (t.val, w)).2) =
      (w : OnePoint ℂ) := by
    rw [(R.atlas.hfree a hxf).2 _ hs, hi, (R.atlas.A a).right_inv hw]
  rw [← hp, b66k_descendedCoefficient_apply]

theorem b66k_freeCoefficient_moving_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (i : Fin 10) (x : R.C) (hx : R.atlas.f x = b6_branch mr_base (Fin.castAdd 3 i)) :
    Tendsto (b66k_freeCoefficient R t v)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 (-h i)) := by
  let a : b66k_Index R := (t, x)
  let w : R.C → ℂ := fun y => (R.atlas.A a (t, y)).2
  have hs := (R.atlas.hA a).1
  have hw0 : w x = 0 := (R.atlas.hmark a (Fin.castAdd 3 i) hx).1
  have hwt : ContinuousAt w x :=
    continuous_snd.continuousAt.comp (((R.atlas.A a).continuousAt hs).comp
      (continuous_const.prodMk continuous_id).continuousAt)
  have htarget : (t.val, 0) ∈ (R.atlas.A a).target := by
    have hp : R.atlas.A a (t, x) = (t.val, 0) :=
      Prod.ext (R.atlas.hparam a _ hs) hw0
    exact hp ▸ (R.atlas.A a).map_source hs
  have hv0 : ContinuousAt (v a) (w x) := by
    rw [hw0]
    exact (hhol a 0 htarget).continuousAt
  have hvw := hv0.comp hwt
  have hn := b66k_mark_order R a (Fin.castAdd 3 i) hx
  have hlim : Tendsto (fun y => (R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
      v a (w y) - h i) (𝓝 x) (𝓝 (-h i)) := by
    have hc : ContinuousAt (fun y => (R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
        v a (w y) - h i) x :=
      ((continuousAt_const.mul (hwt.pow _)).mul hvw).sub continuousAt_const
    simpa only [hw0, zero_pow (by omega : R.atlas.n a.2 - 1 ≠ 0), mul_zero,
      zero_mul, zero_sub] using hc.tendsto
  apply (hlim.mono_left inf_le_left).congr'
  have hsource : ∀ᶠ y : R.C in 𝓝 x, (t, y) ∈ (R.atlas.A a).source :=
    (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_source.mem_nhds hs)
  filter_upwards [hsource.filter_mono inf_le_left, self_mem_nhdsWithin] with y hy hyf
  exact (b66k_freeCoefficient_branch R t h v hv i a y hx hyf hy).symm

theorem b66k_descend_limit {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]
    (P : X → Y) (hP : Continuous P) (hPs : Function.Surjective P)
    (F : X → Z) (D : Y → Z) (B : Set Y) (y₀ : Y) (l : Z)
    (hD : ∀ x, P x ∉ B → D (P x) = F x)
    (hlim : ∀ x, P x = y₀ →
      Tendsto F (𝓝[{x | P x ∉ B}] x) (𝓝 l)) :
    Tendsto D (𝓝[Bᶜ] y₀) (𝓝 l) := by
  rw [Filter.tendsto_def]
  intro V hV
  have hnear : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ P ⁻¹' {y}, P x ∉ B → F x ∈ V := by
    apply hP.isClosedMap.eventually_nhds_fiber
    intro x hx
    exact eventually_nhdsWithin_iff.mp (hlim x hx hV)
  filter_upwards [hnear.filter_mono inf_le_left, self_mem_nhdsWithin] with y hy hyB
  obtain ⟨x, hx⟩ := hPs y
  have hxB : P x ∉ B := hx ▸ hyB
  have he := hy x hx hxB
  rwa [← hD x hxB, hx] at he

theorem b66k_averageCoefficient_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (v : b66k_Index R → ℂ → ℂ) (x : R.C) (l : ℂ)
    (hlim : ∀ y, R.atlas.f y = R.atlas.f x →
      Tendsto (b66k_freeCoefficient R t v)
        (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] y) (𝓝 l)) :
    Tendsto (b66k_averageCoefficient R t v)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 l) := by
  change Tendsto (fun y => (Fintype.card b4b_Group : ℂ)⁻¹ *
    ∑ g : b4b_Group, b66k_freeCoefficient R t v (g • y)) _ _
  have hg (g : b4b_Group) : Tendsto (fun y => b66k_freeCoefficient R t v (g • y))
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 l) := by
    apply (hlim (g • x) (R.atlas.hgal.1 g x)).comp
    apply (R.hC g).continuousAt.continuousWithinAt.tendsto_nhdsWithin
    intro y hy
    simpa only [Set.mem_setOf_eq, R.atlas.hgal.1 g y] using hy
  have hsum := tendsto_finsetSum Finset.univ (fun g _ => hg g)
  have hcard : (Fintype.card b4b_Group : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm := (tendsto_const_nhds (x := (Fintype.card b4b_Group : ℂ)⁻¹)).mul hsum
  simpa only [b66k_averageCoefficient, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul] using hm

theorem b66k_finite_branch_transition (R : rf8_SharedFamily) (j : Fin 13)
    (hj : j.val ≠ 12) (a b : b66k_Index R)
    (ha : R.atlas.f a.2 = b6_branch mr_base j)
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    b66k_transition R a b u = b6a_valueShift u.1 j + u.2 ^ R.atlas.n a.2 := by
  have hm := (R.atlas.hmark a j ha).2 _ ((R.atlas.A a).map_target hu.1)
  have hf := (R.atlas.hfree b hb).2 ((R.atlas.A a).symm u) hu.2
  rw [hf, b6a_value_finite _ j hj, b66k_inverse_parameter R a u hu.1,
    (R.atlas.A a).right_inv hu.1] at hm
  exact OnePoint.coe_injective hm

theorem b66k_stationary_finite_coefficients (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (j : Fin 13)
    (hj : ¬j.val < 10) (hjfin : j.val ≠ 12) (a b : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base j)
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source)
    (hxb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_cocycle R t h a b x = 0 ∧ b66k_vertical R t a b x =
      (R.atlas.n a.2 : ℂ) * (R.atlas.A a (t, x)).2 ^ (R.atlas.n a.2 - 1) := by
  have hu : R.atlas.A a (t, x) ∈
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨(R.atlas.A a).map_source hxa, ?_⟩
    change (R.atlas.A a).symm (R.atlas.A a (t, x)) ∈ (R.atlas.A b).source
    rwa [(R.atlas.A a).left_inv hxa]
  let c : ℂ := if j.val = 11 then 1 else 0
  have he : b66k_transition R a b =ᶠ[𝓝 (R.atlas.A a (t, x))]
      (fun u : (Fin 10 → ℂ) × ℂ => c + u.2 ^ R.atlas.n a.2) := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu]
      with u hu
    simpa only [b6a_valueShift, dif_neg hj] using
      b66k_finite_branch_transition R j hjfin a b ha hb u hu
  have hd := (hasFDerivAt_const c (R.atlas.A a (t, x))).add
    ((ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ).hasFDerivAt.pow (R.atlas.n a.2))
  have hf := (hd.congr_of_eventuallyEq he).fderiv
  constructor
  · simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
      ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨hxa, hxb⟩)]
    rw [hf]
    simp
  · unfold b66k_vertical
    rw [hf]
    simp

theorem b66k_freeCoefficient_stationary_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (j : Fin 13) (hj : ¬j.val < 10) (hjfin : j.val ≠ 12)
    (x : R.C) (hx : R.atlas.f x = b6_branch mr_base j) :
    Tendsto (b66k_freeCoefficient R t v)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 0) := by
  let a : b66k_Index R := (t, x)
  let w : R.C → ℂ := fun y => (R.atlas.A a (t, y)).2
  have hs := (R.atlas.hA a).1
  have hw0 : w x = 0 := (R.atlas.hmark a j hx).1
  have hwt : ContinuousAt w x :=
    continuous_snd.continuousAt.comp (((R.atlas.A a).continuousAt hs).comp
      (continuous_const.prodMk continuous_id).continuousAt)
  have htarget : (t.val, 0) ∈ (R.atlas.A a).target := by
    have hp : R.atlas.A a (t, x) = (t.val, 0) :=
      Prod.ext (R.atlas.hparam a _ hs) hw0
    exact hp ▸ (R.atlas.A a).map_source hs
  have hv0 : ContinuousAt (v a) (w x) := by
    rw [hw0]
    exact (hhol a 0 htarget).continuousAt
  have hn := b66k_mark_order R a j hx
  have hc : ContinuousAt (fun y => (R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
      v a (w y)) x := (continuousAt_const.mul (hwt.pow _)).mul (hv0.comp hwt)
  have hlim : Tendsto (fun y => (R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
      v a (w y)) (𝓝 x) (𝓝 0) := by
    simpa only [hw0, zero_pow (by omega : R.atlas.n a.2 - 1 ≠ 0), mul_zero,
      zero_mul] using hc.tendsto
  apply (hlim.mono_left inf_le_left).congr'
  have hsource : ∀ᶠ y : R.C in 𝓝 x, (t, y) ∈ (R.atlas.A a).source :=
    (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_source.mem_nhds hs)
  filter_upwards [hsource.filter_mono inf_le_left, self_mem_nhdsWithin] with y hy hyf
  have hself := (R.atlas.hA (t, y)).1
  have he := congrFun (congrFun (congrFun hv a) (t, y)) y
  have hcoeff := b66k_stationary_finite_coefficients R t h j hj hjfin a (t, y) y hx hyf hy hself
  rw [hcoeff.1] at he
  simp only [b66k_boundary, ite_eq_left (show
    (t, y) ∈ (R.atlas.A a).source ∩ (R.atlas.A (t, y)).source from ⟨hy, hself⟩),
    hcoeff.2] at he
  exact sub_eq_zero.mp he.symm

theorem b66k_projection_mark_iff (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x : R.C) (j : Fin 13) :
    b6a_map mr_base R.atlas.f (t, x) = b6_branch t.val j ↔
      R.atlas.f x = b6_branch mr_base j := by
  obtain ⟨e, he⟩ := b6t_homeomorph mr_base mr_base_mem_chart t.val t.property
  have hj := b6t_marks mr_base mr_base_mem_chart t.val t.property j
  constructor
  · intro hx
    apply e.injective
    simpa only [he, hj, b6a_map] using hx
  · intro hx
    simpa only [b6a_map, hx] using hj

def b66k_branchVelocity (h : Fin 10 → ℂ) (j : Fin 13) : ℂ :=
  if hj : j.val < 10 then h ⟨j.val, hj⟩ else 0

theorem b66k_freeCoefficient_finite_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (j : Fin 13) (hjfin : j.val ≠ 12) (x : R.C) (hx : R.atlas.f x = b6_branch mr_base j) :
    Tendsto (b66k_freeCoefficient R t v)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x)
      (𝓝 (-b66k_branchVelocity h j)) := by
  by_cases hj : j.val < 10
  · let i : Fin 10 := ⟨j.val, hj⟩
    have he : Fin.castAdd 3 i = j := Fin.ext rfl
    have hl := b66k_freeCoefficient_moving_limit R t h v hv hhol i x (by rwa [he])
    simpa only [b66k_branchVelocity, dite_eq_left hj] using hl
  · simpa only [b66k_branchVelocity, dite_eq_right hj, neg_zero] using
      b66k_freeCoefficient_stationary_limit R t h v hv hhol j hj hjfin x hx

theorem b66k_projection_continuous (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Continuous (fun x : R.C => b6a_map mr_base R.atlas.f (t, x)) := by
  have hp := b6a_map_contMDiff_of_local_formulas mr_base R.C R.atlas.f R.atlas.n
    R.atlas.A R.atlas.hA R.atlas.hparam (fun q hq => (R.atlas.hfree q hq).2)
    (fun q j hj => (R.atlas.hmark q j hj).2)
  exact hp.continuous.comp (continuous_const.prodMk continuous_id)

theorem b66k_descendedCoefficient_finite_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (j : Fin 13) (hj : j.val ≠ 12) :
    Tendsto (b66k_descendedCoefficient R t v)
      (𝓝[(Set.range (b6_branch t.val))ᶜ] (b6_branch t.val j))
      (𝓝 (-b66k_branchVelocity h j)) := by
  apply b66k_descend_limit (fun x : R.C => b6a_map mr_base R.atlas.f (t, x))
    (b66k_projection_continuous R t) (b66k_projection_surjective R t)
    (b66k_averageCoefficient R t v) (b66k_descendedCoefficient R t v)
    (Set.range (b6_branch t.val)) (b6_branch t.val j) (-b66k_branchVelocity h j)
  · intro x hx
    exact b66k_descendedCoefficient_apply R t v x
  · intro x hx
    have hfx := (b66k_projection_mark_iff R t x j).mp hx
    have hl := b66k_averageCoefficient_limit R t v x (-b66k_branchVelocity h j)
      (fun y hy => b66k_freeCoefficient_finite_limit R t h v hv hhol j hj y (hy.trans hfx))
    apply hl.mono_left
    apply nhdsWithin_mono
    intro y hy
    exact b66k_unmarked_of_projection R t y hy

theorem b66k_finite_compl_nhdsWithin {X : Type*} [TopologicalSpace X] [T1Space X]
    (B : Set X) (hB : B.Finite) (x : X) (hx : x ∈ B) :
    𝓝[Bᶜ] x = 𝓝[≠] x := by
  apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
  have hn := (hB.sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds
    (show x ∈ (B \ {x})ᶜ by simp)
  filter_upwards [hn] with y hy
  apply propext
  change (y ∉ B ↔ y ≠ x)
  constructor
  · intro hyB he
    exact hyB (he ▸ hx)
  · intro hyx hyB
    exact hy ⟨hyB, hyx⟩

theorem b66k_extend_finite (B : Set ℂ) (hB : B.Finite) (F L : ℂ → ℂ)
    (hF : ∀ z ∉ B, DifferentiableAt ℂ F z)
    (hlim : ∀ z ∈ B, Tendsto F (𝓝[≠] z) (𝓝 (L z))) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ z ∉ B, f z = F z) ∧ (∀ z ∈ B, f z = L z) := by
  classical
  let f : ℂ → ℂ := fun z => if z ∈ B then L z else F z
  have hoff (z : ℂ) (hz : z ∉ B) : DifferentiableAt ℂ f z := by
    apply (hF z hz).congr_of_eventuallyEq
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hz] with w hw
    exact if_neg hw
  refine ⟨f, ?_, fun z hz => if_neg hz, fun z hz => if_pos hz⟩
  intro z
  by_cases hz : z ∈ B
  · have hnear : ∀ᶠ w in 𝓝[≠] z, w ∉ B := by
      have hn : ∀ᶠ w in 𝓝 z, w ∈ (B \ {z})ᶜ :=
        (hB.sdiff (t := {z})).isClosed.isOpen_compl.mem_nhds
        (show z ∈ (B \ {z})ᶜ by simp)
      filter_upwards [hn.filter_mono inf_le_left, self_mem_nhdsWithin] with w hw hwz
      intro hwB
      exact hw ⟨hwB, hwz⟩
    have hc : ContinuousAt f z := by
      rw [continuousAt_iff_punctured_nhds]
      change Tendsto f _ (𝓝 (if z ∈ B then L z else F z))
      rw [if_pos hz]
      apply (hlim z hz).congr'
      filter_upwards [hnear] with w hw
      exact (if_neg hw).symm
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (hnear.mono fun w hw => hoff w hw) hc).differentiableAt
  · exact hoff z hz

theorem b66k_branch_finite_value (t : Fin 10 → ℂ) (j : Fin 13) (hj : j.val ≠ 12) :
    b6_branch t j = (b6a_valueShift t j : OnePoint ℂ) := by
  fin_cases j <;> first | rfl | exact (hj rfl).elim

theorem b66k_descendedCoefficient_complex_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (j : Fin 13) (hj : j.val ≠ 12) :
    Tendsto (fun z : ℂ => b66k_descendedCoefficient R t v (z : OnePoint ℂ))
      (𝓝[≠] (b6a_valueShift t.val j)) (𝓝 (-b66k_branchVelocity h j)) := by
  have hl := b66k_descendedCoefficient_finite_limit R t h v hv hhol j hj
  rw [b66k_finite_compl_nhdsWithin _ (Set.finite_range _) _ ⟨j, rfl⟩,
    b66k_branch_finite_value t.val j hj] at hl
  apply hl.comp
  apply OnePoint.continuous_coe.continuousAt.continuousWithinAt.tendsto_nhdsWithin
  intro z hz
  exact fun he => hz (OnePoint.coe_injective he)

theorem b66k_entire_coefficient (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ z : ℂ, (z : OnePoint ℂ) ∉ Set.range (b6_branch t.val) →
        f z = b66k_descendedCoefficient R t v (z : OnePoint ℂ)) ∧
      ∀ (j : Fin 13), j.val ≠ 12 → f (b6a_valueShift t.val j) = -b66k_branchVelocity h j := by
  let B : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' Set.range (b6_branch t.val)
  let F : ℂ → ℂ := fun z => b66k_descendedCoefficient R t v (z : OnePoint ℂ)
  have hB : B.Finite := (Set.finite_range (b6_branch t.val)).preimage OnePoint.coe_injective.injOn
  have hlim (z : ℂ) (hz : z ∈ B) :
      Tendsto F (𝓝[≠] z) (𝓝 (limUnder (𝓝[≠] z) F)) := by
    obtain ⟨j, hj⟩ := hz
    have hjfin : j.val ≠ 12 := by
      intro hje
      have hje' : j = 12 := Fin.ext hje
      rw [hje'] at hj
      exact OnePoint.coe_ne_infty z hj.symm
    have hc : b6a_valueShift t.val j = z :=
      OnePoint.coe_injective ((b66k_branch_finite_value t.val j hjfin).symm.trans hj)
    have hl := b66k_descendedCoefficient_complex_limit R t h v hv hhol j hjfin
    rw [hc] at hl
    change Tendsto F (𝓝[≠] z) (𝓝 (-b66k_branchVelocity h j)) at hl
    rw [hl.limUnder_eq]
    exact hl
  obtain ⟨f, hf, hoff, hon⟩ := b66k_extend_finite B hB F
    (fun z => limUnder (𝓝[≠] z) F)
    (fun z hz => (b66k_descendedCoefficient_analytic R t h v hv hhol z hz).differentiableAt) hlim
  refine ⟨f, hf, hoff, ?_⟩
  intro j hj
  have hm : b6a_valueShift t.val j ∈ B := ⟨j, b66k_branch_finite_value t.val j hj⟩
  rw [hon _ hm]
  exact (b66k_descendedCoefficient_complex_limit R t h v hv hhol j hj).limUnder_eq

theorem b66k_infinite_branch_transition (R : rf8_SharedFamily) (a b : b66k_Index R)
    (ha : R.atlas.f a.2 = b6_branch mr_base 12)
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (u : (Fin 10 → ℂ) × ℂ)
    (hu : u ∈ ((R.atlas.A a).symm.trans (R.atlas.A b)).source) :
    u.2 ^ R.atlas.n a.2 ≠ 0 ∧ b66k_transition R a b u = (u.2 ^ R.atlas.n a.2)⁻¹ := by
  have hm := (R.atlas.hmark a 12 ha).2 _ ((R.atlas.A a).map_target hu.1)
  have hf := (R.atlas.hfree b hb).2 ((R.atlas.A a).symm u) hu.2
  rw [hf, b6a_value_infinite _ 12 rfl, (R.atlas.A a).right_inv hu.1] at hm
  have hn : u.2 ^ R.atlas.n a.2 ≠ 0 := by
    intro hn
    rw [hn, b4cov_sphInv_zero] at hm
    exact OnePoint.coe_ne_infty _ hm
  exact ⟨hn, OnePoint.coe_injective (hm.trans (b4cov_sphInv_coe hn))⟩

theorem b66k_freeCoefficient_infinite (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (a : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base 12)
    (hx : R.atlas.f x ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source) :
    (b4cov_chart0 (b6a_map mr_base R.atlas.f (t, x)))⁻¹ ^ 2 * b66k_freeCoefficient R t v x =
      -(R.atlas.n a.2 : ℂ) * (R.atlas.A a (t, x)).2 ^ (R.atlas.n a.2 - 1) *
        v a (R.atlas.A a (t, x)).2 := by
  let b : b66k_Index R := (t, x)
  have hxb := (R.atlas.hA b).1
  have hu : R.atlas.A a (t, x) ∈
      ((R.atlas.A a).symm.trans (R.atlas.A b)).source := by
    refine ⟨(R.atlas.A a).map_source hxa, ?_⟩
    change (R.atlas.A a).symm (R.atlas.A a (t, x)) ∈ (R.atlas.A b).source
    rwa [(R.atlas.A a).left_inv hxa]
  have htrans := b66k_infinite_branch_transition R a b ha hx _ hu
  have heq : b66k_transition R a b =ᶠ[𝓝 (R.atlas.A a (t, x))]
      (fun u : (Fin 10 → ℂ) × ℂ => (u.2 ^ R.atlas.n a.2)⁻¹) := by
    filter_upwards [((R.atlas.A a).symm.trans (R.atlas.A b)).open_source.mem_nhds hu]
      with u hu
    exact (b66k_infinite_branch_transition R a b ha hx u hu).2
  have hpow := ((ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ).hasFDerivAt
    (x := R.atlas.A a (t, x))).pow (R.atlas.n a.2)
  have hd := (hasDerivAt_inv htrans.1).hasFDerivAt.comp (R.atlas.A a (t, x)) hpow
  have hf := (hd.congr_of_eventuallyEq heq).fderiv
  have hzero : b66k_cocycle R t h a b x = 0 := by
    simp only [b66k_cocycle, LinearMap.coe_mk, AddHom.coe_mk,
      ite_eq_left (show (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨hxa, hxb⟩)]
    rw [hf]
    simp
  have hbound := congrFun (congrFun (congrFun hv a) b) x
  rw [hzero] at hbound
  simp only [b66k_boundary, ite_eq_left (show
    (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source from ⟨hxa, hxb⟩)] at hbound
  have hraw : b66k_freeCoefficient R t v x =
      b66k_vertical R t a b x * v a (R.atlas.A a (t, x)).2 := (sub_eq_zero.mp hbound.symm).symm
  have hp : b4cov_chart0 (b6a_map mr_base R.atlas.f (t, x)) =
      ((R.atlas.A a (t, x)).2 ^ R.atlas.n a.2)⁻¹ := by
    rw [(R.atlas.hfree b hx).2 _ hxb, b4cov_chart0_coe]
    simpa only [b66k_transition, (R.atlas.A a).left_inv hxa] using htrans.2
  rw [hp, hraw, b66k_vertical, hf]
  simp
  field_simp [htrans.1]
  <;> ring

theorem b66k_freeCoefficient_infinite_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (x : R.C) (hx : R.atlas.f x = b6_branch mr_base 12) :
    Tendsto (fun y => (b4cov_chart0 (b6a_map mr_base R.atlas.f (t, y)))⁻¹ ^ 2 *
      b66k_freeCoefficient R t v y)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 0) := by
  let a : b66k_Index R := (t, x)
  let w : R.C → ℂ := fun y => (R.atlas.A a (t, y)).2
  have hs := (R.atlas.hA a).1
  have hw0 : w x = 0 := (R.atlas.hmark a 12 hx).1
  have hwt : ContinuousAt w x :=
    continuous_snd.continuousAt.comp (((R.atlas.A a).continuousAt hs).comp
      (continuous_const.prodMk continuous_id).continuousAt)
  have htarget : (t.val, 0) ∈ (R.atlas.A a).target := by
    have hp : R.atlas.A a (t, x) = (t.val, 0) :=
      Prod.ext (R.atlas.hparam a _ hs) hw0
    exact hp ▸ (R.atlas.A a).map_source hs
  have hv0 : ContinuousAt (v a) (w x) := by
    rw [hw0]
    exact (hhol a 0 htarget).continuousAt
  have hn := b66k_mark_order R a 12 hx
  have hc : ContinuousAt (fun y => -(R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
      v a (w y)) x := (continuousAt_const.mul (hwt.pow _)).mul (hv0.comp hwt)
  have hlim : Tendsto (fun y => -(R.atlas.n a.2 : ℂ) * w y ^ (R.atlas.n a.2 - 1) *
      v a (w y)) (𝓝 x) (𝓝 0) := by
    simpa only [hw0, zero_pow (by omega : R.atlas.n a.2 - 1 ≠ 0), mul_zero,
      zero_mul] using hc.tendsto
  apply (hlim.mono_left inf_le_left).congr'
  have hsource : ∀ᶠ y : R.C in 𝓝 x, (t, y) ∈ (R.atlas.A a).source :=
    (continuous_const.prodMk continuous_id).continuousAt
      ((R.atlas.A a).open_source.mem_nhds hs)
  filter_upwards [hsource.filter_mono inf_le_left, self_mem_nhdsWithin] with y hy hyf
  exact (b66k_freeCoefficient_infinite R t h v hv a y hx hyf hy).symm

theorem b66k_averageCoefficient_infinite_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a))
    (x : R.C) (hx : R.atlas.f x = b6_branch mr_base 12) :
    Tendsto (fun y => (b4cov_chart0 (b6a_map mr_base R.atlas.f (t, y)))⁻¹ ^ 2 *
      b66k_averageCoefficient R t v y)
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 0) := by
  have hg (g : b4b_Group) : Tendsto
      (fun y => (b4cov_chart0 (b6a_map mr_base R.atlas.f (t, y)))⁻¹ ^ 2 *
        b66k_freeCoefficient R t v (g • y))
      (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x) (𝓝 0) := by
    have hm : Tendsto (fun y : R.C => g • y)
        (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] x)
        (𝓝[{y | R.atlas.f y ∉ Set.range (b6_branch mr_base)}] (g • x)) := by
      apply (R.hC g).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      intro y hy
      simpa only [Set.mem_setOf_eq, R.atlas.hgal.1 g y] using hy
    have hl := (b66k_freeCoefficient_infinite_limit R t h v hv hhol (g • x)
      ((R.atlas.hgal.1 g x).trans hx)).comp hm
    simpa only [Function.comp_def, b6a_map, R.atlas.hgal.1] using hl
  have hsum := tendsto_finsetSum Finset.univ (fun g _ => hg g)
  have hm := (tendsto_const_nhds (x := (Fintype.card b4b_Group : ℂ)⁻¹)).mul hsum
  simp only [Finset.sum_const_zero, mul_zero] at hm
  convert hm using 1
  funext y
  simp only [b66k_averageCoefficient, Finset.mul_sum]
  ring

theorem b66k_descendedCoefficient_infinite_limit (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) :
    Tendsto (fun z : ℂ => z⁻¹ ^ 2 * b66k_descendedCoefficient R t v (z : OnePoint ℂ))
      (cocompact ℂ) (𝓝 0) := by
  have hl : Tendsto (fun y : OnePoint ℂ => (b4cov_chart0 y)⁻¹ ^ 2 *
      b66k_descendedCoefficient R t v y)
      (𝓝[(Set.range (b6_branch t.val))ᶜ] OnePoint.infty) (𝓝 0) := by
    apply b66k_descend_limit (fun x : R.C => b6a_map mr_base R.atlas.f (t, x))
      (b66k_projection_continuous R t) (b66k_projection_surjective R t)
      (fun x => (b4cov_chart0 (b6a_map mr_base R.atlas.f (t, x)))⁻¹ ^ 2 *
        b66k_averageCoefficient R t v x)
      (fun y => (b4cov_chart0 y)⁻¹ ^ 2 * b66k_descendedCoefficient R t v y)
      (Set.range (b6_branch t.val)) OnePoint.infty 0
    · intro x hx
      rw [b66k_descendedCoefficient_apply]
    · intro x hx
      have hfx := (b66k_projection_mark_iff R t x 12).mp hx
      have hm := b66k_averageCoefficient_infinite_limit R t h v hv hhol x hfx
      apply hm.mono_left
      apply nhdsWithin_mono
      intro y hy
      exact b66k_unmarked_of_projection R t y hy
  rw [b66k_finite_compl_nhdsWithin (Set.range (b6_branch t.val)) (Set.finite_range _)
    (OnePoint.infty : OnePoint ℂ) ⟨12, rfl⟩] at hl
  have hc : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝[≠] OnePoint.infty) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun z => OnePoint.coe_ne_infty z)⟩
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  simpa only [Function.comp_def, b4cov_chart0_coe] using hl.comp hc

theorem b66k_sphere_normalization (R : rf8_SharedFamily)
    (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ) (v : b66k_Index R → ℂ → ℂ)
    (hv : b66k_cocycle R t h = b66k_boundary R t v)
    (hhol : ∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ f 0 = 0 ∧ f 1 = 0 ∧
      Tendsto (fun z => z⁻¹ ^ 2 * f z) (cocompact ℂ) (𝓝 0) ∧
      ∀ i : Fin 10, f (t.val i) = -h i := by
  obtain ⟨f, hf, hregular, hvalues⟩ := b66k_entire_coefficient R t h v hv hhol
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · simpa [b6a_valueShift, b66k_branchVelocity] using hvalues 10 (by decide)
  · simpa [b6a_valueShift, b66k_branchVelocity] using hvalues 11 (by decide)
  · apply (b66k_descendedCoefficient_infinite_limit R t h v hv hhol).congr'
    have hB : (((↑) : ℂ → OnePoint ℂ) ⁻¹' Set.range (b6_branch t.val)).Finite :=
      (Set.finite_range (b6_branch t.val)).preimage OnePoint.coe_injective.injOn
    filter_upwards [hB.isCompact.compl_mem_cocompact] with z hz
    rw [hregular z hz]
  · intro i
    have hj : (Fin.castAdd 3 i).val ≠ 12 := by
      change i.val ≠ 12
      omega
    simpa [b6a_valueShift, b66k_branchVelocity] using hvalues (Fin.castAdd 3 i) hj


theorem b66k_injective_aux (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ K : (Fin 10 → ℂ) →ₗ[ℂ] b66k_cechH1 R t,
      (b66k_cechH1 R t).subtype.comp K = b66k_kodairaSpencer R t ∧
        Function.Injective K := by
  refine ⟨b66k_factor R t, b66k_factor_comp R t, ?_⟩
  apply (injective_iff_map_eq_zero (b66k_factor R t)).mpr
  intro h hh
  have hk : b66k_kodairaSpencer R t h = 0 := congrArg Subtype.val hh
  have hm : b66k_cocycle R t h ∈ b66k_boundaries R t :=
    (Submodule.Quotient.mk_eq_zero (b66k_boundaries R t)).mp hk
  obtain ⟨v, hhol, hv⟩ := b66k_boundary_representation R t _ hm
  obtain ⟨f, hf, h0, h1, hinfty, hvalues⟩ := b66k_sphere_normalization R t h v hv hhol
  have he := b66k_sphere_coefficient_zero f hf h0 h1 hinfty
  funext i
  have hi := hvalues i
  rw [he] at hi
  simpa only [Pi.zero_apply, zero_eq_neg] using hi


end HodgeLean.Foundations.Program
