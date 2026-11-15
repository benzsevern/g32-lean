import HodgeLean.Foundations.Program.RelativeFrameFamilySphereTent

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_moving_root_of_chart {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ))
    (u : OpenPartialHomeomorph C ℂ)
    (huS : u.source = rf7_component P.f (b i) (3 * b6t_radius b) x)
    (huT : u.target = {w : ℂ | ‖w‖ ^ P.n x < 3 * b6t_radius b})
    (hux : u x = 0)
    (huP : ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
      P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ)) :
    ∃ w : b6t_polydisc b × C → ℂ,
      ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w
        (univ ×ˢ rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
      ∀ t : b6t_polydisc b,
        (∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
          b6a_map b P.f (t, y) = ((t.val i + w (t, y) ^ P.n x : ℂ) : OnePoint ℂ)) ∧
        InjOn (fun y ↦ w (t, y)) (rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
        (fun y ↦ w (t, y)) '' rf7_component P.f (b i) (3 * b6t_radius b) x =
          {v : ℂ | ‖v ^ P.n x + (t.val i - b i)‖ < 3 * b6t_radius b} ∧
        (fun y ↦ w (t, y)) '' rf7_inner b P.f i x =
          rf4_innerDisc (P.n x) (rf7_radius b) (t.val i - b i) ∧
        w (t, x) = 0 ∧
        ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x, ∀ z : ℂ,
          P.f y = (z : OnePoint ℂ) → b6t_radius b < dist z (b i) →
            w (t, y) = rf4_rootMap (P.n x) (t.val i - b i)
              (w (⟨b, (b6t_polydisc_neighbourhood b P.hb).1⟩, y)) := by
  classical
  let n := P.n x
  let r := b6t_radius b
  let Δ := rf7_component P.f (b i) (3 * r) x
  have hn : 0 < n := P.hn x
  have hr : 0 < r := (b6t_discs b P.hb).1
  let ε : b6t_polydisc b → ℂ := fun t ↦ t.val i - b i
  have hε (t : b6t_polydisc b) : ‖ε t‖ < r := by
    simpa only [ε, Metric.mem_ball, dist_eq_norm] using t.2 i
  let δ : b6t_polydisc b → {ε : ℂ // ‖ε‖ < r} := fun t ↦ ⟨ε t, hε t⟩
  have hδ : Continuous δ := (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).subtype_mk _
  let w : b6t_polydisc b × C → ℂ := fun q ↦ rf7_tentRoot n r (ε q.1) (u q.2)
  have hxΔ : x ∈ Δ := mem_connectedComponentIn (by
    change P.f x ∈ rf7_sphereBall (b i) (3 * r)
    rw [hx]
    exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩)
  have huMem (y : C) (hy : y ∈ Δ) : y ∈ u.source := by
    rw [huS]
    exact hy
  have huBound (y : C) (hy : y ∈ Δ) : ‖u y‖ ^ n < 3 * r := by
    have hh := u.map_source (huMem y hy)
    rw [huT] at hh
    exact hh
  have hmodel (t : b6t_polydisc b) (y : C) (hy : y ∈ Δ) :
      b6a_map b P.f (t, y) = ((t.val i + w (t, y) ^ n : ℂ) : OnePoint ℂ) := by
    change b6t_sphere b t.val (P.f y) = _
    rw [huP y hy]
    change ((b6t_plane b t.val (b i + u y ^ n) : ℂ) : OnePoint ℂ) = _
    apply congrArg (fun z : ℂ ↦ (z : OnePoint ℂ))
    rw [show w (t, y) = rf7_tentRoot n r (ε t) (u y) from rfl, rf7_tentRoot_pow n hn]
    have hh := rf7_tent_plane_power b P.hb t.val i n (u y) (huBound y hy)
    dsimp only [ε, r] at hh ⊢
    linear_combination hh
  have hwc : ContinuousOn w (univ ×ˢ Δ) := by
    have harg : ContinuousOn (fun q : b6t_polydisc b × C ↦ (δ q.1, u q.2)) (univ ×ˢ Δ) :=
      ((hδ.comp continuous_fst).continuousOn).prodMk
        (u.continuousOn.comp continuous_snd.continuousOn (fun q hq ↦ huMem q.2 hq.2))
    exact (rf7_tentRoot_continuous n hn r hr).comp_continuousOn harg
  have hwa : ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω w (univ ×ˢ Δ) := by
    apply rf7_total_root_analytic P Δ (rf7_component_open P i x) w hwc (Fin.castAdd 3 i) n hn
    rintro ⟨t, y⟩ ⟨_, hy⟩
    simpa [b6a_value] using hmodel t y hy
  have hRadius (t : b6t_polydisc b) (y : C) (hy : y ∈ Δ) (s : ℝ)
      (hs : r < s) (hs' : s ≤ 3 * r) :
      ‖w (t, y) ^ n + ε t‖ < s ↔ P.f y ∈ rf7_sphereBall (b i) s := by
    have hh : b6a_map b P.f (t, y) ∈ rf7_sphereBall (b i) s ↔ P.f y ∈ rf7_sphereBall (b i) s :=
      Iff.of_eq (congrArg (fun S : Set (OnePoint ℂ) ↦ P.f y ∈ S)
        (rf7_sphere_tent_preimage b P.hb t.val t.2 i s hs hs'))
    rw [hmodel t y hy] at hh
    have hcoe (z : ℂ) : (z : OnePoint ℂ) ∈ rf7_sphereBall (b i) s ↔ dist z (b i) < s := by
      constructor
      · rintro ⟨a, ha, haz⟩
        exact OnePoint.coe_injective haz ▸ ha
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hcoe, dist_eq_norm] at hh
    have heq : t.val i + w (t, y) ^ n - b i = w (t, y) ^ n + ε t := by dsimp [ε]; ring
    rwa [heq] at hh
  have hwx (t : b6t_polydisc b) : w (t, x) = 0 := by simp [w, hux, rf7_tentRoot]
  have hwi (t : b6t_polydisc b) : InjOn (fun y ↦ w (t, y)) Δ := by
    intro y hy z hz heq
    change w (t, y) = w (t, z) at heq
    obtain ⟨E, hE⟩ := b6t_homeomorph b P.hb t.val t.2
    have hfy : P.f y = P.f z := E.injective (by
      rw [hE, hE]
      change b6a_map b P.f (t, y) = b6a_map b P.f (t, z)
      rw [hmodel t y hy, hmodel t z hz, heq])
    rw [huP y hy, huP z hz] at hfy
    have hp : u y ^ n = u z ^ n := add_left_cancel (OnePoint.coe_injective hfy)
    have hU := rf7_tentRoot_injective_on_power_fibre n hn r hr (ε t) (hε t) (u y) (u z) hp heq
    exact u.injOn (huMem y hy) (huMem z hz) hU
  have hwimage (t : b6t_polydisc b) : (fun y ↦ w (t, y)) '' Δ =
      {v : ℂ | ‖v ^ n + ε t‖ < 3 * r} := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyBall : P.f y ∈ rf7_sphereBall (b i) (3 * r) :=
        connectedComponentIn_subset (P.f ⁻¹' rf7_sphereBall (b i) (3 * r)) x hy
      exact (hRadius t y hy (3 * r) (by linarith) le_rfl).mpr hyBall
    · intro hv
      by_cases hv0 : v = 0
      · subst v
        exact ⟨x, hxΔ, hwx t⟩
      · have hz : t.val i + v ^ n ∈ Metric.ball (b i) (3 * r) := by
          rw [Metric.mem_ball, dist_eq_norm]
          have heq : t.val i + v ^ n - b i = v ^ n + ε t := by dsimp [ε]; ring
          rw [heq]
          exact hv
        obtain ⟨y, hy, hfy⟩ := rf7_transport_component_surj P i x hx t (t.val i + v ^ n) hz
        have hp : w (t, y) ^ n = v ^ n :=
          add_left_cancel (OnePoint.coe_injective ((hmodel t y hy).symm.trans hfy))
        have hw0 : w (t, y) ≠ 0 := by
          intro h
          rw [h, zero_pow hn.ne'] at hp
          exact hv0 ((pow_eq_zero_iff hn.ne').mp hp.symm)
        let ζ : ℂ := v / w (t, y)
        have hζ : ζ ^ n = 1 := by
          change (v / w (t, y)) ^ n = 1
          rw [div_pow, hp, div_self (pow_ne_zero n hv0)]
        let u' := ζ * u y
        have hup : u' ^ n = u y ^ n := by change (ζ * u y) ^ n = u y ^ n; rw [mul_pow, hζ, one_mul]
        have hu'mem : u' ∈ u.target := by
          rw [huT]
          change ‖u'‖ ^ n < 3 * r
          rw [← norm_pow, hup, norm_pow]
          exact huBound y hy
        let y' := u.symm u'
        have hy' : y' ∈ Δ := by
          have hh := u.map_target hu'mem
          rw [huS] at hh
          exact hh
        refine ⟨y', hy', ?_⟩
        change rf7_tentRoot n r (ε t) (u (u.symm u')) = v
        rw [u.right_inv hu'mem, show u' = ζ * u y from rfl, rf7_tentRoot_mul n r (ε t) (u y) ζ hζ]
        change ζ * w (t, y) = v
        exact div_mul_cancel₀ v hw0
  have hρ : r < rf7_radius b ∧ 2 * rf7_radius b < 3 * r := by
    unfold rf7_radius
    constructor <;> dsimp [r] at * <;> linarith
  refine ⟨w, hwa, fun t ↦ ⟨hmodel t, hwi t, hwimage t, ?_, hwx t, ?_⟩⟩
  · ext v
    constructor
    · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
      exact (hRadius t y hy (2 * rf7_radius b) (by linarith [hr]) hρ.2.le).mpr hys
    · intro hv
      have hv' : v ∈ {v : ℂ | ‖v ^ n + ε t‖ < 3 * r} := lt_trans hv hρ.2
      obtain ⟨y, hy, hwy⟩ := (hwimage t).symm ▸ hv'
      change w (t, y) = v at hwy
      refine ⟨y, ⟨hy, ?_⟩, hwy⟩
      apply (hRadius t y hy (2 * rf7_radius b) (by linarith [hr]) hρ.2.le).mp
      rw [hwy]
      exact hv
  · intro y hy z hfy hdist
    have hp : b i + u y ^ n = z := OnePoint.coe_injective ((huP y hy).symm.trans hfy)
    have hN : ‖u y‖ ^ n = dist z (b i) := by rw [← hp, dist_eq_norm, add_sub_cancel_left, norm_pow]
    have hcollar := rf7_tentRoot_collar n r hr (ε t) (u y) (by rw [hN]; exact hdist.le)
    change rf7_tentRoot n r (ε t) (u y) = _
    rw [hcollar]
    congr 1
    simp only [w, ε, sub_self, rf7_tentRoot, mul_zero, zero_div, sub_zero, Complex.one_cpow, mul_one]

end HodgeLean.Foundations.Program
