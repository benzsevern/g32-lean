import HodgeLean.Foundations.Program.RelativeFrameFamilyDefs
import HodgeLean.Foundations.Program.RelativeFrameFamilyCovering

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem rf7_radius_separation (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    (∀ i j : Fin 10, i ≠ j → 8 * b6t_radius b < dist (b i) (b j)) ∧
      ∀ i : Fin 10, 4 * b6t_radius b < ‖b i‖ ∧ 4 * b6t_radius b < ‖b i - 1‖ := by
  classical
  let a : Fin 10 → ℝ := fun i ↦ ‖b i‖⁻¹ + ‖b i - 1‖⁻¹ +
    ∑ j : Fin 10, if i = j then 0 else (dist (b i) (b j))⁻¹
  have ha (i) : 0 ≤ a i := by dsimp [a]; positivity
  have hs : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ ↦ ha i
  have hbound (x m : ℝ) (hx : 0 < x) (hm : 0 < m)
      (h : m * x⁻¹ ≤ ∑ i, a i) : 4 * m * b6t_radius b < x := by
    have hd : 0 < 4 * (1 + ∑ i, a i) := by positivity
    have hh : 4 * m < x * (4 * (1 + ∑ i, a i)) := by
      have hh := (mul_le_mul_of_nonneg_left h hx.le)
      rw [mul_left_comm, mul_inv_cancel₀ hx.ne', mul_one] at hh
      nlinarith
    change 4 * m * (4 * (1 + ∑ i, a i))⁻¹ < x
    exact (mul_inv_lt_iff₀ hd).2 hh
  have hc := (b6_chart_coordinates b).mp hb
  have hpair (i j : Fin 10) (hij : i ≠ j) : (dist (b i) (b j))⁻¹ ≤ a i := by
    have hh : (dist (b i) (b j))⁻¹ ≤
        ∑ l : Fin 10, if i = l then 0 else (dist (b i) (b l))⁻¹ := by
      simpa [hij] using (Finset.single_le_sum (s := Finset.univ)
        (f := fun l : Fin 10 ↦ if i = l then (0 : ℝ) else (dist (b i) (b l))⁻¹)
        (fun l _ ↦ by split <;> positivity) (Finset.mem_univ j))
    dsimp [a]
    have h₁ : 0 ≤ ‖b i‖⁻¹ := by positivity
    have h₂ : 0 ≤ ‖b i - 1‖⁻¹ := by positivity
    linarith
  constructor
  · intro i j hij
    have hh : a i + a j ≤ ∑ l, a l := by
      have hh := Finset.sum_le_sum_of_subset_of_nonneg
        (show ({i, j} : Finset (Fin 10)) ⊆ Finset.univ by simp)
        (fun l _ _ ↦ ha l)
      simpa [Finset.sum_pair hij] using hh
    have hi := hpair i j hij
    have hj := hpair j i hij.symm
    rw [dist_comm (b j)] at hj
    have := hbound (dist (b i) (b j)) 2 (dist_pos.mpr (hc.1.ne hij)) (by norm_num)
      (by linarith)
    norm_num at this ⊢
    exact this
  · intro i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ ↦ ha j) (Finset.mem_univ i)
    have hp : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (b i) (b j))⁻¹ := by
      exact Finset.sum_nonneg fun j _ ↦ by split <;> positivity
    have h₁ : 0 ≤ ‖b i‖⁻¹ := by positivity
    have h₂ : 0 ≤ ‖b i - 1‖⁻¹ := by positivity
    dsimp [a] at hi
    constructor
    · simpa using hbound ‖b i‖ 1 (norm_pos_iff.mpr (hc.2 i).1) (by norm_num) (by linarith)
    · simpa using hbound ‖b i - 1‖ 1
        (norm_pos_iff.mpr (sub_ne_zero.mpr (hc.2 i).2)) (by norm_num) (by linarith)

theorem rf7_atlas_cover {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) : IsCoveringMapOn P.f (b6t_punctured b) := by
  let e : P.U ≃ₜ P.f ⁻¹' b6t_punctured b :=
    P.hι.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr P.hrange)
  have he (u : P.U) : (e u).val = P.ι u := rfl
  have hfun : (b6t_punctured b).restrictPreimage P.f = P.π ∘ e.symm := by
    funext x
    apply Subtype.ext
    change P.f x.val = (P.π (e.symm x)).val
    rw [← P.hproj]
    have h := congrArg Subtype.val (e.apply_symm_apply x)
    change P.ι (e.symm x) = x.val at h
    rw [h]
  have hcov : IsCoveringMap ((b6t_punctured b).restrictPreimage P.f) := by
    rw [hfun]
    exact P.hπ.isCoveringMap.comp_homeomorph e.symm
  have ho : IsOpen (b6t_punctured b) := (Set.finite_range (b6_branch b)).isClosed.isOpen_compl
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ ho
    (ho.preimage P.hf.continuous) hcov

theorem rf7_atlas_finite_fibres {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (p : OnePoint ℂ) : (P.f ⁻¹' {p}).Finite := by
  obtain ⟨x, hx⟩ := P.hsurj ((0 : ℂ) : OnePoint ℂ)
  obtain ⟨y, hy⟩ := P.hsurj OnePoint.infty
  apply b4_fiber_finite (Module.finrank_self ℂ) (Module.finrank_self ℂ) P.f P.hf
  exact ⟨x, y, by rw [hx, hy]; exact OnePoint.coe_ne_infty 0⟩


theorem rf7_atlas_isOpenMap {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) : IsOpenMap P.f := by
  letI : ContinuousConstSMul G C := ⟨fun g ↦ (P.hact g).continuous⟩
  have hq := P.hf.continuous.isClosedMap.isQuotientMap P.hf.continuous P.hsurj
  intro S hS
  apply hq.isCoinducing.isOpen_preimage.mp
  have heq : P.f ⁻¹' (P.f '' S) = ⋃ g : G, (fun x : C ↦ g • x) '' S := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨g, hg⟩ := P.hgal.2 y x hxy
      exact Set.mem_iUnion.mpr ⟨g, y, hy, hg⟩
    · intro hx
      obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨y, hy, (P.hgal.1 g y).symm⟩
  rw [heq]
  exact isOpen_iUnion fun g ↦ (Homeomorph.smul g).isOpenMap S hS

theorem rf7_sphereBall_isOpen (c : ℂ) (s : ℝ) : IsOpen (rf7_sphereBall c s) :=
  OnePoint.isOpenMap_coe _ Metric.isOpen_ball

theorem rf7_sphereBall_isConnected (c : ℂ) (s : ℝ) (hs : 0 < s) :
    IsConnected (rf7_sphereBall c s) :=
  (Metric.isConnected_ball hs).image _ OnePoint.continuous_coe.continuousOn

theorem rf7_component_open {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) :
    IsOpen (rf7_component P.f (b i) (3 * b6t_radius b) x) := by
  letI : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ℂ C
  exact ((rf7_sphereBall_isOpen _ _).preimage P.hf.continuous).connectedComponentIn

theorem rf7_component_proper {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ))
    (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ Metric.ball (b i) (3 * b6t_radius b)) :
    IsCompact (rf7_component P.f (b i) (3 * b6t_radius b) x ∩
      P.f ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' K)) := by
  have hr := (b6t_discs b P.hb).1
  apply rf7_component_compact_inter P.f
    (rf7_sphereBall (b i) (3 * b6t_radius b)) (((↑) : ℂ → OnePoint ℂ) '' K)
  · exact ((hK.image OnePoint.continuous_coe).isClosed.preimage P.hf.continuous).isCompact
  · exact Set.image_mono hKS
  · rw [hx]
    exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩

theorem rf7_component_onto {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x ∈ rf7_sphereBall (b i) (3 * b6t_radius b)) :
    P.f '' rf7_component P.f (b i) (3 * b6t_radius b) x =
      rf7_sphereBall (b i) (3 * b6t_radius b) := by
  have hr := (b6t_discs b P.hb).1
  letI : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ℂ C
  exact rf7_component_image_eq P.f P.hf.continuous (rf7_atlas_isOpenMap P)
    P.hf.continuous.isClosedMap _ (rf7_sphereBall_isOpen _ _)
    (rf7_sphereBall_isConnected _ _ (by positivity)) x hx

theorem rf7_outer_open {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    (f : C → OnePoint ℂ) (hf : Continuous f) : IsOpen (rf7_outer b f) := by
  apply IsOpen.preimage hf
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact ((isCompact_closedBall (b i) (rf7_radius b)).image OnePoint.continuous_coe).isClosed.isOpen_compl

theorem rf7_outer_closure {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    (f : C → OnePoint ℂ) (hf : Continuous f) :
    closure (rf7_outer b f) ⊆ f ⁻¹' {p | ∀ i, p ∉ rf7_sphereBall (b i) (rf7_radius b)} := by
  apply closure_minimal
  · intro y hy i h
    exact hy i (Set.image_mono Metric.ball_subset_closedBall h)
  · apply IsClosed.preimage hf
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ (rf7_sphereBall_isOpen _ _).isClosed_compl

theorem rf7_piece_cover {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (y : C) :
    y ∈ rf7_outer b P.f ∨ ∃ (i : Fin 10) (x : C),
      P.f x = ((b i : ℂ) : OnePoint ℂ) ∧ y ∈ rf7_inner b P.f i x := by
  classical
  by_cases hy : y ∈ rf7_outer b P.f
  · exact Or.inl hy
  · right
    change ¬ ∀ i, P.f y ∉ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (rf7_radius b) at hy
    push Not at hy
    obtain ⟨i, z, hz, hzy⟩ := hy
    have hr := (b6t_discs b P.hb).1
    have hρ : 2 * rf7_radius b < 3 * b6t_radius b := by unfold rf7_radius; linarith
    have hρ0 : 0 < rf7_radius b := by unfold rf7_radius; positivity
    change dist z (b i) ≤ rf7_radius b at hz
    have hyS : P.f y ∈ rf7_sphereBall (b i) (3 * b6t_radius b) :=
      ⟨z, lt_of_le_of_lt hz (by linarith), hzy⟩
    have hbi : ((b i : ℂ) : OnePoint ℂ) ∈ rf7_sphereBall (b i) (3 * b6t_radius b) :=
      ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩
    have hm : ((b i : ℂ) : OnePoint ℂ) ∈ P.f '' rf7_component P.f (b i) (3 * b6t_radius b) y :=
      (rf7_component_onto P i y hyS).symm ▸ hbi
    obtain ⟨x, hx, hfx⟩ := hm
    refine ⟨i, x, hfx, ?_, z, ?_, hzy⟩
    · have heq := connectedComponentIn_eq hx
      change connectedComponentIn (P.f ⁻¹' rf7_sphereBall (b i) (3 * b6t_radius b)) y =
        connectedComponentIn (P.f ⁻¹' rf7_sphereBall (b i) (3 * b6t_radius b)) x at heq
      change y ∈ connectedComponentIn (P.f ⁻¹' rf7_sphereBall (b i) (3 * b6t_radius b)) x
      rw [← heq]
      exact mem_connectedComponentIn hyS
    · exact lt_of_le_of_lt hz (by linarith)


theorem rf7_punctured_power_limit {C : Type} [TopologicalSpace C] [CompactSpace C] [T2Space C]
    (f : C → OnePoint ℂ) (hf : Continuous f) (c : ℂ)
    (hfin : (f ⁻¹' {(c : OnePoint ℂ)}).Finite)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hk : 0 < k) (j : ℂ → C)
    (hj : ContinuousOn j (Metric.ball (0 : ℂ) R \ {0}))
    (hp : ∀ z ∈ Metric.ball (0 : ℂ) R \ {0}, f (j z) = ((c + z ^ k : ℂ) : OnePoint ℂ)) :
    ∃ x, f x = (c : OnePoint ℂ) ∧ Tendsto j (𝓝[≠] (0 : ℂ)) (𝓝 x) := by
  refine b6m_connected_filter_finite_fibre (map j (𝓝[≠] (0 : ℂ))) ?_ f hf
    (c : OnePoint ℂ) hfin ?_
  · intro V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.mp hV
    let δ := min ε R
    have hδ : 0 < δ := lt_min hε hR
    have hδR : δ ≤ R := min_le_right _ _
    have hδε : δ ≤ ε := min_le_left _ _
    let S := Metric.ball (0 : ℂ) δ \ {0}
    have hS : S ∈ 𝓝[≠] (0 : ℂ) :=
      inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)) self_mem_nhdsWithin
    have hSR : S ⊆ Metric.ball (0 : ℂ) R \ {0} :=
      Set.sdiff_subset_sdiff_left (Metric.ball_subset_ball hδR)
    have hSc : IsPreconnected S := by
      have hh : PathConnectedSpace S :=
        rf7_puncturedDisc_pathConnected 0 0 δ (by simpa using hδ)
      exact (isPathConnected_iff_pathConnectedSpace.mpr hh).isConnected.isPreconnected
    refine ⟨j '' S, image_mem_map hS, hSc.image j (hj.mono hSR), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hεV ⟨Metric.ball_subset_ball hδε hz.1, hz.2⟩
  · rw [tendsto_map'_iff]
    have heq : (f ∘ j) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ ↦ ((c + z ^ k : ℂ) : OnePoint ℂ)) := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hR),
        self_mem_nhdsWithin] with z hz hzne
      exact hp z ⟨hz, hzne⟩
    have hc : Continuous (fun z : ℂ ↦ ((c + z ^ k : ℂ) : OnePoint ℂ)) :=
      OnePoint.continuous_coe.comp (continuous_const.add (continuous_pow k))
    have ht := hc.continuousAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ) from nhdsWithin_le_nhds)
    have ht' : Tendsto (fun z : ℂ ↦ ((c + z ^ k : ℂ) : OnePoint ℂ))
        (𝓝[≠] (0 : ℂ)) (𝓝 (c : OnePoint ℂ)) := by
      simpa only [zero_pow hk.ne', add_zero] using ht
    exact ht'.congr' heq.symm

end HodgeLean.Foundations.Program
