import HodgeLean.Foundations.Program.RelativeFrameFamilyOuter
import HodgeLean.Foundations.Program.RelativeFrameFamilyMarked
import HodgeLean.Foundations.Program.RelativeFrameFamilyDefs
import HodgeLean.Foundations.Program.RelativeFrameFamilyCovering
import HodgeLean.Foundations.Program.RelativeFrameFamilyGeometry
import HodgeLean.Foundations.Program.RelativeFrameFamilyComponent
import HodgeLean.Foundations.Program.RelativeFrameFamilyBase
import HodgeLean.Foundations.Program.RelativeFrameFamilyMoving

noncomputable section
open Set Manifold Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold b4b_group

theorem rf7_rootAtlas_aux (y₀ : b6t_punctured mr_base)
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i)) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C)
      (_ : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C))
      (P : rf7_HurwitzAtlas mr_base b4b_Group C),
      (∃ u₀ : P.π ⁻¹' {y₀}, ∀ i,
        P.hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i)) ∧
      ∀ x (j : Fin 13), P.f x = b6_branch mr_base j → P.n x = orderOf (b4b_root j) := by
  exact rf7_marked_atlas y₀ γ hγ

theorem rf7_radius_bounds_aux (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) :
    b6t_radius b < rf7_radius b ∧ 2 * rf7_radius b < 3 * b6t_radius b ∧
      (∀ i j : Fin 10, i ≠ j → Disjoint (Metric.closedBall (b i) (3 * b6t_radius b))
        (Metric.closedBall (b j) (3 * b6t_radius b))) ∧
      (∀ i, (0 : ℂ) ∉ Metric.closedBall (b i) (3 * b6t_radius b) ∧
        (1 : ℂ) ∉ Metric.closedBall (b i) (3 * b6t_radius b)) ∧
      (∀ i (z : ℂ), rf7_radius b ≤ dist z (b i) → dist z (b i) ≤ 2 * rf7_radius b →
        ∀ j, b6t_radius b < dist z (b j)) ∧
      ∀ t ∈ b6t_polydisc b, ∀ i, ‖t i - b i‖ < rf7_radius b := by
  have hr := (b6t_discs b hb).1
  obtain ⟨hsep, hfixed⟩ := rf7_radius_separation b hb
  have hρ : b6t_radius b < rf7_radius b := by unfold rf7_radius; linarith
  have hρ' : 2 * rf7_radius b < 3 * b6t_radius b := by unfold rf7_radius; linarith
  refine ⟨hρ, hρ', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have ht := dist_triangle (b i) z (b j)
    rw [dist_comm (b i) z] at ht
    have hs := hsep i j hij
    change dist z (b i) ≤ _ at hz
    change dist z (b j) ≤ _ at hz'
    linarith
  · intro i
    obtain ⟨h0, h1⟩ := hfixed i
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_left, not_le] using
        (show 3 * b6t_radius b < ‖b i‖ by linarith)
    · simpa only [Metric.mem_closedBall, dist_comm (1 : ℂ), dist_eq_norm, not_le] using
        (show 3 * b6t_radius b < ‖b i - 1‖ by linarith)
  · intro i z hlo hhi j
    by_cases hij : i = j
    · subst j
      exact hρ.trans_le hlo
    · have hs := hsep i j hij
      have ht := dist_triangle (b i) z (b j)
      rw [dist_comm (b i) z] at ht
      unfold rf7_radius at hhi
      linarith
  · intro t ht i
    have hi : dist (t i) (b i) < b6t_radius b := ht i
    rw [dist_eq_norm] at hi
    exact hi.trans hρ

theorem rf7_punctured_disc_subset (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (i : Fin 10) :
    rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)} ⊆
      b6t_punctured b := by
  have hr := (b6t_discs b hb).1
  obtain ⟨_, _, hdisj, hfixed, _, _⟩ := rf7_radius_bounds_aux b hb
  rintro p ⟨⟨z, hz, rfl⟩, hne⟩ hbranch
  have hz' : z ∈ Metric.closedBall (b i) (3 * b6t_radius b) := Metric.ball_subset_closedBall hz
  have hcent (j : Fin 10) : z ≠ b j := by
    intro h
    by_cases hij : i = j
    · subst j
      exact hne (by simpa only [Set.mem_singleton_iff] using congrArg (fun w : ℂ ↦ (w : OnePoint ℂ)) h)
    · exact Set.disjoint_left.mp (hdisj i j hij) hz'
        (h ▸ Metric.mem_closedBall_self (by positivity))
  have h0 : z ≠ 0 := fun h ↦ (hfixed i).1 (h ▸ hz')
  have h1 : z ≠ 1 := fun h ↦ (hfixed i).2 (h ▸ hz')
  rcases (mr_mem_branch b _).mp hbranch with h | ⟨j, hj⟩
  · exact OnePoint.coe_ne_infty z h
  · have hnot (j : Fin 12) : z ≠ mr_fin b j := by
      induction j using (Fin.addCases (m := 10) (n := 2)) with
      | left j => simpa only [mr_fin, Fin.append_left] using hcent j
      | right j => fin_cases j <;> simpa [mr_fin] using (by assumption : z ≠ _)
    exact hnot j (OnePoint.coe_injective hj)


theorem rf7_covering_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) :
    IsCoveringMapOn P.f
        (rf7_sphereBall (b i) (3 * b6t_radius b) \ {((b i : ℂ) : OnePoint ℂ)}) ∧
      ∀ p : OnePoint ℂ, (P.f ⁻¹' {p}).Finite := by
  exact ⟨(rf7_atlas_cover P).mono (rf7_punctured_disc_subset b P.hb i),
    rf7_atlas_finite_fibres P⟩

theorem rf7_piece_overlap {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) :
    rf7_outer b P.f ∩ rf7_inner b P.f i x =
      rf7_component P.f (b i) (3 * b6t_radius b) x ∩
        P.f ⁻¹' rf7_sphereAnnulus (b i) (rf7_radius b) (2 * rf7_radius b) := by
  obtain ⟨hρ, hρ', hdisj, _, _, _⟩ := rf7_radius_bounds_aux b P.hb
  have hr := (b6t_discs b P.hb).1
  ext y
  constructor
  · rintro ⟨hO, hcomp, z, hz, hzy⟩
    refine ⟨hcomp, z, ⟨?_, hz⟩, hzy⟩
    by_contra h
    exact hO i ⟨z, le_of_not_gt h, hzy⟩
  · rintro ⟨hcomp, z, ⟨hlo, hhi⟩, hzy⟩
    refine ⟨?_, hcomp, z, hhi, hzy⟩
    intro j ⟨w, hw, hwy⟩
    have hwz : w = z := OnePoint.coe_injective (hwy.trans hzy.symm)
    subst w
    change dist z (b j) ≤ rf7_radius b at hw
    by_cases hij : i = j
    · subst j
      exact not_le_of_gt hlo hw
    · apply Set.disjoint_left.mp (hdisj i j hij)
      · exact le_of_lt (hhi.trans hρ')
      · exact hw.trans (by linarith)

theorem rf7_component_centre_fibre {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    rf7_component P.f (b i) (3 * b6t_radius b) x ∩
      P.f ⁻¹' {((b i : ℂ) : OnePoint ℂ)} = {x} := by
  have hr := (b6t_discs b P.hb).1
  ext y
  constructor
  · rintro ⟨hy, hfy⟩
    exact rf7_component_unique_centre P i x hx (rf7_covering_aux P i).1 y hy hfy
  · intro hy
    subst y
    refine ⟨mem_connectedComponentIn ?_, hx⟩
    change P.f x ∈ rf7_sphereBall (b i) (3 * b6t_radius b)
    rw [hx]
    exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩

theorem rf7_component_order_one {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C)
    (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) (y : C)
    (hy : y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x) (hne : y ≠ x) : P.n y = 1 := by
  have hyS := connectedComponentIn_subset _ _ hy
  have hyne : P.f y ≠ ((b i : ℂ) : OnePoint ℂ) := by
    intro hfy
    exact hne (rf7_component_unique_centre P i x hx (rf7_covering_aux P i).1 y hy hfy)
  have hfree : P.f y ∉ Set.range (b6_branch b) :=
    rf7_punctured_disc_subset b P.hb i ⟨hyS, hyne⟩
  let t : b6t_polydisc b := ⟨b, (b6t_polydisc_neighbourhood b P.hb).1⟩
  exact (P.hfree (t, y) hfree).1

theorem rf7_component_props_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    IsOpen (rf7_component P.f (b i) (3 * b6t_radius b) x) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (b i) (3 * b6t_radius b) →
        IsCompact (rf7_component P.f (b i) (3 * b6t_radius b) x ∩
          P.f ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' K))) ∧
      rf7_sphereBall (b i) (3 * b6t_radius b) ⊆
        P.f '' rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      rf7_component P.f (b i) (3 * b6t_radius b) x ∩ P.f ⁻¹' {((b i : ℂ) : OnePoint ℂ)} = {x} ∧
      (∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x, y ≠ x → P.n y = 1) ∧
      ∀ z ∈ Metric.ball (b i) (3 * b6t_radius b), z ≠ b i →
        Nat.card ↥(rf7_component P.f (b i) (3 * b6t_radius b) x ∩
          P.f ⁻¹' {((z : ℂ) : OnePoint ℂ)}) = P.n x := by
  have hr := (b6t_discs b P.hb).1
  have hxS : P.f x ∈ rf7_sphereBall (b i) (3 * b6t_radius b) := by
    rw [hx]
    exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩
  refine ⟨rf7_component_open P i x, rf7_component_proper P i x hx,
    (rf7_component_onto P i x hxS).ge, rf7_component_centre_fibre P i x hx,
    rf7_component_order_one P i x hx, ?_⟩
  exact fun z hz hnz ↦ rf7_component_fibre_degree P i x hx (rf7_covering_aux P i).1 z hz hnz

theorem rf7_base_root_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
    ∃ u : OpenPartialHomeomorph C ℂ, u ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C ∧
      u.source = rf7_component P.f (b i) (3 * b6t_radius b) x ∧
      u.target = {w : ℂ | ‖w‖ ^ P.n x < 3 * b6t_radius b} ∧ u x = 0 ∧
      ∀ y ∈ rf7_component P.f (b i) (3 * b6t_radius b) x,
        P.f y = ((b i + u y ^ P.n x : ℂ) : OnePoint ℂ) := by
  exact rf7_base_root_of_covering P i x hx (rf7_covering_aux P i).1

theorem rf7_offcentre_classify_aux {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] [ConnectedSpace Y] (a c : ℂ) (ρ : ℝ) (hc : ‖c - a‖ < ρ)
    (k : ℕ) (hk : 0 < k) (q : Y → ℂ) (hq : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) q)
    (hrange : ∀ y, q y ∈ Metric.ball a ρ \ {c})
    (hcov : IsCoveringMapOn q (Metric.ball a ρ \ {c}))
    (hdeg : ∀ z ∈ Metric.ball a ρ \ {c}, Nat.card (q ⁻¹' {z}) = k) :
    ∃ v : Y → ℂ, MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) v ∧ Function.Injective v ∧
      range v = {w : ℂ | w ≠ 0 ∧ ‖c + w ^ k - a‖ < ρ} ∧ ∀ y, q y = c + v y ^ k := by
  classical
  letI : LocallyPathConnectedSpace Y := ChartedSpace.locallyPathConnectedSpace ℂ Y
  letI : PathConnectedSpace Y := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨v, hv, hinj, hr, heq⟩ := rf7_offcentre_topological
    a c ρ hc k hk q hrange hcov hdeg
  have h0 (y : Y) : v y ≠ 0 := by
    intro hh
    have hh' := heq y
    rw [hh, zero_pow hk.ne', add_zero] at hh'
    exact (hrange y).2 hh'
  have hp : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y ↦ v y ^ k) := by
    have hh : (fun y ↦ v y ^ k) = (fun y ↦ q y - c) := by
      funext y
      rw [heq y]
      ring
    rw [hh]
    exact hq.sub mdifferentiable_const
  exact ⟨v, rf7_mdifferentiable_root k hk v hv.continuous h0 hp, hinj, hr, heq⟩

theorem rf7_moving_root_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) (i : Fin 10) (x : C) (hx : P.f x = ((b i : ℂ) : OnePoint ℂ)) :
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
  obtain ⟨u, _, huS, huT, hux, huP⟩ := rf7_base_root_aux P i x hx
  exact rf7_moving_root_of_chart P i x hx u huS huT hux huP

theorem rf7_pieces_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) :
    IsOpen (rf7_outer b P.f) ∧
      closure (rf7_outer b P.f) ⊆
        P.f ⁻¹' {p | ∀ i, p ∉ rf7_sphereBall (b i) (rf7_radius b)} ∧
      (∀ (i i' : Fin 10) (x x' : C), P.f x = ((b i : ℂ) : OnePoint ℂ) →
        P.f x' = ((b i' : ℂ) : OnePoint ℂ) → x ≠ x' →
          Disjoint (rf7_component P.f (b i) (3 * b6t_radius b) x)
            (rf7_component P.f (b i') (3 * b6t_radius b) x')) ∧
      (∀ y : C, y ∈ rf7_outer b P.f ∨
        ∃ (i : Fin 10) (x : C), P.f x = ((b i : ℂ) : OnePoint ℂ) ∧ y ∈ rf7_inner b P.f i x) ∧
      ∀ (i : Fin 10) (x : C), P.f x = ((b i : ℂ) : OnePoint ℂ) →
        rf7_outer b P.f ∩ rf7_inner b P.f i x =
          rf7_component P.f (b i) (3 * b6t_radius b) x ∩
            P.f ⁻¹' rf7_sphereAnnulus (b i) (rf7_radius b) (2 * rf7_radius b) := by
  obtain ⟨_, _, hdisj, _, _, _⟩ := rf7_radius_bounds_aux b P.hb
  have hr := (b6t_discs b P.hb).1
  refine ⟨rf7_outer_open P.f P.hf.continuous, rf7_outer_closure P.f P.hf.continuous,
    ?_, rf7_piece_cover P, fun i x _ ↦ rf7_piece_overlap P i x⟩
  intro i i' x x' hx hx' hxx'
  apply Set.disjoint_left.mpr
  intro y hy hy'
  by_cases hii' : i = i'
  · subst i'
    have heq := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hy').symm
    have hx'S : x' ∈ P.f ⁻¹' rf7_sphereBall (b i) (3 * b6t_radius b) := by
      change P.f x' ∈ rf7_sphereBall (b i) (3 * b6t_radius b)
      rw [hx']
      exact ⟨b i, Metric.mem_ball_self (by positivity), rfl⟩
    have hx'comp : x' ∈ rf7_component P.f (b i) (3 * b6t_radius b) x := by
      rw [rf7_component, heq]
      exact mem_connectedComponentIn hx'S
    exact hxx' (rf7_component_unique_centre P i x hx (rf7_covering_aux P i).1 x' hx'comp hx').symm
  · have hyS := connectedComponentIn_subset _ _ hy
    have hyS' := connectedComponentIn_subset _ _ hy'
    obtain ⟨z, hz, hzy⟩ := hyS
    obtain ⟨w, hw, hwy⟩ := hyS'
    have hwz : w = z := OnePoint.coe_injective (hwy.trans hzy.symm)
    subst w
    exact Set.disjoint_left.mp (hdisj i i' hii') (Metric.ball_subset_closedBall hz)
      (Metric.ball_subset_closedBall hw)

theorem rf7_outer_data_aux {b : Fin 10 → ℂ} {G : Type} [Group G] [Finite G] {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction G C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (P : rf7_HurwitzAtlas b G C) :
    ∃ (D : rf4_OuterData C (rf7_outer b P.f))
      (e : Fin D.m ≃ {x : C // ∃ i : Fin 10, P.f x = ((b i : ℂ) : OnePoint ℂ)})
      (idx : Fin D.m → Fin 10),
      D.r = rf7_radius b ∧
      (∀ k, P.f (e k).val = ((b (idx k) : ℂ) : OnePoint ℂ) ∧ D.c k = b (idx k) ∧
        D.deg k = P.n (e k).val) ∧
      (∀ k, (D.P.chart (D.ann k)).source ⊆
          rf7_component P.f (b (idx k)) (3 * b6t_radius b) (e k).val ∧
        ∀ y ∈ (D.P.chart (D.ann k)).source,
          P.f y = ((D.c k + D.P.chart (D.ann k) y ^ D.deg k : ℂ) : OnePoint ℂ)) ∧
      (∀ j, (D.P.chart j).source ⊆ P.f ⁻¹'
        {p | ∀ i, p ∉ ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (b i) (b6t_radius b)}) ∧
      ∀ j, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
        (fun q : b6t_polydisc b × C ↦ D.P.chart j q.2) {q | q.2 ∈ (D.P.chart j).source} := by
  exact rf7_outer_data_of_coverings P (fun i ↦ (rf7_covering_aux P i).1)

end HodgeLean.Foundations.Program
