import HodgeLean.Foundations.Program.HurwitzPrymCovDegree
import HodgeLean.Foundations.Program.HurwitzPrymCovConnected

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: ramification of Galois covers

For a Galois cover `f : C → Y` with group `G` acting faithfully and holomorphically, the points
near `x` over a value `y' ≠ f x` near `f x` form one free `G_x`-orbit: translates by
elements outside `G_x` move a small neighborhood off itself, and fixed points of nontrivial
elements are isolated. Comparing with the local degree gives `e_x = |G_x|`, and orbit counting
gives the degree `|G|`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff Pointwise

namespace HodgeLean.Foundations.Program

section Galois

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

/-- **Fixed points of a nontrivial automorphism are isolated.** -/
theorem b4cov_fixed_isolated [T2Space C] [ConnectedSpace C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (x : C) (k : G)
    (hk : k • x = x) (hk1 : k ≠ 1) : ∀ᶠ z in 𝓝 x, k • z = z → z = x := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have := FiniteDimensional.complete ℂ E
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfr : ∃ᶠ z in 𝓝[≠] x, k • z = z := by
    rw [frequently_nhdsWithin_iff]
    exact hcon.mono fun z hz ↦ ⟨(not_imp.1 hz).1, (not_imp.1 hz).2⟩
  set φ := extChartAt 𝓘(ℂ, E) x
  have hfr' := b4cov_frequently_chart (E := E) (E' := E) (id : C → C) continuous_id x hfr
  let T : E → E := fun w ↦ φ (k • φ.symm w) - w
  have hT : AnalyticAt ℂ T (φ x) := by
    have := b4cov_analyticAt_chart (fun z : C ↦ k • z) (hG k) x x (φ x) (mem_extChartAt_target x)
      (by simp only [φ, extChartAt_to_inv, hk]; exact mem_extChartAt_source x)
    exact this.sub analyticAt_id
  have hTz : ∃ᶠ w in 𝓝[≠] (φ x), T w = 0 := by
    refine hfr'.mono fun w ⟨hw, hP⟩ ↦ ?_
    have hP' : k • φ.symm w = φ.symm w := hP
    simp only [T]
    rw [hP', φ.right_inv hw.1, sub_self]
  have hev := b4cov_eventually_zero_of_frequently hE hT hTz
  have hcont : ContinuousAt (fun z ↦ k • z) x := (hG k).continuous.continuousAt
  have hloc : ∀ᶠ z in 𝓝 x, k • z = z := by
    have h1 := (continuousAt_extChartAt x).preimage_mem_nhds hev
    have h2 : ∀ᶠ z in 𝓝 x, k • z ∈ φ.source :=
      hcont.preimage_mem_nhds (by rw [hk]; exact extChartAt_source_mem_nhds x)
    filter_upwards [h1, h2, extChartAt_source_mem_nhds (I := 𝓘(ℂ, E)) x] with z hz1 hz2 hz3
    have : φ (k • φ.symm (φ z)) - φ z = 0 := hz1
    rw [φ.left_inv hz3, sub_eq_zero] at this
    exact φ.injOn hz2 hz3 this
  have hall := b4cov_eq_of_eventuallyEq (fun z : C ↦ k • z) id (hG k) contMDiff_id x hloc
  exact hk1 (eq_of_smul_eq_smul fun z ↦ by rw [one_smul]; exact congrFun hall z)

/-- **Translates by elements outside the stabilizer move a neighborhood off itself.** -/
theorem b4cov_exists_separating [Finite G] [T2Space C]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (x : C) :
    ∃ N ∈ 𝓝 x, ∀ z ∈ N, ∀ g : G, g • z ∈ N → g • x = x := by
  classical
  have key : ∀ g : G, ∃ Ng ∈ 𝓝 x, ∀ z ∈ Ng, g • z ∈ Ng → g • x = x := by
    intro g
    by_cases hg : g • x = x
    · exact ⟨univ, univ_mem, fun _ _ _ ↦ hg⟩
    · obtain ⟨A, B, hA, hB, hxA, hgB, hAB⟩ := t2_separation (Ne.symm hg)
      refine ⟨A ∩ (fun z ↦ g • z) ⁻¹' B, inter_mem (hA.mem_nhds hxA)
        ((hG g).continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hgB)), ?_⟩
      rintro z ⟨-, hzB⟩ ⟨hgzA, -⟩
      exact absurd (hAB.ne_of_mem hgzA hzB rfl) (by simp)
  choose Ng hNg hsep using key
  refine ⟨⋂ g, Ng g, Filter.iInter_mem.2 hNg, fun z hz g hgz ↦ ?_⟩
  exact hsep g z (mem_iInter.1 hz g) (mem_iInter.1 hgz g)

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- A Galois cover of a surface by a finite group is non-constant (a surface is infinite). -/
theorem b4cov_nonconst_of_galois [Finite G] [T2Space C] (hE : Module.finrank ℂ E = 1) {Y : Type*}
    (f : C → Y) (hgal : b4_IsGaloisCover G f) (x : C) : ∃ a b, f a ≠ f b := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hall : ∀ a, a ∈ range (fun g : G ↦ g • x) := fun a ↦ hgal.2 x a (h x a)
  have : Finite C := Set.finite_univ_iff.1 ((finite_range _).subset fun a _ ↦ hall a)
  obtain ⟨U, hU, -, -, -, z, hzU, hzx⟩ :=
    b4cov_goodPoint hE x {x} ((isOpen_discrete {x}).mem_nhds rfl)
  exact hzx (hU hzU)

/-- Over values near `f x`, the points of a closed set whose only point over `f x` is `x` lie in
any given open neighborhood of `x`. -/
theorem b4cov_fiber_subset_eventually [CompactSpace C] {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] (f : C → Y) (hfc : Continuous f) (x : C) (K : Set C) (hK : IsClosed K)
    (hKx : ∀ z ∈ K, f z = f x → z = x) (U : Set C) (hU : IsOpen U) (hxU : x ∈ U) :
    ∀ᶠ y' in 𝓝 (f x), ∀ z ∈ K, f z = y' → z ∈ U := by
  have hM : IsClosed (f '' (K \ U)) :=
    ((hK.sdiff hU).isCompact.image hfc).isClosed
  have hfx : f x ∉ f '' (K \ U) := by
    rintro ⟨z, ⟨hzK, hzU⟩, hzx⟩
    exact hzU (hKx z hzK hzx ▸ hxU)
  filter_upwards [hM.isOpen_compl.mem_nhds hfx] with y' hy' z hzK hzy
  by_contra hzU
  exact hy' ⟨z, ⟨hzK, hzU⟩, hzy⟩

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y] [IsManifold 𝓘(ℂ, E') ω Y]

/-- **The ramification index of a Galois cover is the order of the stabilizer.** -/
theorem b4cov_ramIndex_galois [Finite G] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [FaithfulSMul G C] [T2Space Y] (hE : Module.finrank ℂ E = 1)
    (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) (x : C) :
    b4_ramIndex E E' f x = Nat.card (MulAction.stabilizer G x) := by
  classical
  have hnc := b4cov_nonconst_of_galois hE f hgal x
  set S := MulAction.stabilizer G x
  have hcont : ∀ g : G, Continuous fun z : C ↦ g • z := fun g ↦ (hG g).continuous
  -- a first neighborhood where `x` is the only point over `f x`
  obtain ⟨U₁, -, hU₁o, hxU₁, -, -, hzero₁, -⟩ :=
    b4cov_local_degree hE hE' f hf hnc x univ univ_mem
  obtain ⟨K₀, hK₀, hK₀c, hK₀U⟩ := exists_mem_nhds_isClosed_subset (hU₁o.mem_nhds hxU₁)
  -- separation and isolated fixed points
  obtain ⟨N₁, hN₁, hsep⟩ := b4cov_exists_separating hG x
  have hiso : ∀ᶠ z in 𝓝 x, ∀ k : S, (k : G) ≠ 1 → (k : G) • z = z → z = x :=
    Filter.eventually_all.2 fun k ↦ by
      by_cases hk : (k : G) = 1
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hk h
      · exact (b4cov_fixed_isolated hE hG x k k.2 hk).mono fun z hz _ ↦ hz
  -- an `S`-invariant neighborhood with all these properties
  let P : Set C := K₀ ∩ N₁ ∩ {z | ∀ k : S, (k : G) ≠ 1 → (k : G) • z = z → z = x}
  have hP : P ∈ 𝓝 x := inter_mem (inter_mem hK₀ hN₁) hiso
  let R : Set C := ⋂ k : S, (fun z : C ↦ (k : G) • z) ⁻¹' P
  have hR : R ∈ 𝓝 x := Filter.iInter_mem.2 fun k ↦
    (hcont k).continuousAt.preimage_mem_nhds (by
      show P ∈ 𝓝 ((k : G) • x)
      rw [k.2]; exact hP)
  have hRP : R ⊆ P := fun z hz ↦ by simpa using mem_iInter.1 hz 1
  have hRinv : ∀ k : S, ∀ z ∈ R, (k : G) • z ∈ R := by
    intro k z hz
    refine mem_iInter.2 fun k' ↦ ?_
    have := mem_iInter.1 hz (k' * k)
    simpa [mul_smul] using this
  -- the local degree inside `R`
  obtain ⟨U, hUR, hUo, hxU, V, hV, hzero, hcount⟩ :=
    b4cov_local_degree hE hE' f hf hnc x R hR
  let W : Set C := ⋃ k : S, (fun z : C ↦ (k : G)⁻¹ • z) ⁻¹' U
  have hUW : U ⊆ W := fun z hz ↦ mem_iUnion.2 ⟨1, by simpa using hz⟩
  have hWR : W ⊆ R := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    have := hRinv k _ (hUR hk)
    simpa [smul_smul] using this
  have hWinv : ∀ k : S, ∀ z ∈ W, (k : G) • z ∈ W := by
    intro k z hz
    obtain ⟨k', hk'⟩ := mem_iUnion.1 hz
    refine mem_iUnion.2 ⟨k * k', ?_⟩
    have : ((k * k' : S) : G)⁻¹ • ((k : G) • z) = (k' : G)⁻¹ • z := by
      rw [smul_smul]
      congr 1
      simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show ((k * k' : S) : G)⁻¹ • ((k : G) • z) ∈ U
    rw [this]
    exact hk'
  -- the closed invariant set `K` used for containment of fibres
  have hEC := b4cov_fiber_subset_eventually f hf.continuous x (closure R) isClosed_closure
    (fun z hz hzx ↦ hzero₁ z (hK₀U (hK₀c.closure_subset_iff.2
      (fun w hw ↦ (hRP hw).1.1) hz)) hzx) U hUo hxU
  -- a point `z ≠ x` of `U` with `f z` in the good neighborhood of `f x`
  have hgood : (U ∩ f ⁻¹' ({y' | ∀ z ∈ closure R, f z = y' → z ∈ U} ∩ V)) ∈ 𝓝 x :=
    inter_mem (hUo.mem_nhds hxU) (hf.continuous.continuousAt.preimage_mem_nhds (hEC.and hV))
  obtain ⟨U', hU'sub, -, -, -, z, hzU', hzx⟩ := b4cov_goodPoint hE x _ hgood
  obtain ⟨hzU, hzEC, hzV⟩ := hU'sub hzU'
  have hfz : f z ≠ f x := fun h ↦ hzx (hzero z hzU h)
  obtain ⟨hcard, -⟩ := hcount (f z) hzV hfz
  -- the fibre near `x` is the free `S`-orbit of `z`
  have hfib : f ⁻¹' {f z} ∩ U = range fun k : S ↦ (k : G) • z := by
    ext w
    constructor
    · rintro ⟨hwf, hwU⟩
      obtain ⟨g, hg⟩ := hgal.2 z w hwf.symm
      have hgx : g • x = x := hsep z ((hRP (hWR (hUW hzU))).1.2) g
        (hg ▸ (hRP (hWR (hUW hwU))).1.2)
      exact ⟨⟨g, hgx⟩, hg⟩
    · rintro ⟨k, rfl⟩
      refine ⟨hgal.1 k z, hzEC _ (subset_closure (hWR (hWinv k z (hUW hzU)))) (hgal.1 k z)⟩
  have hinj : Function.Injective fun k : S ↦ (k : G) • z := by
    intro a b hab
    have hab' : ((b⁻¹ * a : S) : G) • z = z := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      rw [show (a : G) • z = (b : G) • z from hab, inv_smul_smul]
    by_contra hne
    have h1 : ((b⁻¹ * a : S) : G) ≠ 1 := by
      intro h1
      apply hne
      have : b⁻¹ * a = 1 := Subtype.ext h1
      exact (inv_mul_eq_one.1 this).symm
    exact hzx ((hRP (hWR (hUW hzU))).2 _ h1 hab')
  rw [← hcard, hfib, ← image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]

/-- **The degree of a Galois cover is the order of the group.** -/
theorem b4cov_fiberDegree_galois [Finite G] [Nonempty C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [FaithfulSMul G C] [T2Space Y] [ConnectedSpace Y]
    (hE : Module.finrank ℂ E = 1) (hE' : Module.finrank ℂ E' = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) (hgal : b4_IsGaloisCover G f) (y : Y) :
    b4_fiberDegree E E' f y = Nat.card G := by
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have hnc := b4cov_nonconst_of_galois hE f hgal x₀
  obtain ⟨x, rfl⟩ := b4cov_surjective hE' f hf hnc y
  have hfib : f ⁻¹' {f x} = MulAction.orbit G x := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, MulAction.mem_orbit_iff]
    exact ⟨fun h ↦ hgal.2 x z h.symm, fun ⟨g, hg⟩ ↦ hg ▸ hgal.1 g x⟩
  have hcard : ∀ z ∈ MulAction.orbit G x,
      Nat.card (MulAction.stabilizer G z) = Nat.card (MulAction.stabilizer G x) := by
    intro z hz
    have h1 := Subgroup.card_mul_index (MulAction.stabilizer G z)
    have h2 := Subgroup.card_mul_index (MulAction.stabilizer G x)
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_iff.2 hz] at h1
    rw [MulAction.index_stabilizer] at h2
    have hpos : 0 < (MulAction.orbit G x).ncard :=
      (Set.ncard_pos (Set.finite_range fun g : G ↦ g • x)).2 ⟨x, MulAction.mem_orbit_self x⟩
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  rw [b4_fiberDegree, hfib]
  rw [finsum_mem_congr rfl fun z hz ↦ (b4cov_ramIndex_galois hE hE' hG f hf hgal z).trans
    (hcard z hz)]
  rw [← mul_one (Nat.card (MulAction.stabilizer G x)), ← mul_finsum_mem,
    finsum_one, mul_comm, ← MulAction.index_stabilizer, Subgroup.index_mul_card]

end Galois

end HodgeLean.Foundations.Program
