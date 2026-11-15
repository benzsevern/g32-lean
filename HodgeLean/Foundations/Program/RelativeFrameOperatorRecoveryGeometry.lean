import HodgeLean.Foundations.Program.RelativeFrameOperatorCutoffMap
import HodgeLean.Foundations.Program.RelativeFrameOperatorSmoothCoefficients

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_annulus_in_inner {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (S : rf4_Plumbing D ε X) (x : Fin D.m) :
    S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r) ⊆
      (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) := by
  intro p hp
  exact ((Set.ext_iff.mp (S.overlap x) p).mpr hp).2

theorem rf4_annuli_disjoint {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (S : rf4_Plumbing D ε X) :
    Pairwise fun x y ↦ Disjoint
      (S.h '' ((D.P.chart (D.ann x)).symm '' b63r_annulus (D.deg x) D.r))
      (S.h '' ((D.P.chart (D.ann y)).symm '' b63r_annulus (D.deg y) D.r)) := by
  intro x y hxy
  exact (S.disjoint hxy).mono (rf4_annulus_in_inner S x) (rf4_annulus_in_inner S y)

theorem rf4_transition_bdd {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e d : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (K L : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (hsK : K ⊆ e.target) (hsL : L ⊆ d.target) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ w ∈ L, e.symm z = d.symm w →
      ‖deriv (d ∘ e.symm) z‖ ≤ B := by
  let A := e.symm '' K ∩ d.symm '' L
  have hEK := hK.image_of_continuousOn (e.continuousOn_symm.mono hsK)
  have hDL := hL.image_of_continuousOn (d.continuousOn_symm.mono hsL)
  have hA : IsCompact A := hEK.inter_right hDL.isClosed
  have hAe : A ⊆ e.source := by
    rintro p ⟨⟨z, hz, rfl⟩, _⟩
    exact e.map_target (hsK hz)
  have hAd : A ⊆ d.source := by
    rintro p ⟨_, ⟨w, hw, rfl⟩⟩
    exact d.map_target (hsL hw)
  have himage := hA.image_of_continuousOn (e.continuousOn.mono hAe)
  have hcont : ContinuousOn (fun z ↦ ‖deriv (d ∘ e.symm) z‖) (e '' A) := by
    rintro z ⟨p, hp, rfl⟩
    have ht := rf4_atlas_transition_analytic e d he hd (e p) (e.map_source (hAe hp))
      (by simpa only [e.left_inv (hAe hp)] using hAd hp)
    exact ht.deriv.continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := himage.bddAbove_image hcont
  refine ⟨B, ?_⟩
  intro z hz w hw hzw
  apply hB
  refine ⟨z, ?_, rfl⟩
  exact ⟨e.symm z, ⟨⟨z, hz, rfl⟩, ⟨w, hw, hzw.symm⟩⟩, e.right_inv (hsK hz)⟩

theorem rf4_halfClosedAnnulus_closure (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (u : ℂ) (hu : r ≤ ‖u‖ ^ n ∧ ‖u‖ ^ n < 2 * r) :
    u ∈ closure (b63r_annulus n r) := by
  have hu0 : 0 < ‖u‖ := by
    apply norm_pos_iff.mpr
    exact rf4_closedAnnulus_ne_zero hn hr ⟨hu.1, hu.2.le⟩
  have hc : Continuous (fun t : ℝ ↦ (t : ℂ) * u) := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ) * u) (𝓝[>] 1) (𝓝 u) := by
    simpa only [Complex.ofReal_one, one_mul] using
      (hc.tendsto 1).mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  have hU : ∀ᶠ t : ℝ in 𝓝 1, ‖(t : ℂ) * u‖ ^ n < 2 * r :=
    (isOpen_lt (by fun_prop : Continuous (fun t : ℝ ↦ ‖(t : ℂ) * u‖ ^ n))
      continuous_const).mem_nhds (by simpa only [Set.mem_setOf_eq, Complex.ofReal_one, one_mul] using hu.2)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, hU.filter_mono nhdsWithin_le_nhds] with t ht htu
  change r < ‖(t : ℂ) * u‖ ^ n ∧ ‖(t : ℂ) * u‖ ^ n < 2 * r
  refine ⟨?_, htu⟩
  have ht1 : 1 < t := ht
  have hpow : ‖u‖ ^ n < (t * ‖u‖) ^ n :=
    pow_lt_pow_left₀ (by nlinarith) (norm_nonneg u) (by omega)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < t)]
    using hu.1.trans_lt hpow

theorem rf4_halfClosedAnnulus_inner {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) (x : Fin D.m)
    (u : ℂ) (hu : D.r ≤ ‖u‖ ^ D.deg x ∧ ‖u‖ ^ D.deg x < 2 * D.r) :
    S.h ((D.P.chart (D.ann x)).symm u) ∈
      (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  let A := b63r_annulus (D.deg x) D.r
  have hucl : u ∈ closure A := rf4_halfClosedAnnulus_closure _ (D.hdeg x) _ D.hr u hu
  have heA : closure A ⊆ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
  have hut : u ∈ e.target := heA hucl
  let K := (S.w x).symm '' closure (rf4_innerDisc (D.deg x) D.r (ε x))
  have hK : IsCompact K := (rf4_innerDisc_closure_compact _ (D.hdeg x) _ _).image_of_continuousOn
    ((S.w x).continuousOn_symm.mono (S.w_target x))
  have hAK : e.symm '' A ⊆ K := by
    intro p hp
    have hp' : p ∈ S.h '' ((D.P.chart (D.ann x)).symm '' A) := by
      obtain ⟨v, hv, rfl⟩ := hp
      exact ⟨(D.P.chart (D.ann x)).symm v, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨v, hv, rfl⟩ := rf4_annulus_in_inner S x hp'
    exact ⟨v, subset_closure hv, rfl⟩
  have hpK : e.symm u ∈ K :=
    (closure_minimal hAK hK.isClosed)
      ((e.continuousAt_symm hut).continuousWithinAt.mem_closure_image hucl)
  have hps : e.symm u ∈ (S.w x).source := by
    obtain ⟨v, hv, hev⟩ := hpK
    exact hev ▸ (S.w x).map_target (S.w_target x hv)
  haveI : NeBot (𝓝[A] u) := mem_closure_iff_nhdsWithin_neBot.mp hucl
  let F : ℂ → ℂ := fun z ↦ S.w x (e.symm z) ^ D.deg x + ε x
  have hF : ContinuousAt F u :=
    (((S.w x).continuousAt hps).comp (e.continuousAt_symm hut)).pow _ |>.add continuousAt_const
  have hG : ContinuousAt (fun z : ℂ ↦ z ^ D.deg x) u := by fun_prop
  have heq : F =ᶠ[𝓝[A] u] fun z ↦ z ^ D.deg x := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hg := (S.glue x z hz).2
    have hp := (rf4_sector_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
      (S.small x) z hz (fun _ _ ↦ 0)).1
    change S.w x (S.h ((D.P.chart (D.ann x)).symm z)) ^ D.deg x + ε x = _
    rw [hg, hp, sub_add_cancel]
  have hlim : Tendsto F (𝓝[A] u) (𝓝 (u ^ D.deg x)) := by
    rw [Filter.tendsto_congr' heq]
    exact hG.tendsto.mono_left nhdsWithin_le_nhds
  have hpow : F u = u ^ D.deg x :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) hlim
  have hi : S.w x (e.symm u) ∈ rf4_innerDisc (D.deg x) D.r (ε x) := by
    change ‖F u‖ < 2 * D.r
    rw [hpow, norm_pow]
    exact hu.2
  exact ⟨S.w x (e.symm u), hi, (S.w x).left_inv hps⟩

theorem rf4_innerBoundary_not_outer {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) (x : Fin D.m)
    (u : ℂ) (hu : ‖u‖ ^ D.deg x = D.r) :
    S.h ((D.P.chart (D.ann x)).symm u) ∉ S.h '' O := by
  have hu' : D.r ≤ ‖u‖ ^ D.deg x ∧ ‖u‖ ^ D.deg x < 2 * D.r := by
    rw [hu]
    exact ⟨le_rfl, by linarith [D.hr]⟩
  have hi := rf4_halfClosedAnnulus_inner S x u hu'
  intro ho
  have ha := (Set.ext_iff.mp (S.overlap x)
    (S.h ((D.P.chart (D.ann x)).symm u))).mp ⟨ho, hi⟩
  obtain ⟨q, ⟨v, hv, hvq⟩, hqp⟩ := ha
  have hp : (D.P.chart (D.ann x)).symm v = (D.P.chart (D.ann x)).symm u :=
    S.h.injective ((congrArg S.h hvq).trans hqp)
  have hvt := D.P.contained (D.ann x) (subset_closure ((D.hann x).ge hv))
  have hut := D.P.contained (D.ann x)
    ((closure_mono (D.hann x).ge)
      (rf4_halfClosedAnnulus_closure _ (D.hdeg x) _ D.hr u hu'))
  have hvu : v = u := by
    simpa only [(D.P.chart (D.ann x)).right_inv hvt,
      (D.P.chart (D.ann x)).right_inv hut] using congrArg (D.P.chart (D.ann x)) hp
  have hlt : D.r < D.r := by simpa only [hvu, hu] using hv.1
  exact (lt_irrefl _) hlt

theorem rf4_annulus_closure_power {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) (x : Fin D.m)
    (u : ℂ) (hucl : u ∈ closure (b63r_annulus (D.deg x) D.r)) :
    S.h ((D.P.chart (D.ann x)).symm u) ∈ (S.w x).source ∧
      S.w x (S.h ((D.P.chart (D.ann x)).symm u)) ^ D.deg x + ε x = u ^ D.deg x := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  let A := b63r_annulus (D.deg x) D.r
  have heA : closure A ⊆ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact (closure_mono (D.hann x).ge).trans (D.P.contained (D.ann x))
  have hut : u ∈ e.target := heA hucl
  let K := (S.w x).symm '' closure (rf4_innerDisc (D.deg x) D.r (ε x))
  have hK : IsCompact K := (rf4_innerDisc_closure_compact _ (D.hdeg x) _ _).image_of_continuousOn
    ((S.w x).continuousOn_symm.mono (S.w_target x))
  have hAK : e.symm '' A ⊆ K := by
    intro p hp
    have hp' : p ∈ S.h '' ((D.P.chart (D.ann x)).symm '' A) := by
      obtain ⟨v, hv, rfl⟩ := hp
      exact ⟨(D.P.chart (D.ann x)).symm v, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨v, hv, rfl⟩ := rf4_annulus_in_inner S x hp'
    exact ⟨v, subset_closure hv, rfl⟩
  have hpK : e.symm u ∈ K :=
    (closure_minimal hAK hK.isClosed)
      ((e.continuousAt_symm hut).continuousWithinAt.mem_closure_image hucl)
  have hps : e.symm u ∈ (S.w x).source := by
    obtain ⟨v, hv, hev⟩ := hpK
    exact hev ▸ (S.w x).map_target (S.w_target x hv)
  haveI : NeBot (𝓝[A] u) := mem_closure_iff_nhdsWithin_neBot.mp hucl
  let F : ℂ → ℂ := fun z ↦ S.w x (e.symm z) ^ D.deg x + ε x
  have hF : ContinuousAt F u :=
    (((S.w x).continuousAt hps).comp (e.continuousAt_symm hut)).pow _ |>.add continuousAt_const
  have hG : ContinuousAt (fun z : ℂ ↦ z ^ D.deg x) u := by fun_prop
  have heq : F =ᶠ[𝓝[A] u] fun z ↦ z ^ D.deg x := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hg := (S.glue x z hz).2
    have hp := (rf4_sector_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
      (S.small x) z hz (fun _ _ ↦ 0)).1
    change S.w x (S.h ((D.P.chart (D.ann x)).symm z)) ^ D.deg x + ε x = _
    rw [hg, hp, sub_add_cancel]
  have hlim : Tendsto F (𝓝[A] u) (𝓝 (u ^ D.deg x)) := by
    rw [Filter.tendsto_congr' heq]
    exact hG.tendsto.mono_left nhdsWithin_le_nhds
  have hpow : F u = u ^ D.deg x :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds) hlim
  exact ⟨hps, hpow⟩

theorem rf4_closedAnnulus_subset_closure (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    rf4_closedAnnulus n r ⊆ closure (b63r_annulus n r) := by
  intro u hu
  by_cases h : ‖u‖ ^ n < 2 * r
  · exact rf4_halfClosedAnnulus_closure n hn r hr u ⟨hu.1, h⟩
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr (rf4_closedAnnulus_ne_zero hn hr hu)
  have hstrict : r < ‖u‖ ^ n := by linarith
  have hc : Continuous (fun t : ℝ ↦ (t : ℂ) * u) := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ) * u) (𝓝[<] 1) (𝓝 u) := by
    simpa only [Complex.ofReal_one, one_mul] using
      (hc.tendsto 1).mono_left (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have hL : ∀ᶠ t : ℝ in 𝓝 1, r < ‖(t : ℂ) * u‖ ^ n :=
    (isOpen_lt continuous_const
      (by fun_prop : Continuous (fun t : ℝ ↦ ‖(t : ℂ) * u‖ ^ n))).mem_nhds
      (by simpa only [Set.mem_setOf_eq, Complex.ofReal_one, one_mul] using hstrict)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, hL.filter_mono nhdsWithin_le_nhds,
    (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with t ht htl htpos
  change r < ‖(t : ℂ) * u‖ ^ n ∧ ‖(t : ℂ) * u‖ ^ n < 2 * r
  refine ⟨htl, ?_⟩
  have ht1 : t < 1 := ht
  have hpow : (t * ‖u‖) ^ n < ‖u‖ ^ n :=
    pow_lt_pow_left₀ (by nlinarith) (mul_nonneg htpos.le (norm_nonneg u)) (by omega)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    using hpow.trans_le hu.2

theorem rf4_outerBoundary_not_inner {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {ε : Fin D.m → ℂ} {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (S : rf4_Plumbing D ε X) (x : Fin D.m)
    (u : ℂ) (hu : ‖u‖ ^ D.deg x = 2 * D.r) :
    S.h ((D.P.chart (D.ann x)).symm u) ∉
      (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) := by
  have huc : u ∈ rf4_closedAnnulus (D.deg x) D.r := by
    change D.r ≤ ‖u‖ ^ D.deg x ∧ ‖u‖ ^ D.deg x ≤ 2 * D.r
    rw [hu]
    exact ⟨by linarith [D.hr], le_rfl⟩
  have hcl := rf4_closedAnnulus_subset_closure _ (D.hdeg x) _ D.hr huc
  have hpow := (rf4_annulus_closure_power S x u hcl).2
  rintro ⟨w, hw, heq⟩
  have hwt := S.w_target x (subset_closure hw)
  have hwp : S.w x (S.h ((D.P.chart (D.ann x)).symm u)) = w := by
    rw [← heq, (S.w x).right_inv hwt]
  rw [hwp] at hpow
  change ‖w ^ D.deg x + ε x‖ < 2 * D.r at hw
  rw [hpow, norm_pow, hu] at hw
  exact (lt_irrefl _) hw

end HodgeLean.Foundations.Program
