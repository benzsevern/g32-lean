import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRank
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreSucc

/-! # Fibre dimension loci: reduction to charts

The Cartan–Remmert locus `{x ∈ Z | k ≤ dim_x (Z ∩ f⁻¹(f x))}` of a holomorphic map of reduced
spaces is read, in a chart `c` at `x₀` and with the target chart map written as `G ∘ c` near `x₀`,
as the Euclidean locus `ancr_fibreLocus A G k` of the image `A = c(Z ∩ dom)`. Local holomorphic
equations of the Euclidean locus at every point of an open `O ⊆ ℂⁿ` (`ancr_LocEqOn`) give back a
closed analytic subset of the space. The case `k = 0` of the Euclidean statement is the set `A`
itself; the case `k + 1` is `ancr_cartan_remmert_euclid_succ`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations

universe u v

/-! ### Chart bookkeeping -/

section Chart

variable {X : Type u} [TopologicalSpace X]

/-- A chart map is continuous on its domain. -/
theorem ancr_chart_continuousOn (c : an_Chart X) : ContinuousOn c.toFun c.dom :=
  continuousOn_iff_continuous_domRestrict.mpr c.isEmbedding.continuous

/-- The points of the chart domain sent into an open set form an open set. -/
theorem ancr_chart_isOpen_inter_preimage (c : an_Chart X) {O : Set (Fin c.n → ℂ)}
    (hO : IsOpen O) : IsOpen (c.dom ∩ c.toFun ⁻¹' O) :=
  (ancr_chart_continuousOn c).isOpen_inter_preimage c.isOpen_dom hO

/-- A chart map is injective on its domain. -/
theorem ancr_chart_injOn (c : an_Chart X) : InjOn c.toFun c.dom := fun x hx y hy h ↦
  congrArg Subtype.val (c.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

/-- A neighbourhood of a point of the chart domain contains every point of the domain whose image
lies in some open neighbourhood of the image point: the chart is an embedding.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5. -/
theorem ancr_chart_nhds (c : an_Chart X) {x : X} (hx : x ∈ c.dom) {Ω : Set X}
    (hΩ : Ω ∈ 𝓝 x) :
    ∃ O : Set (Fin c.n → ℂ), IsOpen O ∧ c.toFun x ∈ O ∧
      ∀ y ∈ c.dom, c.toFun y ∈ O → y ∈ Ω := by
  have h1 : ((↑) : c.dom → X) ⁻¹' Ω ∈ 𝓝 (⟨x, hx⟩ : c.dom) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hΩ
  rw [c.isEmbedding.isInducing.nhds_eq_comap] at h1
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp h1
  obtain ⟨O, hOt, hO, hxO⟩ := mem_nhds_iff.mp ht
  exact ⟨O, hO, hxO, fun y hy hyO ↦
    hts (show (⟨y, hy⟩ : c.dom) ∈ c.dom.domRestrict c.toFun ⁻¹' t from hOt hyO)⟩

/-- A point of the chart domain lies in the local model. -/
theorem ancr_chart_mem_zeroLocus (c : an_Chart X) {x : X} (hx : x ∈ c.dom) :
    c.toFun x ∈ an_zeroLocus c.U c.eqns :=
  c.image_eq ▸ mem_image_of_mem _ hx

/-- A function holomorphic near the chart images of the points of `W ⊆ dom`, composed with the
chart map, is a holomorphic function on `W`: the atlas is analytic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 and §4.1. -/
theorem ancr_isHolFun_comp_chart (S : an_ReducedSpace X) (i : S.atlas.ι) {W : Set X}
    (hW : W ⊆ (S.atlas.chart i).dom) (H : (Fin (S.atlas.chart i).n → ℂ) → ℂ)
    (hH : ∀ y ∈ W, AnalyticAt ℂ H ((S.atlas.chart i).toFun y)) :
    S.IsHolFun (fun y : W ↦ H ((S.atlas.chart i).toFun y)) := by
  intro y l hyl
  obtain ⟨W', hW', hyW', T, hT, hTeq⟩ := S.isAnalytic l i y ⟨hW y.2, hyl⟩
  refine ⟨(S.atlas.chart l).dom ∩ (S.atlas.chart l).toFun ⁻¹' W',
    ancr_chart_isOpen_inter_preimage _ hW', ⟨hyl, hyW'⟩, fun z ↦ H (T z), ?_, ?_⟩
  · exact (hH y y.2).comp_of_eq (hT _ hyW') (hTeq y ⟨hW y.2, hyl⟩ hyW').symm
  · rintro y' ⟨⟨_, hy'W'⟩, hy'l⟩
    simp only [hTeq y' ⟨hW y'.2, hy'l⟩ hy'W']

variable {Y : Type v} [TopologicalSpace Y]

/-- A holomorphic map, read in a chart `i` at `x` and a chart `j` at `f x`, is near `c_i x` the
restriction of a holomorphic map of the ambient spaces.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 and §4.1. -/
theorem ancr_isHom_chart_rep (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) (i : S.atlas.ι) (j : T.atlas.ι) {x : X}
    (hxi : x ∈ (S.atlas.chart i).dom) (hxj : f x ∈ (T.atlas.chart j).dom) :
    ∃ O : Set (Fin (S.atlas.chart i).n → ℂ), IsOpen O ∧ (S.atlas.chart i).toFun x ∈ O ∧
      ∃ G : (Fin (S.atlas.chart i).n → ℂ) → (Fin (T.atlas.chart j).n → ℂ),
        AnalyticOnNhd ℂ G O ∧ ∀ y ∈ (S.atlas.chart i).dom, (S.atlas.chart i).toFun y ∈ O →
          f y ∈ (T.atlas.chart j).dom ∧
            (T.atlas.chart j).toFun (f y) = G ((S.atlas.chart i).toFun y) := by
  set ci := S.atlas.chart i
  set cj := T.atlas.chart j
  have hcoord : ∀ m : Fin cj.n, T.IsHolFun (fun y : cj.dom ↦ cj.toFun y m) := fun m ↦
    ancr_isHolFun_comp_chart T j subset_rfl (fun z ↦ z m) fun _ _ ↦
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin cj.n ↦ ℂ) m).analyticAt _
  have hpull : ∀ m : Fin cj.n, S.IsHolFun (fun y : f ⁻¹' cj.dom ↦ cj.toFun (f y) m) :=
    fun m ↦ hf.2 cj.dom cj.isOpen_dom _ (hcoord m)
  choose N hN hxN Gm hGm hGeq using fun m ↦ hpull m ⟨x, hxj⟩ i hxi
  set Ω : Set X := ci.dom ∩ f ⁻¹' cj.dom ∩ ⋂ m, N m
  have hΩ : Ω ∈ 𝓝 x :=
    ((ci.isOpen_dom.inter (cj.isOpen_dom.preimage hf.1)).inter
      (isOpen_iInter_of_finite hN)).mem_nhds ⟨⟨hxi, hxj⟩, mem_iInter.mpr hxN⟩
  obtain ⟨O1, hO1, hxO1, hO1Ω⟩ := ancr_chart_nhds ci hxi hΩ
  set G : (Fin ci.n → ℂ) → (Fin cj.n → ℂ) := fun z m ↦ Gm m z
  have hGa : AnalyticAt ℂ G (ci.toFun x) := AnalyticAt.pi hGm
  obtain ⟨O2, hO2sub, hO2, hxO2⟩ := mem_nhds_iff.mp hGa.eventually_analyticAt
  refine ⟨O1 ∩ O2, hO1.inter hO2, ⟨hxO1, hxO2⟩, G, fun z hz ↦ hO2sub hz.2, fun y hy hyO ↦ ?_⟩
  have hyΩ := hO1Ω y hy hyO.1
  refine ⟨hyΩ.1.2, funext fun m ↦ ?_⟩
  exact hGeq m ⟨y, hyΩ.1.2⟩ ⟨mem_iInter.mp hyΩ.2 m, hy⟩

end Chart

/-! ### The Euclidean statement -/

section Euclid

variable {n p : ℕ}

/-- **Cartan–Remmert in `ℂⁿ`, positive fibre dimension.** For `A` with local holomorphic
equations on an open `O ⊆ ℂⁿ` and `G` holomorphic on `O`, the points of `A` whose `G`-fibre has
local dimension at least `k + 1` again have local holomorphic equations on `O`.
Source: Cartan–Remmert; Fischer, *Complex Analytic Geometry*, LNM 538, §3.6; Grauert–Remmert,
*Coherent Analytic Sheaves*, §5.5 (semicontinuity of the fibre dimension). -/
theorem ancr_cartan_remmert_euclid_succ (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (A : Set (Fin n → ℂ)) (hA : ancr_LocEqOn O A) (G : (Fin n → ℂ) → (Fin p → ℂ))
    (hG : AnalyticOnNhd ℂ G O) (k : ℕ) :
    ancr_LocEqOn O (ancr_fibreLocus A G (k + 1)) :=
  ancrs_locEqOn_fibreLocus O hO A hA G hG (k + 1)

/-- **Cartan–Remmert in `ℂⁿ`.**
Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6. -/
theorem ancr_cartan_remmert_euclid (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (A : Set (Fin n → ℂ)) (hA : ancr_LocEqOn O A) (G : (Fin n → ℂ) → (Fin p → ℂ))
    (hG : AnalyticOnNhd ℂ G O) (k : ℕ) :
    ancr_LocEqOn O (ancr_fibreLocus A G k) := by
  cases k with
  | zero => rw [ancr_fibreLocus_zero]; exact hA
  | succ k => exact ancr_cartan_remmert_euclid_succ O hO A hA G hG k

/-- Germs of sets that agree on a neighbourhood of the anchor are equal. -/
theorem ancr_germ_congr {A B O : Set (Fin n → ℂ)} {x : Fin n → ℂ} (hO : O ∈ 𝓝 x)
    (h : A ∩ O = B ∩ O) : adim2_germ n A x = adim2_germ n B x := by
  unfold adim2_germ
  apply Filter.Germ.coe_eq.mpr
  have hO' : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), x + z ∈ O := by
    have : Tendsto (fun z : Fin n → ℂ ↦ x + z) (𝓝 0) (𝓝 x) := by
      have := ((continuous_const_add x).tendsto (0 : Fin n → ℂ))
      rwa [add_zero] at this
    exact this hO
  filter_upwards [hO'] with z hz
  apply propext
  constructor
  · intro hA; exact (h.subset ⟨hA, hz⟩).1
  · intro hB; exact (h.symm.subset ⟨hB, hz⟩).1

end Euclid

/-! ### Back and forth between the space and its charts -/

section Transfer

variable {X : Type u} [TopologicalSpace X]

/-- A subset which, near every point, is read in some chart as a set with local holomorphic
equations on an open subset of `ℂⁿ` is closed analytic.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.6 (analyticity is local). -/
theorem ancr_isClosedAnalytic_of_chart (S : an_ReducedSpace X) (E : Set X)
    (h : ∀ x₀ : X, ∃ i : S.atlas.ι, x₀ ∈ (S.atlas.chart i).dom ∧
      ∃ O : Set (Fin (S.atlas.chart i).n → ℂ), IsOpen O ∧ (S.atlas.chart i).toFun x₀ ∈ O ∧
        ∃ B : Set (Fin (S.atlas.chart i).n → ℂ), ancr_LocEqOn O B ∧
          ∀ y ∈ (S.atlas.chart i).dom, (S.atlas.chart i).toFun y ∈ O →
            (y ∈ E ↔ (S.atlas.chart i).toFun y ∈ B)) :
    an_IsClosedAnalytic S E := by
  classical
  refine ⟨isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x₀ hx₀ ↦ ?_), fun x₀ hx₀ ↦ ?_⟩
  · obtain ⟨i, hxi, O, hO, hxO, B, hB, hiff⟩ := h x₀
    obtain ⟨W, hW, hxW, hWO, s, hs, hsB⟩ := hB _ hxO
    have hnot : ¬ ∀ g ∈ s, g ((S.atlas.chart i).toFun x₀) = 0 := fun hall ↦
      hx₀ ((hiff x₀ hxi hxO).mpr ((hsB _ hxW).mpr hall))
    push Not at hnot
    obtain ⟨g, hgs, hg0⟩ := hnot
    have hW' : IsOpen (W ∩ g ⁻¹' {0}ᶜ) :=
      (hs g hgs).continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
    refine ⟨(S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹' (W ∩ g ⁻¹' {0}ᶜ), ?_,
      ancr_chart_isOpen_inter_preimage _ hW', ⟨hxi, hxW, hg0⟩⟩
    rintro y ⟨hyi, hyW, hyg⟩ hyE
    exact hyg ((hsB _ hyW).mp ((hiff y hyi (hWO hyW)).mp hyE) g hgs)
  · obtain ⟨i, hxi, O, hO, hxO, B, hB, hiff⟩ := h x₀
    obtain ⟨W, hW, hxW, hWO, s, hs, hsB⟩ := hB _ hxO
    set Wx : Set X := (S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹' W
    let e := s.equivFin
    refine ⟨Wx, ancr_chart_isOpen_inter_preimage _ hW, ⟨hxi, hxW⟩, s.card,
      fun l y ↦ (e.symm l : (Fin (S.atlas.chart i).n → ℂ) → ℂ) ((S.atlas.chart i).toFun y),
      fun l ↦ ancr_isHolFun_comp_chart S i inter_subset_left _
        fun y hy ↦ hs _ (e.symm l).2 _ hy.2, fun y ↦ ?_⟩
    rw [hiff y y.2.1 (hWO y.2.2), hsB _ y.2.2]
    constructor
    · intro hall l
      exact hall _ (e.symm l).2
    · intro hall g hgs
      simpa using hall (e ⟨g, hgs⟩)

/-- The chart image of a closed analytic subset has local holomorphic equations on every open
subset of the ambient open set of the model.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 and §1.1.6. -/
theorem ancr_locEqOn_chart_image (S : an_ReducedSpace X) {Z : Set X}
    (hZ : an_IsClosedAnalytic S Z) (i : S.atlas.ι) {O : Set (Fin (S.atlas.chart i).n → ℂ)}
    (hO : IsOpen O) (hOU : O ⊆ (S.atlas.chart i).U) :
    ancr_LocEqOn O ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom)) := by
  classical
  revert O
  set c := S.atlas.chart i
  intro O hO hOU
  -- the empty case: an open neighbourhood avoiding the image
  have hempty : ∀ z ∈ O, ∀ W : Set (Fin c.n → ℂ), IsOpen W → z ∈ W →
      (∀ w ∈ W, w ∉ c.toFun '' (Z ∩ c.dom)) →
      ∃ W : Set (Fin c.n → ℂ), IsOpen W ∧ z ∈ W ∧ W ⊆ O ∧
        ∃ s : Finset ((Fin c.n → ℂ) → ℂ), (∀ h ∈ s, AnalyticOnNhd ℂ h W) ∧
          ∀ w ∈ W, (w ∈ c.toFun '' (Z ∩ c.dom) ↔ ∀ h ∈ s, h w = 0) := by
    intro z hz W hW hzW hnot
    refine ⟨W ∩ O, hW.inter hO, ⟨hzW, hz⟩, inter_subset_right, {fun _ ↦ 1},
      fun h hh ↦ by rw [Finset.mem_singleton.mp hh]; exact analyticOnNhd_const,
      fun w hw ↦ ?_⟩
    simp only [Finset.mem_singleton, forall_eq, one_ne_zero, iff_false]
    exact hnot w hw.1
  have hcont : ContinuousOn c.eqns c.U := c.analyticOnNhd_eqns.continuousOn
  intro z hz
  by_cases hzM : z ∈ c.toFun '' c.dom
  swap
  · -- off the model
    rw [c.image_eq] at hzM
    have hne : c.eqns z ≠ 0 := fun h0 ↦ hzM ⟨hOU hz, h0⟩
    refine hempty z hz (c.U ∩ c.eqns ⁻¹' {0}ᶜ)
      (hcont.isOpen_inter_preimage c.isOpen_U isOpen_compl_singleton) ⟨hOU hz, hne⟩ ?_
    rintro w ⟨_, hw⟩ ⟨y, ⟨_, hy⟩, rfl⟩
    exact hw (ancr_chart_mem_zeroLocus c hy).2
  obtain ⟨y, hy, rfl⟩ := hzM
  by_cases hyZ : y ∉ Z
  · obtain ⟨O', hO', hyO', hO'Z⟩ := ancr_chart_nhds c hy (hZ.1.isOpen_compl.mem_nhds hyZ)
    refine hempty _ hz O' hO' hyO' ?_
    rintro w hw ⟨y', ⟨hy'Z, hy'⟩, rfl⟩
    exact hO'Z y' hy' hw hy'Z
  push Not at hyZ
  obtain ⟨Wz, hWz, hyWz, q, g, hg, hgiff⟩ := hZ.2 y hyZ
  choose N hN hyN Gl hGl hGeq using fun l ↦ hg l ⟨y, hyWz⟩ i hy
  have hΩ : Wz ∩ ⋂ l, N l ∈ 𝓝 y :=
    (hWz.inter (isOpen_iInter_of_finite hN)).mem_nhds ⟨hyWz, mem_iInter.mpr hyN⟩
  obtain ⟨O', hO', hyO', hO'Ω⟩ := ancr_chart_nhds c hy hΩ
  choose R hRsub hR hyR using fun l ↦ mem_nhds_iff.mp (hGl l).eventually_analyticAt
  set W : Set (Fin c.n → ℂ) := O ∩ O' ∩ ⋂ l, R l
  have hW : IsOpen W := (hO.inter hO').inter (isOpen_iInter_of_finite hR)
  refine ⟨W, hW, ⟨⟨hz, hyO'⟩, mem_iInter.mpr hyR⟩, fun w hw ↦ hw.1.1,
    Finset.univ.image (fun m : Fin c.k ↦ fun w ↦ c.eqns w m) ∪ Finset.univ.image Gl,
    ?_, fun w hw ↦ ?_⟩
  · intro h hh
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hh
      intro w hw
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.k ↦ ℂ) m).analyticAt _).comp
        (c.analyticOnNhd_eqns w (hOU hw.1.1))
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hh
      intro w hw
      exact hRsub l (mem_iInter.mp hw.2 l)
  have hfwd : ∀ y' ∈ c.dom, c.toFun y' ∈ O' → (y' ∈ Z ↔ ∀ l, Gl l (c.toFun y') = 0) := by
    intro y' hy' hy'O
    have hΩ' := hO'Ω y' hy' hy'O
    rw [hgiff ⟨y', hΩ'.1⟩]
    refine forall_congr' fun l ↦ ?_
    rw [hGeq l ⟨y', hΩ'.1⟩ ⟨mem_iInter.mp hΩ'.2 l, hy'⟩]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y', ⟨hy'Z, hy'⟩, rfl⟩ h (⟨m, rfl⟩ | ⟨l, rfl⟩)
    · exact congrFun (ancr_chart_mem_zeroLocus c hy').2 m
    · exact (hfwd y' hy' hw.1.2).mp hy'Z l
  · intro hall
    have hwM : w ∈ an_zeroLocus c.U c.eqns :=
      ⟨hOU hw.1.1, funext fun m ↦ hall _ (Or.inl ⟨m, rfl⟩)⟩
    rw [← c.image_eq] at hwM
    obtain ⟨y', hy', rfl⟩ := hwM
    exact ⟨y', ⟨(hfwd y' hy' hw.1.2).mpr fun l ↦ hall _ (Or.inr ⟨l, rfl⟩), hy'⟩, rfl⟩

end Transfer

/-! ### Cartan–Remmert from the Euclidean statement -/

section Reduction

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- **Cartan–Remmert, chart reduction.** Given the independence of the local dimension from the
chart (the statement of `an_dimAt_eq_chart`), the fibre dimension loci of a holomorphic map are
closed analytic, by the Euclidean statement `ancr_cartan_remmert_euclid` in a chart at each point.
Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6; Grauert–Remmert, *Coherent Analytic
Sheaves*, §1.1.5. -/
theorem ancr_cartan_remmert_of_chart (S : an_ReducedSpace X) (T : an_ReducedSpace Y)
    (f : X → Y) (hf : an_IsHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (k : ℕ)
    (hchart : ∀ (Z' : Set X) (i : S.atlas.ι) {x : X}, x ∈ (S.atlas.chart i).dom →
      an_dimAt S Z' x = adim2_dimension (S.atlas.chart i).n
        (adim2_germ (S.atlas.chart i).n
          ((S.atlas.chart i).toFun '' (Z' ∩ (S.atlas.chart i).dom))
          ((S.atlas.chart i).toFun x))) :
    an_IsClosedAnalytic S
      {x | x ∈ Z ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (Z ∩ f ⁻¹' {f x}) x} := by
  apply ancr_isClosedAnalytic_of_chart
  intro x₀
  set i := S.atlas.chartAt x₀
  set j := T.atlas.chartAt (f x₀)
  set c := S.atlas.chart i
  set cj := T.atlas.chart j
  have hxi : x₀ ∈ c.dom := S.atlas.mem_chartAt x₀
  obtain ⟨O1, hO1, hxO1, G, hG, hGrep⟩ :=
    ancr_isHom_chart_rep S T hf i j hxi (T.atlas.mem_chartAt (f x₀))
  set O := O1 ∩ c.U
  have hO : IsOpen O := hO1.inter c.isOpen_U
  set A := c.toFun '' (Z ∩ c.dom)
  have hA : ancr_LocEqOn O A := ancr_locEqOn_chart_image S hZ i hO inter_subset_right
  refine ⟨i, hxi, O, hO, ⟨hxO1, (ancr_chart_mem_zeroLocus c hxi).1⟩,
    ancr_fibreLocus A G k,
    ancr_cartan_remmert_euclid O hO A hA G (hG.mono inter_subset_left) k, fun y hy hyO ↦ ?_⟩
  have hZiff : y ∈ Z ↔ c.toFun y ∈ A := by
    refine ⟨fun h ↦ ⟨y, ⟨h, hy⟩, rfl⟩, ?_⟩
    rintro ⟨y', ⟨hy'Z, hy'⟩, hyy'⟩
    rwa [← ancr_chart_injOn c hy' hy hyy']
  have hset : (c.toFun '' ((Z ∩ f ⁻¹' {f y}) ∩ c.dom)) ∩ O =
      (A ∩ G ⁻¹' {G (c.toFun y)}) ∩ O := by
    ext w
    constructor
    · rintro ⟨⟨y', ⟨⟨hy'Z, hy'f⟩, hy'⟩, rfl⟩, hwO⟩
      refine ⟨⟨⟨y', ⟨hy'Z, hy'⟩, rfl⟩, ?_⟩, hwO⟩
      change G (c.toFun y') = G (c.toFun y)
      rw [← (hGrep y' hy' hwO.1).2, ← (hGrep y hy hyO.1).2, mem_singleton_iff.mp hy'f]
    · rintro ⟨⟨⟨y', ⟨hy'Z, hy'⟩, rfl⟩, hGw⟩, hwO⟩
      refine ⟨⟨y', ⟨⟨hy'Z, ?_⟩, hy'⟩, rfl⟩, hwO⟩
      have h1 := hGrep y' hy' hwO.1
      have h2 := hGrep y hy hyO.1
      have heq : cj.toFun (f y') = cj.toFun (f y) := by
        rw [h1.2, h2.2]; exact hGw
      exact ancr_chart_injOn cj h1.1 h2.1 heq
  change (y ∈ Z ∧ _) ↔ (c.toFun y ∈ A ∧ _)
  rw [hchart _ i hy, ancr_germ_congr (hO.mem_nhds hyO) hset, hZiff]

end Reduction

end HodgeLean.Foundations.Analytic
