import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertProper

/-! # Remmert's proper mapping theorem: the induction

Lane `an-rem`, prefix `anrem_`. Remmert's theorem for closed analytic sets of bounded dimension, by
induction on the dimension and, inside, by descending induction on the fibre dimension: over the
complement of the image of the locus of larger fibres the image is analytic of the expected
dimension (`anrem_partA`); across that image it is the union of the image itself, the closure of the
top-dimensional part (a local Remmert–Stein extension) and the image of the lower-dimensional part
of the locus (the induction hypothesis), by the bound `dim ≤ dim image + dim fibre`. The
Cartan–Remmert theorem and the local Remmert–Stein extension enter as the inputs
`anrem_CartanRemmertStmt` and `anrem_LocalRSStmt` (Remmert, Math. Ann. 133 (1957); Narasimhan,
LNM 25, Ch. VII). HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

universe u v

/-- The Cartan–Remmert theorem on fibre dimension, as an input. -/
def anrem_CartanRemmertStmt.{u', v'} : Prop :=
  ∀ {X : Type u'} {Y : Type v'} [TopologicalSpace X] [TopologicalSpace Y] (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) (f : X → Y), an_IsHom S T f → ∀ {Z : Set X},
    an_IsClosedAnalytic S Z → ∀ k : ℕ,
      an_IsClosedAnalytic S {x | x ∈ Z ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (Z ∩ f ⁻¹' {f x}) x}

/-- A local form of the Remmert–Stein extension theorem, as an input until proved. -/
def anrem_LocalRSStmt : Prop :=
  ∀ (n d : ℕ) (T B Ω : Set (Fin n → ℂ)), IsOpen Ω → (∀ z ∈ Ω, anrem_LocEq T z) →
    (∀ z ∈ T ∩ Ω, adim2_dimension n (adim2_germ n T z) ≤ (d : WithBot ℕ∞)) → B ⊆ Ω \ T →
    (∀ z ∈ Ω \ T, anrem_LocEq B z) →
    (∀ z ∈ B, ∀ Q ∈ (adim2_ideal n (adim2_germ n B z)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞)) →
    ∀ a ∈ T ∩ Ω, anrem_LocEq (closure B) a

theorem anrem_le_of_not_succ_le {a : WithBot ℕ∞} {k : ℕ}
    (h : ¬ ((k + 1 : ℕ) : WithBot ℕ∞) ≤ a) : a ≤ (k : WithBot ℕ∞) := by
  by_contra h'
  exact h (anrem_succ_le_of_not_le h')

theorem anrem_eventually_not_mem {n : ℕ} {S : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (hloc : anrem_LocEq S z) (hz : z ∉ S) : ∀ᶠ w in 𝓝 z, w ∉ S := by
  obtain ⟨U, hU, hzU, m, f, hf, hUS⟩ := hloc
  have : ¬ ∀ j, f j z = 0 := fun h' ↦ hz ((hUS z hzU).2 h')
  push Not at this
  obtain ⟨j, hj⟩ := this
  filter_upwards [Filter.Eventually.and (hU.mem_nhds hzU)
    ((hf j z hzU).continuousAt.eventually_ne hj)] with w hw hwS
  exact hw.2 ((hUS w hw.1).1 hwS j)

theorem anrem_dimension_le_of_not_mem {n : ℕ} {S : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (hloc : anrem_LocEq S z) (hz : z ∉ S) (d : WithBot ℕ∞) :
    adim2_dimension n (adim2_germ n S z) ≤ d :=
  (anrem_dimension_le_iff S z d).2 fun Q hQ ↦ by
    rw [anrem_minimalPrimes_of_not_mem hloc hz] at hQ; exact hQ.elim

theorem anrem_locEq_of_eventually_not_mem {n : ℕ} {S : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (h : ∀ᶠ w in 𝓝 z, w ∉ S) : anrem_LocEq S z := by
  obtain ⟨O, hOsub, hO, hzO⟩ := eventually_nhds_iff.1 h
  exact ⟨O, hO, hzO, 1, fun _ _ ↦ 1, fun _ ↦ analyticOnNhd_const,
    fun w hw ↦ by simp only [one_ne_zero, forall_const, iff_false]; exact hOsub w hw⟩

theorem anrem_isOpen_diff_of_locEq {n : ℕ} {Ω S : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (h : ∀ z ∈ Ω, anrem_LocEq S z) : IsOpen (Ω \ S) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  filter_upwards [anrem_eventually_not_mem (h z hz.1) hz.2, hΩ.mem_nhds hz.1] with w h1 h2
  exact ⟨h2, h1⟩

theorem anrem_locEq_union {n : ℕ} {A B : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (hA : anrem_LocEq A z) (hB : anrem_LocEq B z) : anrem_LocEq (A ∪ B) z := by
  have := anrem_locEq_biUnion (S := fun b : Bool ↦ cond b A B) Finset.univ
    (fun b _ ↦ by cases b <;> assumption)
  convert this using 1
  ext w; simp [or_comm]

section Charts

variable {Z : Type u} [TopologicalSpace Z]

/-- The local model is closed in the open set carrying it. -/
theorem anrem_chart_model_closed (c : an_Chart Z) {z : Fin c.n → ℂ} (hz : z ∈ c.U)
    (hzc : z ∈ closure (c.toFun '' c.dom)) : z ∈ c.toFun '' c.dom := by
  by_contra hzm
  rw [c.image_eq] at hzm
  have : ¬ c.eqns z = 0 := fun h ↦ hzm ⟨hz, h⟩
  obtain ⟨l, hl⟩ : ∃ l, c.eqns z l ≠ 0 := by
    by_contra h; push Not at h; exact this (funext h)
  have hcont : ContinuousAt (fun w ↦ c.eqns w l) z :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.k ↦ ℂ) l).analyticAt _).comp
      (c.analyticOnNhd_eqns z hz) |>.continuousAt
  obtain ⟨w, hwm, hw⟩ := (mem_closure_iff_frequently.1 hzc |>.and_eventually
    (hcont.eventually_ne hl)).exists
  rw [c.image_eq] at hwm
  exact hw (congrFun hwm.2 l)

/-- Local equations of a chart image from local analyticity at the points of the chart domain. -/
theorem anrem_chart_image_locEq' (S : an_ReducedSpace Z) (A : Set Z) (i : S.atlas.ι)
    {z : Fin (S.atlas.chart i).n → ℂ} (hz : z ∈ (S.atlas.chart i).U)
    (h : ∀ y ∈ (S.atlas.chart i).dom, (S.atlas.chart i).toFun y = z → anrem_AnNear S A y) :
    anrem_LocEq ((S.atlas.chart i).toFun '' (A ∩ (S.atlas.chart i).dom)) z := by
  by_cases hzm : z ∈ (S.atlas.chart i).toFun '' (S.atlas.chart i).dom
  · obtain ⟨y, hy, rfl⟩ := hzm
    exact anrem_anNear_chart S (h y hy rfl) i hy
  · refine anrem_locEq_of_eventually_not_mem ?_
    have hc : IsClosed (closure ((S.atlas.chart i).toFun '' (S.atlas.chart i).dom)) :=
      isClosed_closure
    have hnot : z ∉ closure ((S.atlas.chart i).toFun '' (S.atlas.chart i).dom) := fun h' ↦
      hzm (anrem_chart_model_closed _ hz h')
    filter_upwards [hc.isOpen_compl.mem_nhds hnot] with w hw hwA
    obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hwA
    exact hw (subset_closure (mem_image_of_mem _ hy))

end Charts

section Main

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

theorem anrem_fibreLocus_facts (hCR : anrem_CartanRemmertStmt.{u, v}) (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) {f : X → Y} (hf : an_IsHom S T f) {W : Set X}
    (hW : an_IsClosedAnalytic S W) {p : ℕ} (hWdim : ∀ x ∈ W, an_dimAt S W x ≤ (p : WithBot ℕ∞)) :
    (∀ k, an_IsClosedAnalytic S (anrem_fibreLocus S f W k)) ∧
    (∀ k, anrem_fibreLocus S f W k ⊆ W) ∧
    (∀ k, anrem_fibreLocus S f W (k + 1) ⊆ anrem_fibreLocus S f W k) ∧
    (∀ k, p < k → anrem_fibreLocus S f W k = ∅) ∧
    anrem_fibreLocus S f W 0 = W ∧
    (∀ k, ∀ x ∈ anrem_fibreLocus S f W k,
      an_dimAt S (anrem_fibreLocus S f W k) x ≤ (p : WithBot ℕ∞)) := by
  refine ⟨fun k ↦ hCR S T f hf hW k, fun k x hx ↦ hx.1, fun k x hx ↦ ⟨hx.1, ?_⟩,
    fun k hk ↦ ?_, ?_, fun k x hx ↦ (anrem_dimAt_mono S (fun z hz ↦ hz.1) x).trans
      (hWdim x hx.1)⟩
  · refine le_trans ?_ hx.2
    exact_mod_cast Nat.le_succ k
  · ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    have h1 := hx.2.trans ((anrem_dimAt_mono S inter_subset_left x).trans (hWdim x hx.1))
    have : k ≤ p := by exact_mod_cast h1
    omega
  · ext x
    refine ⟨fun h ↦ h.1, fun hx ↦ ⟨hx, ?_⟩⟩
    set c := S.atlas.chart (S.atlas.chartAt x)
    have hxc : c.toFun x ∈ c.toFun '' (W ∩ f ⁻¹' {f x} ∩ c.dom) :=
      ⟨x, ⟨⟨hx, rfl⟩, S.atlas.mem_chartAt x⟩, rfl⟩
    have : Nontrivial (AnalyticGerm c.n ⧸ adim2_ideal c.n (adim2_germ c.n
        (c.toFun '' (W ∩ f ⁻¹' {f x} ∩ c.dom)) (c.toFun x))) :=
      Ideal.Quotient.nontrivial_iff.2 (adim9b_germ_ideal_ne_top _ _ _ hxc)
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := AnalyticGerm c.n ⧸ adim2_ideal c.n
      (adim2_germ c.n (c.toFun '' (W ∩ f ⁻¹' {f x} ∩ c.dom)) (c.toFun x)))
    exact_mod_cast h0

/-- **The step of the descending induction on fibre dimension.** -/
theorem anrem_descend_step (hFM : anrem_FiniteMappingStmt) (hCS : anrem_ClosedSubspaceStmt)
    (hDCu : anrem_DimChartStmt.{u}) (hDCv : anrem_DimChartStmt.{v})
    (hCR : anrem_CartanRemmertStmt.{u, v}) (hRS : anrem_LocalRSStmt)
    (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y} (hf : an_IsProperHom S T f)
    {p : ℕ} (IH : ∀ e : ℕ, p = e + 1 → ∀ W' : Set X, an_IsClosedAnalytic S W' →
      (∀ x ∈ W', an_dimAt S W' x ≤ (e : WithBot ℕ∞)) → an_IsClosedAnalytic T (f '' W'))
    {W : Set X} (hW : an_IsClosedAnalytic S W)
    (hWdim : ∀ x ∈ W, an_dimAt S W x ≤ (p : WithBot ℕ∞)) {k : ℕ}
    (hD : ∀ j, k < j → an_IsClosedAnalytic T (f '' anrem_fibreLocus S f W j) ∧
      ∀ y ∈ f '' anrem_fibreLocus S f W j,
        an_dimAt T (f '' anrem_fibreLocus S f W j) y ≤ ((p - j : ℕ) : WithBot ℕ∞)) :
    an_IsClosedAnalytic T (f '' anrem_fibreLocus S f W k) ∧
      ∀ y ∈ f '' anrem_fibreLocus S f W k,
        an_dimAt T (f '' anrem_fibreLocus S f W k) y ≤ ((p - k : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨hFc, hFW, hFmono, hFempty, -, hFdim⟩ := anrem_fibreLocus_facts hCR S T hf.2 hW hWdim
  set F := anrem_fibreLocus S f W
  have hT₀ := hD (k + 1) (Nat.lt_succ_self k)
  -- over the complement of the image of the next locus, the fibres have dimension `k`
  have hfibk : ∀ x ∈ F k, f x ∉ f '' F (k + 1) →
      an_dimAt S (F k ∩ f ⁻¹' {f x}) x = (k : WithBot ℕ∞) := by
    intro x hx hfx
    have hx1 : x ∉ F (k + 1) := fun h ↦ hfx ⟨x, h, rfl⟩
    have hle : an_dimAt S (W ∩ f ⁻¹' {f x}) x ≤ (k : WithBot ℕ∞) :=
      anrem_le_of_not_succ_le fun h ↦ hx1 ⟨hFW k hx, by exact_mod_cast h⟩
    refine le_antisymm ((anrem_dimAt_mono S (inter_subset_inter_left _ (hFW k)) x).trans hle) ?_
    exact_mod_cast anrem_fibreLocus_dim hDCu S T hf.2 hW k hx.1 hx.2
  have hPA : ∀ y, y ∉ f '' F (k + 1) → anrem_AnNear T (f '' F k) y ∧
      an_dimAt T (f '' F k) y ≤ ((p - k : ℕ) : WithBot ℕ∞) := fun y hy ↦
    anrem_partA hFM hCS hDCu S T hf (hFc k) hT₀.1.1.isOpen_compl
      (fun x hx ↦ by exact_mod_cast hfibk x hx.1 hx.2) (fun x hx ↦ hFdim k x hx.1) hy
  have hclosed : IsClosed (f '' F k) := hf.1.isClosedMap _ (hFc k).1
  have hAn : an_IsClosedAnalytic T (f '' F k) := by
    refine ⟨hclosed, fun a ha ↦ ?_⟩
    by_cases haT : a ∉ f '' F (k + 1)
    · exact (hPA a haT).1
    push Not at haT
    -- the exceptional image is nonempty, so `k < p`
    obtain ⟨x₁, hx₁, hfx₁⟩ := haT
    have hkp : k + 1 ≤ p := by
      by_contra h
      rw [hFempty (k + 1) (by omega)] at hx₁
      exact hx₁
    obtain ⟨r, hr⟩ : ∃ r, p = k + 1 + r := ⟨p - (k + 1), by omega⟩
    have hpk : p - k = r + 1 := by omega
    set jd := T.atlas.chartAt a
    have had : a ∈ (T.atlas.chart jd).dom := T.atlas.mem_chartAt a
    set Ω := (T.atlas.chart jd).U
    have hΩ : IsOpen Ω := (T.atlas.chart jd).isOpen_U
    set Im := (T.atlas.chart jd).toFun '' (f '' F k ∩ (T.atlas.chart jd).dom)
    set T' := (T.atlas.chart jd).toFun '' (f '' F (k + 1) ∩ (T.atlas.chart jd).dom)
    have hdU : ∀ y ∈ (T.atlas.chart jd).dom, (T.atlas.chart jd).toFun y ∈ Ω := by
      intro y hy
      have : (T.atlas.chart jd).toFun y ∈ (T.atlas.chart jd).toFun '' (T.atlas.chart jd).dom :=
        mem_image_of_mem _ hy
      rw [(T.atlas.chart jd).image_eq] at this; exact this.1
    have hT'loc : ∀ z ∈ Ω, anrem_LocEq T' z := fun z hz ↦
      anrem_chart_image_locEq T hT₀.1 jd hz
    have hT'dim : ∀ z ∈ T' ∩ Ω, adim2_dimension _ (adim2_germ _ T' z) ≤ (r : WithBot ℕ∞) := by
      rintro _ ⟨⟨y', hy', rfl⟩, -⟩
      rw [← hDCv T _ jd hy'.2]
      have := hT₀.2 y' hy'.1
      rwa [show p - (k + 1) = r by omega] at this
    have hnotT' : ∀ y ∈ (T.atlas.chart jd).dom, (T.atlas.chart jd).toFun y ∉ T' →
        y ∉ f '' F (k + 1) := fun y hy h h' ↦ h ⟨y, ⟨h', hy⟩, rfl⟩
    have hImloc : ∀ z ∈ Ω \ T', anrem_LocEq Im z := by
      rintro z ⟨hz, hzT⟩
      refine anrem_chart_image_locEq' T _ jd hz fun y hy hyz ↦ ?_
      exact (hPA y (hnotT' y hy (hyz ▸ hzT))).1
    have hΩT : IsOpen (Ω \ T') := anrem_isOpen_diff_of_locEq hΩ hT'loc
    have hImdim : ∀ z ∈ Ω \ T',
        adim2_dimension _ (adim2_germ _ Im z) ≤ ((r + 1 : ℕ) : WithBot ℕ∞) := by
      intro z hz
      by_cases hzI : z ∈ Im
      · obtain ⟨y, hy, rfl⟩ := hzI
        rw [← hDCv T _ jd hy.2, ← hpk]
        exact (hPA y (hnotT' y hy.2 hz.2)).2
      · exact anrem_dimension_le_of_not_mem (hImloc z hz) hzI _
    -- the top-dimensional part of the image off the exceptional set
    set B := {z | z ∈ Im ∧ z ∉ T' ∧ ((r + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension _ (adim2_germ _ Im z)}
    have hImΩ : Im ⊆ Ω := by rintro _ ⟨y, hy, rfl⟩; exact hdU y hy.2
    have hBsub : B ⊆ Ω \ T' := fun z hz ↦ ⟨hImΩ hz.1, hz.2.1⟩
    have hsplit : ∀ z ∈ Ω \ T', z ∈ Im →
        anrem_LocEq {w | w ∈ Im ∧ ((r + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension _ (adim2_germ _ Im w)} z ∧
        (∀ᶠ w in 𝓝 z, w ∈ {w | w ∈ Im ∧ ((r + 1 : ℕ) : WithBot ℕ∞) ≤
            adim2_dimension _ (adim2_germ _ Im w)} →
          ∀ Q ∈ (adim2_ideal _ (adim2_germ _ {w | w ∈ Im ∧ ((r + 1 : ℕ) : WithBot ℕ∞) ≤
            adim2_dimension _ (adim2_germ _ Im w)} w)).minimalPrimes,
            ringKrullDim (AnalyticGerm _ ⧸ Q) = ((r + 1 : ℕ) : WithBot ℕ∞)) := by
      intro z hz hzI
      obtain ⟨h1, h2, -, -⟩ := anrem_split hzI (hImloc z hz)
        (Filter.mem_of_superset (hΩT.mem_nhds hz) fun w hw ↦ hImdim w hw)
      exact ⟨h1, h2⟩
    have hBeq : ∀ z ∈ Ω \ T', ∀ᶠ w in 𝓝 z, w ∈ B ↔
        w ∈ {w | w ∈ Im ∧ ((r + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension _ (adim2_germ _ Im w)} := by
      intro z hz
      filter_upwards [hΩT.mem_nhds hz] with w hw
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hw.2, h.2⟩⟩
    have hBloc : ∀ z ∈ Ω \ T', anrem_LocEq B z := by
      intro z hz
      by_cases hzI : z ∈ Im
      · obtain ⟨O, hOsub, hO, hzO⟩ := eventually_nhds_iff.1 (hBeq z hz)
        exact anrem_locEq_congr hO hzO (by
          ext w; exact ⟨fun h ↦ ⟨(hOsub w h.2).2 h.1, h.2⟩, fun h ↦ ⟨(hOsub w h.2).1 h.1, h.2⟩⟩)
          (hsplit z hz hzI).1
      · refine anrem_locEq_of_eventually_not_mem ?_
        filter_upwards [anrem_eventually_not_mem (hImloc z hz) hzI] with w hw hwB
        exact hw hwB.1
    have hBpure : ∀ z ∈ B, ∀ Q ∈ (adim2_ideal _ (adim2_germ _ B z)).minimalPrimes,
        ringKrullDim (AnalyticGerm _ ⧸ Q) = ((r + 1 : ℕ) : WithBot ℕ∞) := by
      intro z hzB Q hQ
      have hz : z ∈ Ω \ T' := hBsub hzB
      rw [anrem_germ_congr (hBeq z hz)] at hQ
      exact (hsplit z hz hzB.1).2.self_of_nhds ⟨hzB.1, hzB.2.2⟩ Q hQ
    have haT' : (T.atlas.chart jd).toFun a ∈ T' ∩ Ω :=
      ⟨⟨a, ⟨⟨x₁, hx₁, hfx₁⟩, had⟩, rfl⟩, hdU a had⟩
    have hclB := hRS _ r T' B Ω hΩ hT'loc hT'dim hBsub hBloc hBpure _ haT'
    -- the lower-dimensional part of the locus
    obtain ⟨e, he⟩ : ∃ e, p = e + 1 := ⟨k + r, by omega⟩
    obtain ⟨hLc, hLW, hLdim⟩ := anrem_lowClosure hDCu S (hFc k) (e := e)
      (fun x hx ↦ he ▸ hFdim k x hx)
    have hLimg := IH e he _ hLc hLdim
    set ImL := (T.atlas.chart jd).toFun ''
      (f '' closure {x | x ∈ F k ∧ an_dimAt S (F k) x ≤ (e : WithBot ℕ∞)} ∩ (T.atlas.chart jd).dom)
    have hImLloc : anrem_LocEq ImL ((T.atlas.chart jd).toFun a) :=
      anrem_chart_image_locEq T hLimg jd (hdU a had)
    -- the image near the point is the union of the three pieces
    have heq : Im ∩ Ω = (closure B ∪ T' ∪ ImL) ∩ Ω := by
      ext z
      constructor
      · rintro ⟨hzIm, hzΩ⟩
        refine ⟨?_, hzΩ⟩
        by_cases hzT : z ∈ T'
        · exact Or.inl (Or.inr hzT)
        by_cases hzd : ((r + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension _ (adim2_germ _ Im z)
        · exact Or.inl (Or.inl (subset_closure ⟨hzIm, hzT, hzd⟩))
        obtain ⟨y, ⟨⟨x, hxF, rfl⟩, hyd⟩, rfl⟩ := hzIm
        have hx1 : f x ∉ f '' F (k + 1) := hnotT' _ hyd hzT
        have hfib : an_dimAt S (F k ∩ f ⁻¹' {f x}) x ≤ ((k : ℕ∞) : WithBot ℕ∞) :=
          (hfibk x hxF hx1).le
        have hM1 := anrem_dim_le_image_add S T hf.2 (hFc k) hxF hfib jd hyd (I := Im)
          (by
            filter_upwards [((T.atlas.chart jd).isOpen_dom.preimage hf.1.continuous).mem_nhds hyd]
              with x' hx' hx'F
            exact ⟨f x', ⟨⟨x', hx'F, rfl⟩, hx'⟩, rfl⟩)
          (hImloc _ ⟨hzΩ, hzT⟩) (anrem_le_of_not_succ_le hzd)
        rw [show r + k = e by omega] at hM1
        exact Or.inr ⟨f x, ⟨⟨x, subset_closure ⟨hxF, hM1⟩, rfl⟩, hyd⟩, rfl⟩
      · rintro ⟨hz, hzΩ⟩
        refine ⟨?_, hzΩ⟩
        rcases hz with (hzB | hzT) | hzL
        · have hzI : z ∈ closure Im := closure_mono (fun w hw ↦ hw.1) hzB
          have hzm : z ∈ (T.atlas.chart jd).toFun '' (T.atlas.chart jd).dom :=
            anrem_chart_model_closed _ hzΩ (closure_mono (s := Im)
              (fun w hw ↦ by obtain ⟨y, hy, hyw⟩ := hw; exact ⟨y, hy.2, hyw⟩) hzI)
          obtain ⟨y, hy, rfl⟩ := hzm
          have hyc := (anrem_mem_closure_chart_iff (T.atlas.chart jd) (f '' F k) hy).2 hzI
          rw [hclosed.closure_eq] at hyc
          exact ⟨y, ⟨hyc, hy⟩, rfl⟩
        · obtain ⟨y, ⟨⟨x, hxF, rfl⟩, hyd⟩, rfl⟩ := hzT
          exact ⟨f x, ⟨⟨x, hFmono k hxF, rfl⟩, hyd⟩, rfl⟩
        · obtain ⟨y, ⟨⟨x, hxL, rfl⟩, hyd⟩, rfl⟩ := hzL
          exact ⟨f x, ⟨⟨x, hLW hxL, rfl⟩, hyd⟩, rfl⟩
    have hloc := anrem_locEq_congr hΩ (hdU a had) heq.symm
      (anrem_locEq_union (anrem_locEq_union hclB (hT'loc _ (hdU a had))) hImLloc)
    exact anrem_anNear_of_chart T jd had hloc
  refine ⟨hAn, fun y hy ↦ ?_⟩
  -- the dimension bound, at every level
  have hfibj : ∀ j, ∀ x ∈ F j, f x ∉ f '' F (j + 1) →
      an_dimAt S (F j ∩ f ⁻¹' {f x}) x = (j : WithBot ℕ∞) := by
    intro j x hx hfx
    have hx1 : x ∉ F (j + 1) := fun h ↦ hfx ⟨x, h, rfl⟩
    have hle : an_dimAt S (W ∩ f ⁻¹' {f x}) x ≤ (j : WithBot ℕ∞) :=
      anrem_le_of_not_succ_le fun h ↦ hx1 ⟨hFW j hx, by exact_mod_cast h⟩
    refine le_antisymm ((anrem_dimAt_mono S (inter_subset_inter_left _ (hFW j)) x).trans hle) ?_
    exact_mod_cast anrem_fibreLocus_dim hDCu S T hf.2 hW j hx.1 hx.2
  have hPAj : ∀ j, ∀ y', y' ∉ f '' F (j + 1) →
      an_dimAt T (f '' F j) y' ≤ ((p - j : ℕ) : WithBot ℕ∞) := fun j y' hy' ↦
    (anrem_partA hFM hCS hDCu S T hf (hFc j) (hf.1.isClosedMap _ (hFc (j + 1)).1).isOpen_compl
      (fun x hx ↦ by exact_mod_cast hfibj j x hx.1 hx.2) (fun x hx ↦ hFdim j x hx.1) hy').2
  set jd := T.atlas.chartAt y
  have hyd : y ∈ (T.atlas.chart jd).dom := T.atlas.mem_chartAt y
  have hdU : ∀ y' ∈ (T.atlas.chart jd).dom, (T.atlas.chart jd).toFun y' ∈ (T.atlas.chart jd).U := by
    intro y' hy'
    have : (T.atlas.chart jd).toFun y' ∈ (T.atlas.chart jd).toFun '' (T.atlas.chart jd).dom :=
      mem_image_of_mem _ hy'
    rw [(T.atlas.chart jd).image_eq] at this; exact this.1
  set Ims : ℕ → Set (Fin (T.atlas.chart jd).n → ℂ) := fun j ↦
    (T.atlas.chart jd).toFun '' (f '' F j ∩ (T.atlas.chart jd).dom)
  set b := (T.atlas.chart jd).toFun y
  change adim2_dimension _ (adim2_germ _ (Ims k) b) ≤ _
  refine (anrem_dimension_le_iff _ _ _).2 fun Q hQ ↦ ?_
  have hbI : b ∈ Ims k := ⟨y, ⟨hy, hyd⟩, rfl⟩
  have hIloc : anrem_LocEq (Ims k) b := anrem_chart_image_locEq T hAn jd (hdU y hyd)
  obtain ⟨eQ, heQ⟩ := anrem_quotient_dim_cases Q hQ.1.1
  obtain ⟨C, hbC, hCI, -, hCpure, -⟩ := anrem_component hbI hIloc hQ heQ
  rw [heQ]
  let P : ℕ → Prop := fun j ↦ ∀ᶠ z in 𝓝 b, z ∈ C → z ∈ Ims j
  have hPk : P k := hCI
  have hkp : k ≤ p := by
    by_contra h
    obtain ⟨x, hx, -⟩ := hy
    rw [hFempty k (by omega)] at hx
    exact hx
  have hPp : ¬ P (p + 1) := by
    intro h
    obtain ⟨x, ⟨⟨x', hx', -⟩, -⟩, -⟩ := h.self_of_nhds hbC
    rw [hFempty (p + 1) (Nat.lt_succ_self p)] at hx'
    exact hx'
  set js := Nat.findGreatest P p
  have hjs : P js := Nat.findGreatest_spec hkp hPk
  have hkjs : k ≤ js := Nat.le_findGreatest hkp hPk
  have hjsp : js ≤ p := Nat.findGreatest_le p
  have hnext : ¬ P (js + 1) := by
    by_cases h : js + 1 ≤ p
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self js) h
    · have : js = p := by omega
      rw [this]; exact hPp
  obtain ⟨O, hOsub, hO, hbO⟩ := eventually_nhds_iff.1 (hjs.and hCpure)
  have hfreq : ∃ᶠ z in 𝓝 b, z ∈ C ∧ z ∉ Ims (js + 1) := by
    simp only [P, not_eventually, not_imp] at hnext
    exact hnext
  obtain ⟨z, ⟨hzC, hznot⟩, hzO⟩ := (hfreq.and_eventually (hO.mem_nhds hbO)).exists
  obtain ⟨y', ⟨hy'F, hy'd⟩, rfl⟩ := (hOsub z hzO).1 hzC
  have hy'n : y' ∉ f '' F (js + 1) := fun h ↦ hznot ⟨y', ⟨h, hy'd⟩, rfl⟩
  have h1 := hPAj js y' hy'n
  rw [hDCv T _ jd hy'd] at h1
  have h2 : adim2_dimension _ (adim2_germ _ C ((T.atlas.chart jd).toFun y')) =
      (eQ : WithBot ℕ∞) := anrem_dimension_eq_of_pure hzC ((hOsub _ hzO).2 hzC)
  have h3 : adim2_dimension _ (adim2_germ _ C ((T.atlas.chart jd).toFun y')) ≤
      adim2_dimension _ (adim2_germ _ (Ims js) ((T.atlas.chart jd).toFun y')) := by
    apply anrem_dimension_mono
    filter_upwards [hO.mem_nhds hzO] with w hw hwC
    exact (hOsub w hw).1 hwC
  rw [h2] at h3
  refine h3.trans (h1.trans ?_)
  exact_mod_cast Nat.sub_le_sub_left hkjs p

/-- **Remmert's proper mapping theorem under a dimension bound.** -/
theorem anrem_remmert_bounded (hFM : anrem_FiniteMappingStmt) (hCS : anrem_ClosedSubspaceStmt)
    (hDCu : anrem_DimChartStmt.{u}) (hDCv : anrem_DimChartStmt.{v})
    (hCR : anrem_CartanRemmertStmt.{u, v}) (hRS : anrem_LocalRSStmt)
    (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y} (hf : an_IsProperHom S T f)
    (p : ℕ) : ∀ W : Set X, an_IsClosedAnalytic S W → (∀ x ∈ W, an_dimAt S W x ≤ (p : WithBot ℕ∞)) →
      an_IsClosedAnalytic T (f '' W) := by
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
  intro W hW hWdim
  have IH : ∀ e : ℕ, p = e + 1 → ∀ W' : Set X, an_IsClosedAnalytic S W' →
      (∀ x ∈ W', an_dimAt S W' x ≤ (e : WithBot ℕ∞)) → an_IsClosedAnalytic T (f '' W') :=
    fun e he W' hW' hdim ↦ ihp e (by omega) W' hW' hdim
  obtain ⟨-, -, -, hFempty, hF0, -⟩ := anrem_fibreLocus_facts hCR S T hf.2 hW hWdim
  have hall : ∀ m k, p + 1 ≤ k + m →
      an_IsClosedAnalytic T (f '' anrem_fibreLocus S f W k) ∧
        ∀ y ∈ f '' anrem_fibreLocus S f W k,
          an_dimAt T (f '' anrem_fibreLocus S f W k) y ≤ ((p - k : ℕ) : WithBot ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [hFempty k (by omega), image_empty]
      exact ⟨an_isClosedAnalytic_empty T, fun y hy ↦ hy.elim⟩
    | succ m ihm =>
      intro k hk
      by_cases h : p + 1 ≤ k + m
      · exact ihm k h
      · exact anrem_descend_step hFM hCS hDCu hDCv hCR hRS S T hf IH hW hWdim
          (fun j hj ↦ ihm j (by omega))
  have := (hall (p + 1) 0 (by omega)).1
  rwa [hF0] at this

/-- Germ dimensions in an open subspace. -/
theorem anrem_dimAt_openSpace (hDCu : anrem_DimChartStmt.{u}) (S : an_ReducedSpace X) {O : Set X}
    (hO : IsOpen O) (W' : Set O) (x : O) :
    an_dimAt (anrem_openSpace S hO) W' x = an_dimAt S (Subtype.val '' W') x := by
  rw [hDCu (anrem_openSpace S hO) W' (S.atlas.chartAt x) (S.atlas.mem_chartAt (x : X))]
  change adim2_dimension (S.atlas.chart (S.atlas.chartAt (x : X))).n (adim2_germ _
    ((S.atlas.chart (S.atlas.chartAt (x : X))).toFun ∘ Subtype.val ''
      (W' ∩ Subtype.val ⁻¹' (S.atlas.chart (S.atlas.chartAt (x : X))).dom)) _) = _
  congr 2
  ext z
  constructor
  · rintro ⟨w, ⟨hwW, hwd⟩, rfl⟩
    exact ⟨w, ⟨⟨w, hwW, rfl⟩, hwd⟩, rfl⟩
  · rintro ⟨_, ⟨⟨w, hwW, rfl⟩, hwd⟩, rfl⟩
    exact ⟨w, ⟨hwW, hwd⟩, rfl⟩

/-- Closed analytic sets restrict to open subspaces. -/
theorem anrem_isClosedAnalytic_openSpace (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O)
    {W : Set X} (hW : an_IsClosedAnalytic S W) :
    an_IsClosedAnalytic (anrem_openSpace S hO) (Subtype.val ⁻¹' W : Set O) := by
  refine ⟨hW.1.preimage continuous_subtype_val, fun x hx ↦ ?_⟩
  change anrem_AnNear (anrem_openSpace S hO) _ x
  rw [anrem_anNear_openSpace_iff, Subtype.image_preimage_coe]
  exact anrem_anNear_mono_nhd S hO x.2 (by ext z; simp only [mem_inter_iff]; tauto) (hW.2 x hx)

/-- **Remmert's proper mapping theorem.** -/
theorem anrem_remmert (hFM : anrem_FiniteMappingStmt) (hCS : anrem_ClosedSubspaceStmt)
    (hDCu : anrem_DimChartStmt.{u}) (hDCv : anrem_DimChartStmt.{v})
    (hCR : anrem_CartanRemmertStmt.{u, v}) (hRS : anrem_LocalRSStmt)
    (S : an_ReducedSpace X) (T : an_ReducedSpace Y) [LocallyCompactSpace Y]
    (hDB : ∀ (Z : Set X) {K : Set X}, IsCompact K → ∃ d : ℕ, ∀ x ∈ K, an_dimAt S Z x ≤ d)
    {f : X → Y} (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) :
    an_IsClosedAnalytic T (f '' Z) := by
  have := T.t2Space
  refine ⟨hf.1.isClosedMap _ hZ.1, fun y hy ↦ ?_⟩
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  obtain ⟨d, hd⟩ := hDB Z (hf.1.isCompact_preimage hK)
  set V := interior K
  have hV : IsOpen V := isOpen_interior
  have hyV : y ∈ V := mem_interior_iff_mem_nhds.2 hKy
  have hO : IsOpen (f ⁻¹' V) := hV.preimage hf.1.continuous
  set S' := anrem_openSpace S hO
  set T' := anrem_openSpace T hV
  set f' : (f ⁻¹' V : Set X) → V := V.restrictPreimage f
  have hf' : an_IsProperHom S' T' f' := by
    refine ⟨anrem_isProperMap_restrictPreimage hf.1 (⟨V, hV⟩ : TopologicalSpace.Opens Y), ?_⟩
    exact anrem_isHom_openSpace S T hf.2 hO hV (fun x hx ↦ hx)
  set Z' : Set (f ⁻¹' V : Set X) := Subtype.val ⁻¹' Z
  have hZ' : an_IsClosedAnalytic S' Z' := anrem_isClosedAnalytic_openSpace S hO hZ
  have hZ'dim : ∀ x ∈ Z', an_dimAt S' Z' x ≤ (d : WithBot ℕ∞) := by
    intro x hx
    rw [anrem_dimAt_openSpace hDCu S hO]
    refine (anrem_dimAt_mono S (Z' := Z) (fun z hz ↦ by
      obtain ⟨w, hw, hwz⟩ := hz; exact hwz ▸ hw) x).trans ?_
    exact
      (hd x (interior_subset (s := K) x.2))
  have himg := anrem_remmert_bounded hFM hCS hDCu hDCv hCR hRS S' T' hf' d Z' hZ' hZ'dim
  obtain ⟨x, hxZ, rfl⟩ := hy
  have hmem : (⟨f x, hyV⟩ : V) ∈ f' '' Z' := ⟨⟨x, hyV⟩, hxZ, rfl⟩
  have hnear : anrem_AnNear (anrem_openSpace T hV) (f' '' Z') ⟨f x, hyV⟩ := himg.2 _ hmem
  rw [anrem_anNear_openSpace_iff] at hnear
  refine anrem_anNear_mono_nhd T hV hyV ?_ hnear
  ext w
  constructor
  · rintro ⟨⟨_, ⟨x', hx'Z, rfl⟩, rfl⟩, hwV⟩
    exact ⟨⟨x', hx'Z, rfl⟩, hwV⟩
  · rintro ⟨⟨x', hx'Z, rfl⟩, hwV⟩
    exact ⟨⟨_, ⟨⟨x', hwV⟩, hx'Z, rfl⟩, rfl⟩, hwV⟩

end Main

end HodgeLean.Foundations.Analytic
