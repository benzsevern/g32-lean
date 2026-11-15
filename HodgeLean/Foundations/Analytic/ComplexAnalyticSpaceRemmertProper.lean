import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertSlice

/-! # Images under proper maps over constant fibre dimension

Lane `an-rem`, prefix `anrem_`. Holomorphic maps between open subspaces and Euclidean spaces, the
local finite projection theorem in `ℂᴺ` (from the finite mapping theorem and closed subspaces,
taken as inputs `anrem_FiniteMappingStmt` and `anrem_ClosedSubspaceStmt`), chart representations
of holomorphic maps, and the image of a closed analytic set under a proper holomorphic map over
an open set where its fibres have constant dimension: analytic, of the expected dimension
(Narasimhan, LNM 25, Ch. VII; Chirka, *Complex Analytic Sets*, §3.7). Germ dimensions in an
arbitrary chart are the input `anrem_DimChartStmt`. HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

universe u v w

section Plumbing

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]

theorem anrem_isHom_comp (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (R : an_ReducedSpace Z)
    {f : X → Y} {g : Y → Z} (hf : an_IsHom S T f) (hg : an_IsHom T R g) :
    an_IsHom S R (g ∘ f) :=
  ⟨hg.1.comp hf.1, fun V hV h hh ↦ hf.2 _ (hV.preimage hg.1) _ (hg.2 V hV h hh)⟩

theorem anrem_isHom_openSpace_val (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O) :
    an_IsHom (anrem_openSpace S hO) S Subtype.val :=
  ⟨continuous_subtype_val, fun _ _ _ hg ↦ anrem_isHolFun_openSpace S hO hg⟩

/-- A holomorphic function on an open piece of an open subspace, read on the ambient space. -/
theorem anrem_isHolFun_of_openSpace (T : an_ReducedSpace Y) {O' : Set Y} (hO' : IsOpen O')
    {V : Set O'} {g : V → ℂ} (hg : (anrem_openSpace T hO').IsHolFun g) :
    T.IsHolFun (fun y : (Subtype.val '' V : Set Y) ↦ g ⟨y.2.choose, y.2.choose_spec.1⟩) := by
  intro y j hy
  obtain ⟨N, hN, hyN, G, hG, h⟩ := hg ⟨y.2.choose, y.2.choose_spec.1⟩ j
    (show ((y.2.choose : O') : Y) ∈ (T.atlas.chart j).dom by rw [y.2.choose_spec.2]; exact hy)
  refine ⟨Subtype.val '' N, hO'.isOpenMap_subtype_val N hN, ⟨_, hyN, y.2.choose_spec.2⟩, G,
    ?_, fun z hz ↦ ?_⟩
  · have := hG
    change AnalyticAt ℂ G ((T.atlas.chart j).toFun (y.2.choose : Y)) at this
    rwa [y.2.choose_spec.2] at this
  · obtain ⟨⟨w, hwN, hwz⟩, hzd⟩ := hz
    have hw : (z.2.choose : Y) = w := by rw [z.2.choose_spec.2, hwz]
    have hw' : z.2.choose = w := Subtype.ext hw
    have := h ⟨z.2.choose, z.2.choose_spec.1⟩ ⟨hw' ▸ hwN,
      show ((z.2.choose : O') : Y) ∈ (T.atlas.chart j).dom by rw [z.2.choose_spec.2]; exact hzd⟩
    change g ⟨z.2.choose, _⟩ = _
    rw [this]
    change G ((T.atlas.chart j).toFun (z.2.choose : Y)) = _
    rw [z.2.choose_spec.2]

/-- Corestriction of a holomorphic map to an open subspace containing its range. -/
theorem anrem_isHom_corestrict (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {O' : Set Y} (hO' : IsOpen O') (hrange : ∀ x, f x ∈ O') :
    an_IsHom S (anrem_openSpace T hO') (fun x ↦ ⟨f x, hrange x⟩) := by
  refine ⟨hf.1.subtype_mk _, fun V hV g hg ↦ ?_⟩
  have hVY : IsOpen (Subtype.val '' V : Set Y) := hO'.isOpenMap_subtype_val V hV
  have h1 := hf.2 _ hVY _ (anrem_isHolFun_of_openSpace T hO' hg)
  have hsub : (fun x ↦ (⟨f x, hrange x⟩ : O')) ⁻¹' V ⊆ f ⁻¹' (Subtype.val '' V) :=
    fun x hx ↦ ⟨_, hx, rfl⟩
  have h2 := anrem_isHolFun_restrict S hsub h1
  convert h2 using 2 with x
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact (Exists.choose_spec (⟨_, x.2, rfl⟩ : ∃ v ∈ V, (v : Y) = f x)).2.symm

/-- Maps of `ℂⁿ` analytic everywhere are holomorphic for the structure sheaves. -/
theorem anrem_isHom_euclid {n m : ℕ} {F : (Fin n → ℂ) → (Fin m → ℂ)}
    (hF : ∀ z, AnalyticAt ℂ F z) : an_IsHom (an_euclidSpace n) (an_euclidSpace m) F := by
  have hc : Continuous F := continuous_iff_continuousAt.2 fun z ↦ (hF z).continuousAt
  refine ⟨hc, fun V _ g hg x _ _ ↦ ?_⟩
  obtain ⟨N, hN, hxN, G, hG, h⟩ := hg ⟨F x, x.2⟩ ⟨⟩ (mem_univ _)
  exact ⟨F ⁻¹' N, hN.preimage hc, hxN, G ∘ F, (show AnalyticAt ℂ G (F x) from hG).comp (hF x),
    fun y hy ↦ h ⟨F y, y.2⟩ ⟨hy.1, mem_univ _⟩⟩

/-- On `ℂⁿ`, local analyticity is having local equations. -/
theorem anrem_anNear_euclid_iff {n : ℕ} (A : Set (Fin n → ℂ)) (z : Fin n → ℂ) :
    anrem_AnNear (an_euclidSpace n) A z ↔ anrem_LocEq A z := by
  constructor
  · intro h
    have := anrem_anNear_chart (an_euclidSpace n) h ⟨⟩ (mem_univ z)
    simpa [an_euclidSpace, an_euclidAtlas] using this
  · intro h
    exact anrem_anNear_of_chart (an_euclidSpace n) ⟨⟩ (mem_univ z)
      (by simpa [an_euclidSpace, an_euclidAtlas] using h)

end Plumbing

/-! ### The local finite projection theorem in `ℂᴺ` -/

/-- The finite mapping theorem for spaces whose points are of type `Type`, as an input. -/
def anrem_FiniteMappingStmt : Prop :=
  ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) (f : X → Y), an_IsProperHom S T f → ∀ {Z : Set X},
    an_IsClosedAnalytic S Z → (∀ y, (Z ∩ f ⁻¹' {y}).Finite) → an_IsClosedAnalytic T (f '' Z)

/-- Closed analytic subsets of spaces whose points are of type `Type` are spaces, as an input. -/
def anrem_ClosedSubspaceStmt : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (S : an_ReducedSpace X) {Z : Set X},
    an_IsClosedAnalytic S Z → ∃ SZ : an_ReducedSpace Z, an_IsHom SZ S Subtype.val

/-- A set with local equations at every point of an open set is relatively closed there. -/
theorem anrem_isClosed_of_locEq {N : ℕ} {C O : Set (Fin N → ℂ)}
    (h : ∀ z ∈ O, anrem_LocEq C z) : IsClosed (Subtype.val ⁻¹' C : Set O) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hzU, k, f, hf, hUC⟩ := h z z.2
  have : ¬ ∀ j, f j z = 0 := fun h' ↦ hz ((hUC z hzU).2 h')
  push Not at this
  obtain ⟨j, hj⟩ := this
  have hev : ∀ᶠ x in 𝓝 (z : Fin N → ℂ), x ∈ U ∧ f j x ≠ 0 :=
    Filter.Eventually.and (hU.mem_nhds hzU) ((hf j z hzU).continuousAt.eventually_ne hj)
  have := continuous_subtype_val.continuousAt.preimage_mem_nhds hev
  filter_upwards [this] with x hx hxC
  exact hx.2 ((hUC x hx.1).1 hxC j)

/-- **Local finite projections.** If `C` has local equations at the points of an open set `O`,
lies in `O`, and the linear map `P` restricted to `C` is proper with finite fibres over an open
`V ⊇ P(O)`, then `P(C)` has local equations at the points of `V`. -/
theorem anrem_finite_projection_local (hFM : anrem_FiniteMappingStmt)
    (hCS : anrem_ClosedSubspaceStmt) {N m : ℕ} {C O : Set (Fin N → ℂ)} (hO : IsOpen O)
    (P : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ)) {V : Set (Fin m → ℂ)} (hV : IsOpen V)
    (hOV : ∀ z ∈ O, P z ∈ V) (hCO : C ⊆ O) (hCloc : ∀ z ∈ O, anrem_LocEq C z)
    (hproper : ∀ K, IsCompact K → K ⊆ V → IsCompact (C ∩ P ⁻¹' K))
    (hfin : ∀ t ∈ V, (C ∩ P ⁻¹' {t}).Finite) :
    ∀ t ∈ V, anrem_LocEq (P '' C) t := by
  set X₀ := anrem_openSpace (an_euclidSpace N) hO
  set C₀ : Set O := Subtype.val ⁻¹' C
  have hC₀ : an_IsClosedAnalytic X₀ C₀ := by
    refine ⟨anrem_isClosed_of_locEq hCloc, fun x _ ↦ ?_⟩
    change anrem_AnNear (anrem_openSpace (an_euclidSpace N) hO) C₀ x
    rw [anrem_anNear_openSpace_iff, show Subtype.val '' C₀ = C by
      ext z; exact ⟨fun ⟨w, hw, hwz⟩ ↦ hwz ▸ hw, fun hz ↦ ⟨⟨z, hCO hz⟩, hz, rfl⟩⟩,
      anrem_anNear_euclid_iff]
    exact hCloc x x.2
  obtain ⟨SZ, hval⟩ := hCS X₀ hC₀
  set Y₀ := anrem_openSpace (an_euclidSpace m) hV
  let p : C₀ → V := fun c ↦ ⟨P c.1.1, hOV _ c.1.2⟩
  have hPhom : an_IsHom (an_euclidSpace N) (an_euclidSpace m) P :=
    anrem_isHom_euclid fun z ↦ P.analyticAt z
  have hp : an_IsHom SZ Y₀ p := by
    have h1 := anrem_isHom_comp SZ X₀ (an_euclidSpace N) hval
      (anrem_isHom_openSpace_val (an_euclidSpace N) hO)
    have h2 := anrem_isHom_comp SZ (an_euclidSpace N) (an_euclidSpace m) h1 hPhom
    exact anrem_isHom_corestrict SZ (an_euclidSpace m) h2 hV (fun c ↦ hOV _ c.1.2)
  have : LocallyCompactSpace V := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hpp : IsProperMap p := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hp.1, fun K hK ↦ ?_⟩
    rw [Subtype.isCompact_iff, Subtype.isCompact_iff, image_image]
    have heq : (fun c : C₀ ↦ ((c : O) : Fin N → ℂ)) '' (p ⁻¹' K) =
        C ∩ P ⁻¹' (Subtype.val '' K) := by
      ext z
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c.2, ⟨p c, hc, rfl⟩⟩
      · rintro ⟨hzC, ⟨t, htK, htz⟩⟩
        refine ⟨⟨⟨z, hCO hzC⟩, hzC⟩, ?_, rfl⟩
        change p _ ∈ K
        have : p ⟨⟨z, hCO hzC⟩, hzC⟩ = t := Subtype.ext htz.symm
        rw [this]; exact htK
    rw [heq]
    exact hproper _ (hK.image continuous_subtype_val) (fun _ ⟨t, _, htz⟩ ↦ htz ▸ t.2)
  have hpfin : ∀ t, ((univ : Set C₀) ∩ p ⁻¹' {t}).Finite := by
    intro t
    refine ((hfin t t.2).preimage (f := fun c : C₀ ↦ ((c : O) : Fin N → ℂ))
      (fun c _ c' _ h ↦ Subtype.ext (Subtype.ext h))).subset fun c hc ↦ ?_
    refine ⟨c.2, ?_⟩
    have : p c = t := hc.2
    exact congrArg Subtype.val this
  have himg := hFM SZ Y₀ p ⟨hpp, hp⟩ (an_isClosedAnalytic_univ SZ) hpfin
  have hset : Subtype.val '' (p '' univ) = P '' C := by
    ext t
    constructor
    · rintro ⟨_, ⟨c, -, rfl⟩, rfl⟩
      exact ⟨_, c.2, rfl⟩
    · rintro ⟨z, hzC, rfl⟩
      exact ⟨p ⟨⟨z, hCO hzC⟩, hzC⟩, ⟨_, mem_univ _, rfl⟩, rfl⟩
  intro t ht
  have hnear : anrem_AnNear Y₀ (p '' univ) ⟨t, ht⟩ := by
    by_cases hmem : (⟨t, ht⟩ : V) ∈ p '' univ
    · exact himg.2 _ hmem
    · exact anrem_anNear_of_not_mem Y₀ himg.1 hmem
  rw [anrem_anNear_openSpace_iff, hset, anrem_anNear_euclid_iff] at hnear
  exact hnear


/-! ### Chart representations -/

/-- Germ dimensions computed in any chart, as an input. -/
def anrem_DimChartStmt.{u'} : Prop :=
  ∀ {X : Type u'} [TopologicalSpace X] (S : an_ReducedSpace X) (Z : Set X) (i : S.atlas.ι)
    {x : X}, x ∈ (S.atlas.chart i).dom → an_dimAt S Z x = adim2_dimension (S.atlas.chart i).n
      (adim2_germ (S.atlas.chart i).n ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom))
        ((S.atlas.chart i).toFun x))

theorem anrem_graph_inter_fibre {n m : ℕ} (A : Set (Fin n → ℂ))
    (F : (Fin n → ℂ) → (Fin m → ℂ)) (t : Fin m → ℂ) :
    anrem_graph (A ∩ {z | F z = t}) F = anrem_graph A F ∩ {u | anrem_snd u = t} := by
  ext u
  simp only [anrem_graph, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h3.trans h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h3 ▸ h2⟩, h3⟩

section Rep

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- A holomorphic map read in a chart of the source and a chart of the target is, near a point,
the restriction of an ambient map analytic at the image point. -/
theorem anrem_hom_chart_rep (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {x : X} (i : S.atlas.ι) (hxi : x ∈ (S.atlas.chart i).dom)
    (jd : T.atlas.ι) (hxd : f x ∈ (T.atlas.chart jd).dom) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (S.atlas.chart i).dom ∩ f ⁻¹' (T.atlas.chart jd).dom ∧
      ∃ F : (Fin (S.atlas.chart i).n → ℂ) → (Fin (T.atlas.chart jd).n → ℂ),
        AnalyticAt ℂ F ((S.atlas.chart i).toFun x) ∧
        ∀ x' ∈ N, (T.atlas.chart jd).toFun (f x') = F ((S.atlas.chart i).toFun x') := by
  set c := S.atlas.chart i
  set d := T.atlas.chart jd
  have hcoord : ∀ l : Fin d.n, S.IsHolFun (fun x' : f ⁻¹' d.dom ↦ d.toFun (f x') l) := fun l ↦
    hf.2 _ d.isOpen_dom _ (anrem_isHolFun_comp_chart T jd subset_rfl (fun z ↦ z l)
      fun _ _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d.n ↦ ℂ) l).analyticAt _)
  choose N hN hxN G hG hGeq using fun l ↦ hcoord l ⟨x, hxd⟩ i hxi
  refine ⟨(⋂ l, N l) ∩ c.dom ∩ f ⁻¹' d.dom,
    ((isOpen_iInter_of_finite hN).inter c.isOpen_dom).inter (d.isOpen_dom.preimage hf.1),
    ⟨⟨mem_iInter.2 hxN, hxi⟩, hxd⟩, fun x' hx' ↦ ⟨hx'.1.2, hx'.2⟩, fun z l ↦ G l z,
    analyticAt_pi_iff.2 hG, fun x' hx' ↦ funext fun l ↦ ?_⟩
  exact hGeq l ⟨x', hx'.2⟩ ⟨mem_iInter.1 hx'.1.1 l, hx'.1.2⟩

/-- **The image of a slice near one point of a fibre.** At a point `x` of a closed analytic `W`
near which the fibres of `f` on `W` all have dimension `j` and `W` has dimension at most `q`,
there are an open neighbourhood `B` of `x` and a subset `Q ⊆ W` such that every point of
`W ∩ B` has a point of `Q` in its fibre, `f(Q)` is analytic near `f x`, and its chart image has
Hausdorff dimension at most `2(q - j)`. -/
theorem anrem_partA_local (hFM : anrem_FiniteMappingStmt) (hCS : anrem_ClosedSubspaceStmt)
    (hDC : anrem_DimChartStmt.{u}) (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {W : Set X} (hW : an_IsClosedAnalytic S W) {j q : ℕ} {B₀ : Set X}
    (hB₀ : IsOpen B₀) (hfibB : ∀ x' ∈ W ∩ B₀, an_dimAt S (W ∩ f ⁻¹' {f x'}) x' = j)
    (hdimB : ∀ x' ∈ W ∩ B₀, an_dimAt S W x' ≤ q) {x : X} (hx : x ∈ W) (hxB : x ∈ B₀)
    (jd : T.atlas.ι) (hxd : f x ∈ (T.atlas.chart jd).dom) :
    ∃ B Q : Set X, IsOpen B ∧ x ∈ B ∧ Q ⊆ W ∧ (∀ x' ∈ W ∩ B, ∃ x'' ∈ Q, f x'' = f x') ∧
      anrem_AnNear T (f '' Q) (f x) ∧ (∀ x'' ∈ Q, f x'' ∈ (T.atlas.chart jd).dom) ∧
      dimH ((T.atlas.chart jd).toFun '' (f '' Q)) ≤ ((2 * (q - j) : ℕ) : ENNReal) := by
  classical
  set i := S.atlas.chartAt x
  set c := S.atlas.chart i
  have hxi : x ∈ c.dom := S.atlas.mem_chartAt x
  set d := T.atlas.chart jd
  obtain ⟨N, hN, hxN, hNsub, F, hF, hFeq⟩ := anrem_hom_chart_rep S T hf i hxi jd hxd
  obtain ⟨UA, hUA, hxUA, kA, eA, heA, hUAeq⟩ := anrem_anNear_chart S (hW.2 x hx) i hxi
  obtain ⟨OF, hOFsub, hOF, hxOF⟩ := eventually_nhds_iff.1 hF.eventually_analyticAt
  obtain ⟨O₁, hO₁, hO₁eq⟩ := anrem_chart_nhd c (hN.inter hB₀)
  set O := O₁ ∩ UA ∩ OF
  have hO : IsOpen O := (hO₁.inter hUA).inter hOF
  have hxO₁ : c.toFun x ∈ O₁ := by
    have : x ∈ c.dom ∩ (N ∩ B₀) := ⟨hxi, hxN, hxB⟩
    rw [← hO₁eq] at this; exact this.2
  have hxO : c.toFun x ∈ O := ⟨⟨hxO₁, hxUA⟩, hxOF⟩
  have hO_N : ∀ x', x' ∈ c.dom → c.toFun x' ∈ O → x' ∈ N ∧ x' ∈ B₀ := by
    intro x' hx'c hx'O
    have : x' ∈ c.dom ∩ c.toFun ⁻¹' O₁ := ⟨hx'c, hx'O.1.1⟩
    rw [hO₁eq] at this; exact this.2
  set A := c.toFun '' (W ∩ c.dom)
  set Γ := anrem_graph A F
  set UΓ : Set (Fin (c.n + d.n) → ℂ) := anrem_fst ⁻¹' O
  have hUΓ : IsOpen UΓ := hO.preimage anrem_fst.continuous
  let fΓ : Fin (kA + d.n) → (Fin (c.n + d.n) → ℂ) → ℂ :=
    Fin.append (fun l u ↦ eA l (anrem_fst u)) (fun l u ↦ anrem_snd u l - F (anrem_fst u) l)
  have hfΓ : ∀ l, AnalyticOnNhd ℂ (fΓ l) UΓ := by
    intro l
    refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
    · intro u hu
      simp only [fΓ, Fin.append_left]
      exact (heA l _ hu.1.2).comp (anrem_fst.analyticAt u)
    · intro u hu
      simp only [fΓ, Fin.append_right]
      refine ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d.n ↦ ℂ) l).analyticAt _
        |>.comp (anrem_snd.analyticAt u)).sub ?_
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d.n ↦ ℂ) l).analyticAt _).comp
        ((hOFsub _ hu.2).comp (anrem_fst.analyticAt u))
  have hUΓeq : ∀ u ∈ UΓ, (u ∈ Γ ↔ ∀ l, fΓ l u = 0) := by
    intro u hu
    change (anrem_fst u ∈ A ∧ anrem_snd u = F (anrem_fst u)) ↔ _
    rw [hUAeq _ hu.1.2]
    constructor
    · rintro ⟨h1, h2⟩ l
      refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
      · simpa [fΓ] using h1 l
      · simp [fΓ, h2]
    · intro h
      refine ⟨fun l ↦ by simpa [fΓ] using h (Fin.castAdd d.n l), funext fun l ↦ ?_⟩
      have := h (Fin.natAdd kA l)
      simp only [fΓ, Fin.append_right] at this
      exact sub_eq_zero.1 this
  -- points of the graph near the base point come from points of `W`
  let ι : X → (Fin (c.n + d.n) → ℂ) := fun x' ↦ Fin.append (c.toFun x') (d.toFun (f x'))
  have hcorr : ∀ u ∈ Γ ∩ UΓ, ∃ x' ∈ W ∩ c.dom, c.toFun x' ∈ O ∧ u = ι x' := by
    rintro u ⟨⟨⟨x', hx'W, hx'u⟩, hsnd⟩, hu⟩
    refine ⟨x', hx'W, ?_, ?_⟩
    · rw [hx'u]; exact hu
    · have hN' := (hO_N x' hx'W.2 (hx'u ▸ hu)).1
      simp only [ι]
      rw [hFeq x' hN', hx'u, ← hsnd, anrem_append_fst_snd]
  have hιΓ : ∀ x', x' ∈ W ∩ c.dom → c.toFun x' ∈ O → ι x' ∈ Γ ∩ UΓ := by
    intro x' hx' hx'O
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change anrem_fst (ι x') ∈ A
      simp only [ι, anrem_fst_append]
      exact mem_image_of_mem c.toFun hx'
    · change anrem_snd (ι x') = F (anrem_fst (ι x'))
      simp only [ι, anrem_snd_append, anrem_fst_append]
      exact hFeq x' (hO_N x' hx'.2 hx'O).1
    · change anrem_fst (ι x') ∈ O
      simpa [ι] using hx'O
  have hdinj : ∀ x' x'', x' ∈ N → x'' ∈ N → d.toFun (f x') = d.toFun (f x'') → f x' = f x'' :=
    fun x' x'' h' h'' h ↦ anrem_chart_injOn d (hNsub h').2 (hNsub h'').2 h
  -- dimensions transported to the graph
  have hfib' : ∀ u ∈ Γ ∩ UΓ,
      adim2_dimension (c.n + d.n) (adim2_germ (c.n + d.n) (Γ ∩ {v | anrem_snd v = anrem_snd u}) u)
        = j := by
    intro u hu
    obtain ⟨x', hx', hx'O, rfl⟩ := hcorr u hu
    obtain ⟨hx'N, hx'B⟩ := hO_N x' hx'.2 hx'O
    have hFx' : AnalyticAt ℂ F (c.toFun x') := hOFsub _ hx'O.2
    have hι : ι x' = Fin.append (c.toFun x') (F (c.toFun x')) := by
      simp only [ι]; rw [hFeq x' hx'N]
    rw [show anrem_snd (ι x') = F (c.toFun x') by simp [hι], ← anrem_graph_inter_fibre, hι,
      anrem_graph_dimension _ F _ hFx', ← hfibB x' ⟨hx'.1, hx'B⟩, hDC S _ i hx'.2]
    congr 1
    apply anrem_germ_congr
    filter_upwards [hO.mem_nhds hx'O] with z hz
    constructor
    · rintro ⟨⟨x'', hx''W, rfl⟩, hFz⟩
      have hx''N := (hO_N x'' hx''W.2 hz).1
      refine ⟨x'', ⟨⟨hx''W.1, ?_⟩, hx''W.2⟩, rfl⟩
      exact hdinj x'' x' hx''N hx'N (by rw [hFeq x'' hx''N, hFeq x' hx'N]; exact hFz)
    · rintro ⟨x'', ⟨⟨hx''W, hfx''⟩, hx''c⟩, rfl⟩
      have hx''N := (hO_N x'' hx''c hz).1
      refine ⟨⟨x'', ⟨hx''W, hx''c⟩, rfl⟩, ?_⟩
      change F (c.toFun x'') = F (c.toFun x')
      rw [← hFeq x'' hx''N, ← hFeq x' hx'N, show f x'' = f x' from hfx'']
  have hdim' : ∀ u ∈ Γ ∩ UΓ, adim2_dimension (c.n + d.n) (adim2_germ (c.n + d.n) Γ u) ≤ q := by
    intro u hu
    obtain ⟨x', hx', hx'O, rfl⟩ := hcorr u hu
    obtain ⟨hx'N, hx'B⟩ := hO_N x' hx'.2 hx'O
    have hι : ι x' = Fin.append (c.toFun x') (F (c.toFun x')) := by
      simp only [ι]; rw [hFeq x' hx'N]
    rw [hι, anrem_graph_dimension _ F _ (hOFsub _ hx'O.2)]
    have := hdimB x' ⟨hx'.1, hx'B⟩
    rwa [hDC S _ i hx'.2] at this
  -- the generic slice through the base point
  set γ := ι x
  have hγ : γ ∈ Γ ∩ UΓ := hιΓ x ⟨hx, hxi⟩ hxO
  obtain ⟨π, ρ, r, ρ', hρ, hr, hρ', hcb, hfinP, hcompP, hcovP, hdimsP⟩ :=
    anrem_slice_local hUΓ hfΓ hUΓeq anrem_snd hγ.1 hγ.2 hfib' hdim'
  set Γ' := Γ ∩ {v | π v = π γ} ∩ Metric.ball γ ρ
  set b := anrem_snd γ
  have hb : b = d.toFun (f x) := by simp [b, γ, ι]
  set C := Γ' ∩ anrem_snd ⁻¹' Metric.ball b r
  set OC := Metric.ball γ ρ ∩ anrem_snd ⁻¹' Metric.ball b r
  have hOC : IsOpen OC := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage anrem_snd.continuous)
  have hballU : Metric.ball γ ρ ⊆ UΓ := Metric.ball_subset_closedBall.trans hcb
  have hCeq : C = Γ ∩ {v | π v = π γ} ∩ OC := by
    ext v; simp only [C, Γ', OC, mem_inter_iff, mem_preimage]; tauto
  have hCloc : ∀ z ∈ OC, anrem_LocEq C z := by
    intro z hz
    rw [hCeq]
    exact anrem_locEq_of_eqns hUΓ hfΓ hUΓeq π (π γ) hOC ⟨hballU hz.1, hz⟩
  have hsnd_img := anrem_finite_projection_local hFM hCS hOC anrem_snd Metric.isOpen_ball
    (fun z hz ↦ hz.2) (fun z hz ↦ ⟨hz.1.2, hz.2⟩) hCloc
    (fun K hK hKb ↦ by
      have := hcompP K hK hKb
      convert this using 1
      ext v
      simp only [C, Γ', mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hKb h2⟩, h2⟩)
    (fun t ht ↦ by
      refine (hfinP t ht).subset fun v hv ↦ ?_
      exact ⟨hv.1.1, hv.2⟩)
  -- the piece of `W` read off the slice
  set Q := {x' | x' ∈ W ∩ c.dom ∧ c.toFun x' ∈ O ∧ ι x' ∈ C}
  have hQW : Q ⊆ W := fun x' hx' ↦ hx'.1.1
  have hQd : ∀ x'' ∈ Q, f x'' ∈ d.dom := fun x'' hx'' ↦
    (hNsub (hO_N x'' hx''.1.2 hx''.2.1).1).2
  have hCQ : ∀ v ∈ C, ∃ x'' ∈ Q, v = ι x'' := by
    intro v hv
    obtain ⟨x'', hx'', hx''O, rfl⟩ := hcorr v ⟨hv.1.1.1, hballU hv.1.2⟩
    exact ⟨x'', ⟨hx'', hx''O, hv⟩, rfl⟩
  have himg : d.toFun '' (f '' Q) = anrem_snd '' C := by
    ext t
    constructor
    · rintro ⟨_, ⟨x'', hx'', rfl⟩, rfl⟩
      exact ⟨ι x'', hx''.2.2, by simp [ι]⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x'', hx'', rfl⟩ := hCQ v hv
      exact ⟨f x'', ⟨x'', hx'', rfl⟩, by simp [ι]⟩
  -- the covering neighbourhood
  have hιcont : ContinuousOn ι (c.dom ∩ c.toFun ⁻¹' O) := by
    have h1 : ContinuousOn c.toFun (c.dom ∩ c.toFun ⁻¹' O) :=
      (anrem_chart_continuousOn c).mono inter_subset_left
    have h2 : ContinuousOn (fun x' ↦ d.toFun (f x')) (c.dom ∩ c.toFun ⁻¹' O) := by
      refine (anrem_chart_continuousOn d).comp hf.1.continuousOn fun x' hx' ↦ ?_
      exact (hNsub (hO_N x' hx'.1 hx'.2).1).2
    refine continuousOn_pi.2 fun l ↦ ?_
    refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
    · simp only [ι, Fin.append_left]
      exact (continuous_apply l).comp_continuousOn h1
    · simp only [ι, Fin.append_right]
      exact (continuous_apply l).comp_continuousOn h2
  set B := (c.dom ∩ c.toFun ⁻¹' O) ∩ ι ⁻¹' (Metric.ball γ ρ' ∩ anrem_snd ⁻¹' Metric.ball b r)
  have hB : IsOpen B := hιcont.isOpen_inter_preimage
    (anrem_chart_isOpen_preimage c hO)
    (Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage anrem_snd.continuous))
  refine ⟨B, Q, hB, ⟨⟨hxi, hxO⟩, Metric.mem_ball_self hρ', Metric.mem_ball_self hr⟩, hQW,
    ?_, ?_, hQd, ?_⟩
  · rintro x' ⟨hx'W, ⟨hx'c, hx'O⟩, hx'b, hx'r⟩
    have hu := hιΓ x' ⟨hx'W, hx'c⟩ hx'O
    obtain ⟨v, hv, hvsnd⟩ := hcovP (ι x') ⟨hu.1, hx'b⟩ hx'r
    obtain ⟨x'', hx'', rfl⟩ := hCQ v ⟨hv, show anrem_snd v ∈ Metric.ball b r by
      rw [hvsnd]; exact hx'r⟩
    refine ⟨x'', hx'', ?_⟩
    have h1 : d.toFun (f x'') = d.toFun (f x') := by simpa [ι] using hvsnd
    exact hdinj x'' x' (hO_N x'' hx''.1.2 hx''.2.1).1 (hO_N x' hx'c hx'O).1 h1
  · refine anrem_anNear_of_chart T jd hxd ?_
    have : f '' Q ∩ d.dom = f '' Q := inter_eq_left.2 fun _ ⟨x'', hx'', h⟩ ↦ h ▸ hQd x'' hx''
    rw [this, himg, ← hb]
    exact hsnd_img b (Metric.mem_ball_self hr)
  · rw [himg]
    refine (anrem_snd.lipschitzWith.dimH_image_le C).trans ?_
    have hC' : C = Γ' ∩ OC := by
      ext v; simp only [C, Γ', OC, mem_inter_iff, mem_preimage]; tauto
    rw [hC']
    refine anrem_dimH_le Γ' OC hOC (q - j) fun z hz ↦ ⟨?_, hdimsP z hz.1⟩
    exact anrem_locEq_of_eqns hUΓ hfΓ hUΓeq π (π γ) Metric.isOpen_ball
      ⟨hballU hz.1.2, hz.1.2⟩

theorem anrem_anNear_biUnion (T : an_ReducedSpace Y) {ι : Type*} (s : Finset ι) {A : ι → Set Y}
    {y : Y} (h : ∀ i ∈ s, anrem_AnNear T (A i) y) : anrem_AnNear T (⋃ i ∈ s, A i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using anrem_anNear_of_not_mem T isClosed_empty (notMem_empty y)
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact anrem_anNear_union T (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **Images over constant fibre dimension.** If the fibres of a proper holomorphic map on a
closed analytic `W` have dimension `j` at all points over an open `Y₀`, and `W` has dimension at
most `q` there, then `f(W)` is analytic at every point of `Y₀`, of dimension at most `q - j`. -/
theorem anrem_partA (hFM : anrem_FiniteMappingStmt) (hCS : anrem_ClosedSubspaceStmt)
    (hDC : anrem_DimChartStmt.{u}) (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsProperHom S T f) {W : Set X} (hW : an_IsClosedAnalytic S W) {j q : ℕ}
    {Y₀ : Set Y} (hY₀ : IsOpen Y₀)
    (hfib : ∀ x ∈ W ∩ f ⁻¹' Y₀, an_dimAt S (W ∩ f ⁻¹' {f x}) x = j)
    (hdim : ∀ x ∈ W ∩ f ⁻¹' Y₀, an_dimAt S W x ≤ q) {y : Y} (hy : y ∈ Y₀) :
    anrem_AnNear T (f '' W) y ∧ an_dimAt T (f '' W) y ≤ ((q - j : ℕ) : WithBot ℕ∞) := by
  classical
  set jd := T.atlas.chartAt y
  set d := T.atlas.chart jd
  have hyd : y ∈ d.dom := T.atlas.mem_chartAt y
  have hclosed : IsClosed (f '' W) := hf.1.isClosedMap W hW.1
  -- an open neighbourhood on which the image is a finite union of slice images
  obtain ⟨V, hV, hyV, t, Q, hQW, hQnear, hQd, hQdim, hcover⟩ : ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      ∃ (t : Finset X) (Q : X → Set X), (∀ x ∈ t, Q x ⊆ W) ∧
        (∀ x ∈ t, anrem_AnNear T (f '' Q x) y) ∧ (∀ x ∈ t, ∀ x'' ∈ Q x, f x'' ∈ d.dom) ∧
        (∀ x ∈ t, dimH (d.toFun '' (f '' Q x)) ≤ ((2 * (q - j) : ℕ) : ENNReal)) ∧
        f '' W ∩ V ⊆ ⋃ x ∈ t, f '' Q x := by
    by_cases hyW : y ∈ f '' W
    swap
    · exact ⟨(f '' W)ᶜ, hclosed.isOpen_compl, hyW, ∅, fun _ ↦ ∅, by simp, by simp, by simp,
        by simp, fun z hz ↦ (hz.2 hz.1).elim⟩
    have hΦ : IsCompact (W ∩ f ⁻¹' {y}) :=
      (hf.1.isCompact_preimage isCompact_singleton).inter_left hW.1
    have hloc : ∀ x ∈ W ∩ f ⁻¹' {y}, ∃ B Q : Set X, IsOpen B ∧ x ∈ B ∧ Q ⊆ W ∧
        (∀ x' ∈ W ∩ B, ∃ x'' ∈ Q, f x'' = f x') ∧ anrem_AnNear T (f '' Q) (f x) ∧
        (∀ x'' ∈ Q, f x'' ∈ d.dom) ∧
        dimH (d.toFun '' (f '' Q)) ≤ ((2 * (q - j) : ℕ) : ENNReal) := by
      intro x hx
      have hfx : f x = y := hx.2
      have hxY : f x ∈ Y₀ := hfx ▸ hy
      exact anrem_partA_local hFM hCS hDC S T hf.2 hW (hY₀.preimage hf.2.1)
        (fun x' hx' ↦ hfib x' ⟨hx'.1, hx'.2⟩) (fun x' hx' ↦ hdim x' ⟨hx'.1, hx'.2⟩) hx.1 hxY jd
        (hfx ▸ hyd)
    choose! B Q hBo hxB hQW hcov hQnear hQd hQdim using hloc
    obtain ⟨t, htΦ, hΦt⟩ := hΦ.elim_nhds_subcover B fun x hx ↦ (hBo x hx).mem_nhds (hxB x hx)
    set R := W \ ⋃ x ∈ t, B x
    have hR : IsClosed R := hW.1.sdiff (isOpen_biUnion fun x hx ↦ hBo x (htΦ x hx))
    have hyR : y ∉ f '' R := by
      rintro ⟨x', hx'R, hx'y⟩
      exact hx'R.2 (hΦt ⟨hx'R.1, hx'y⟩)
    refine ⟨(f '' R)ᶜ, (hf.1.isClosedMap R hR).isOpen_compl, hyR, t, Q,
      fun x hx ↦ hQW x (htΦ x hx), fun x hx ↦ ?_, fun x hx ↦ hQd x (htΦ x hx),
      fun x hx ↦ hQdim x (htΦ x hx), ?_⟩
    · have := hQnear x (htΦ x hx)
      rwa [(htΦ x hx).2] at this
    · rintro _ ⟨⟨x', hx'W, rfl⟩, hnot⟩
      have hx' : x' ∈ ⋃ x ∈ t, B x := by
        by_contra hc
        exact hnot ⟨x', ⟨hx'W, hc⟩, rfl⟩
      obtain ⟨x, hxt, hx'B⟩ := mem_iUnion₂.1 hx'
      obtain ⟨x'', hx''Q, hfx''⟩ := hcov x (htΦ x hxt) x' ⟨hx'W, hx'B⟩
      exact mem_iUnion₂.2 ⟨x, hxt, x'', hx''Q, hfx''⟩
  have heqV : f '' W ∩ V = (⋃ x ∈ t, f '' Q x) ∩ V := by
    ext z
    constructor
    · intro hz; exact ⟨hcover hz, hz.2⟩
    · rintro ⟨hz, hzV⟩
      obtain ⟨x, hxt, hzQ⟩ := mem_iUnion₂.1 hz
      exact ⟨image_mono (hQW x hxt) hzQ, hzV⟩
  have hnear : anrem_AnNear T (f '' W) y :=
    anrem_anNear_mono_nhd T hV hyV heqV.symm (anrem_anNear_biUnion T t hQnear)
  refine ⟨hnear, ?_⟩
  obtain ⟨O', hO', hO'eq⟩ := anrem_chart_nhd d hV
  have hyO' : d.toFun y ∈ O' := by
    have : y ∈ d.dom ∩ V := ⟨hyd, hyV⟩
    rw [← hO'eq] at this; exact this.2
  change adim2_dimension d.n (adim2_germ d.n (d.toFun '' (f '' W ∩ d.dom)) (d.toFun y)) ≤ _
  refine anrem_dimension_le_of_dimH (anrem_anNear_chart T hnear jd hyd)
    (hO'.mem_nhds hyO') (q - j) ?_
  have hsub : d.toFun '' (f '' W ∩ d.dom) ∩ O' ⊆ ⋃ x ∈ (t : Set X), d.toFun '' (f '' Q x) := by
    rintro _ ⟨⟨y', ⟨hy'W, hy'd⟩, rfl⟩, hy'O⟩
    have hy'V : y' ∈ V := by
      have : y' ∈ d.dom ∩ d.toFun ⁻¹' O' := ⟨hy'd, hy'O⟩
      rw [hO'eq] at this; exact this.2
    obtain ⟨x, hxt, hy'Q⟩ := mem_iUnion₂.1 (hcover ⟨hy'W, hy'V⟩)
    exact mem_iUnion₂.2 ⟨x, hxt, mem_image_of_mem _ hy'Q⟩
  refine (dimH_mono hsub).trans ?_
  rw [dimH_bUnion t.countable_toSet]
  exact iSup₂_le fun x hx ↦ hQdim x hx

/-- The locus of points of `W` where the fibre of `f` has dimension at least `k`. -/
def anrem_fibreLocus (S : an_ReducedSpace X) (f : X → Y) (W : Set X) (k : ℕ) : Set X :=
  {x' | x' ∈ W ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (W ∩ f ⁻¹' {f x'}) x'}

theorem anrem_dimension_cases {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (hy : y ∈ A) :
    ∃ e : ℕ, e ≤ n ∧ adim2_dimension n (adim2_germ n A y) = e := by
  have : Nontrivial (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n A y)) :=
    Ideal.Quotient.nontrivial_iff.2 (adim9b_germ_ideal_ne_top n A y hy)
  have hle : adim2_dimension n (adim2_germ n A y) ≤ (n : WithBot ℕ∞) := by
    rw [← adim6_parameter_dimension n]
    exact ringKrullDim_quotient_le _
  exact anr_dim_cases n hle

/-- **The large part of a fibre lies in the fibre-dimension locus.** -/
theorem anrem_fibreLocus_dim (hDC : anrem_DimChartStmt.{u}) (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) {f : X → Y} (hf : an_IsHom S T f) {W : Set X}
    (hW : an_IsClosedAnalytic S W) (k : ℕ) {x : X} (hx : x ∈ W)
    (hk : ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (W ∩ f ⁻¹' {f x}) x) :
    ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (anrem_fibreLocus S f W k ∩ f ⁻¹' {f x}) x := by
  set i := S.atlas.chartAt x
  set c := S.atlas.chart i
  have hxi : x ∈ c.dom := S.atlas.mem_chartAt x
  have hΦ := anrem_isClosedAnalytic_fibre S T hf hW (f x)
  set A := c.toFun '' (W ∩ f ⁻¹' {f x} ∩ c.dom)
  have hxA : c.toFun x ∈ A := ⟨x, ⟨⟨hx, rfl⟩, hxi⟩, rfl⟩
  have hloc : anrem_LocEq A (c.toFun x) := anrem_anNear_chart S (hΦ.2 x ⟨hx, rfl⟩) i hxi
  have hk' : ((k : ℕ) : WithBot ℕ∞) ≤ adim2_dimension c.n (adim2_germ c.n A (c.toFun x)) := hk
  obtain ⟨Q, hQ, hkQ⟩ := anrem_exists_minimalPrime_ge hk'
  obtain ⟨e, he⟩ := anrem_quotient_dim_cases Q hQ.1.1
  obtain ⟨C, hxC, hCA, -, hCdim, -⟩ := anrem_component hxA hloc hQ he
  obtain ⟨O₁, hO₁sub, hO₁, hxO₁⟩ := eventually_nhds_iff.1 (hCA.and (hCdim.mono fun z hz hzC ↦
    anrem_dimension_eq_of_pure hzC (hz hzC)))
  change ((k : ℕ) : WithBot ℕ∞) ≤ adim2_dimension c.n (adim2_germ c.n
    (c.toFun '' (anrem_fibreLocus S f W k ∩ f ⁻¹' {f x} ∩ c.dom)) (c.toFun x))
  have hke : ((k : ℕ) : WithBot ℕ∞) ≤ e := he ▸ hkQ
  refine hke.trans ?_
  rw [← (hO₁sub _ hxO₁).2 hxC]
  apply anrem_dimension_mono
  filter_upwards [hO₁.mem_nhds hxO₁] with z hz hzC
  obtain ⟨x', ⟨⟨hx'W, hx'f⟩, hx'c⟩, rfl⟩ := (hO₁sub z hz).1 hzC
  refine ⟨x', ⟨⟨⟨hx'W, ?_⟩, hx'f⟩, hx'c⟩, rfl⟩
  have hfx' : f x' = f x := hx'f
  rw [hfx', hDC S _ i hx'c]
  refine hke.trans ?_
  rw [← (hO₁sub _ hz).2 hzC]
  apply anrem_dimension_mono
  filter_upwards [hO₁.mem_nhds hz] with w hw hwC
  exact (hO₁sub w hw).1 hwC

theorem anrem_succ_le_of_not_le {a : WithBot ℕ∞} {n : ℕ} (h : ¬ a ≤ (n : WithBot ℕ∞)) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd bot_le h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact le_top
    | coe a =>
      have : ¬ a ≤ n := fun h' ↦ h (by exact_mod_cast h')
      exact_mod_cast (show n + 1 ≤ a by omega)

/-- **Dimension is at most the dimension of the image plus that of the fibre.** If the fibre of
`f` on `W` through `x` has dimension at most `k` and a set `I` containing the chart image of `f(W)`
near `f x` has dimension at most `e` there, then `W` has dimension at most `e + k` at `x`. -/
theorem anrem_dim_le_image_add (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) {f : X → Y} (hf : an_IsHom S T f) {W : Set X}
    (hW : an_IsClosedAnalytic S W) {x : X} (hx : x ∈ W) {k : ℕ}
    (hfibk : an_dimAt S (W ∩ f ⁻¹' {f x}) x ≤ ((k : ℕ∞) : WithBot ℕ∞)) (jd : T.atlas.ι)
    (hxd : f x ∈ (T.atlas.chart jd).dom) {I : Set (Fin (T.atlas.chart jd).n → ℂ)}
    (hI : ∀ᶠ x' in 𝓝 x, x' ∈ W → (T.atlas.chart jd).toFun (f x') ∈ I)
    (hIloc : anrem_LocEq I ((T.atlas.chart jd).toFun (f x))) {e : ℕ}
    (he : adim2_dimension _ (adim2_germ _ I ((T.atlas.chart jd).toFun (f x))) ≤ e) :
    an_dimAt S W x ≤ ((e + k : ℕ) : WithBot ℕ∞) := by
  classical
  set i := S.atlas.chartAt x
  set c := S.atlas.chart i
  have hxi : x ∈ c.dom := S.atlas.mem_chartAt x
  obtain ⟨N, hN, hxN, hNsub, F, hF, hFeq⟩ := anrem_hom_chart_rep S T hf i hxi jd hxd
  obtain ⟨UA, hUA, hxUA, kA, eA, heA, hUAeq⟩ := anrem_anNear_chart S (hW.2 x hx) i hxi
  obtain ⟨OF, hOFsub, hOF, hxOF⟩ := eventually_nhds_iff.1 hF.eventually_analyticAt
  obtain ⟨NI, hNIsub, hNI, hxNI⟩ := eventually_nhds_iff.1 hI
  obtain ⟨O₁, hO₁, hO₁eq⟩ := anrem_chart_nhd c (hN.inter hNI)
  set O := O₁ ∩ UA ∩ OF
  have hO : IsOpen O := (hO₁.inter hUA).inter hOF
  have hxO₁ : c.toFun x ∈ O₁ := by
    have : x ∈ c.dom ∩ (N ∩ NI) := ⟨hxi, hxN, hxNI⟩
    rw [← hO₁eq] at this; exact this.2
  have hxO : c.toFun x ∈ O := ⟨⟨hxO₁, hxUA⟩, hxOF⟩
  have hO_N : ∀ x', x' ∈ c.dom → c.toFun x' ∈ O → x' ∈ N ∧ x' ∈ NI := by
    intro x' hx'c hx'O
    have : x' ∈ c.dom ∩ c.toFun ⁻¹' O₁ := ⟨hx'c, hx'O.1.1⟩
    rw [hO₁eq] at this; exact this.2
  set A := c.toFun '' (W ∩ c.dom)
  set Γ := anrem_graph A F
  set UΓ : Set (Fin (c.n + (T.atlas.chart jd).n) → ℂ) := anrem_fst ⁻¹' O
  have hUΓ : IsOpen UΓ := hO.preimage anrem_fst.continuous
  let fΓ : Fin (kA + (T.atlas.chart jd).n) → (Fin (c.n + (T.atlas.chart jd).n) → ℂ) → ℂ :=
    Fin.append (fun l u ↦ eA l (anrem_fst u)) (fun l u ↦ anrem_snd u l - F (anrem_fst u) l)
  have hfΓ : ∀ l, AnalyticOnNhd ℂ (fΓ l) UΓ := by
    intro l
    refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
    · intro u hu
      simp only [fΓ, Fin.append_left]
      exact (heA l _ hu.1.2).comp (anrem_fst.analyticAt u)
    · intro u hu
      simp only [fΓ, Fin.append_right]
      refine ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (T.atlas.chart jd).n ↦ ℂ) l).analyticAt _
        |>.comp (anrem_snd.analyticAt u)).sub ?_
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (T.atlas.chart jd).n ↦ ℂ) l).analyticAt _).comp
        ((hOFsub _ hu.2).comp (anrem_fst.analyticAt u))
  have hUΓeq : ∀ u ∈ UΓ, (u ∈ Γ ↔ ∀ l, fΓ l u = 0) := by
    intro u hu
    change (anrem_fst u ∈ A ∧ anrem_snd u = F (anrem_fst u)) ↔ _
    rw [hUAeq _ hu.1.2]
    constructor
    · rintro ⟨h1, h2⟩ l
      refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
      · simpa [fΓ] using h1 l
      · simp [fΓ, h2]
    · intro h
      refine ⟨fun l ↦ by simpa [fΓ] using h (Fin.castAdd (T.atlas.chart jd).n l), funext fun l ↦ ?_⟩
      have := h (Fin.natAdd kA l)
      simp only [fΓ, Fin.append_right] at this
      exact sub_eq_zero.1 this
  set γ : Fin (c.n + (T.atlas.chart jd).n) → ℂ := Fin.append (c.toFun x) (F (c.toFun x))
  have hγΓ : γ ∈ Γ := anrem_append_mem_graph ⟨x, ⟨hx, hxi⟩, rfl⟩
  have hγU : γ ∈ UΓ := by simpa [γ, UΓ] using hxO
  have hsndγ : anrem_snd γ = (T.atlas.chart jd).toFun (f x) := by
    simp only [γ, anrem_snd_append]; exact (hFeq x hxN).symm
  -- the fibre of the graph through the base point
  set Φ := Γ ∩ {u | anrem_snd u = anrem_snd γ}
  have hΦdim : adim2_dimension (c.n + (T.atlas.chart jd).n) (adim2_germ (c.n + (T.atlas.chart jd).n) Φ γ) ≤ k := by
    have hgerm : adim2_germ (c.n + (T.atlas.chart jd).n) Φ γ =
        adim2_germ (c.n + (T.atlas.chart jd).n) (anrem_graph (A ∩ {z | F z = F (c.toFun x)}) F) γ := by
      have : anrem_snd γ = F (c.toFun x) := by simp [γ]
      rw [anrem_graph_inter_fibre, ← this]
    rw [hgerm, anrem_graph_dimension _ F _ hF]
    refine le_of_eq_of_le ?_ hfibk
    change _ = adim2_dimension c.n (adim2_germ c.n (c.toFun '' (W ∩ f ⁻¹' {f x} ∩ c.dom))
      (c.toFun x))
    congr 1
    apply anrem_germ_congr
    filter_upwards [hO.mem_nhds hxO] with z hz
    constructor
    · rintro ⟨⟨x'', hx''W, rfl⟩, hFz⟩
      have hx''N := (hO_N x'' hx''W.2 hz).1
      refine ⟨x'', ⟨⟨hx''W.1, ?_⟩, hx''W.2⟩, rfl⟩
      exact anrem_chart_injOn (T.atlas.chart jd) (hNsub hx''N).2 (hNsub hxN).2
        (by rw [hFeq x'' hx''N, hFeq x hxN]; exact hFz)
    · rintro ⟨x'', ⟨⟨hx''W, hfx''⟩, hx''c⟩, rfl⟩
      have hx''N := (hO_N x'' hx''c hz).1
      refine ⟨⟨x'', ⟨hx''W, hx''c⟩, rfl⟩, ?_⟩
      change F (c.toFun x'') = F (c.toFun x)
      rw [← hFeq x'' hx''N, ← hFeq x hxN, show f x'' = f x from hfx'']
  have hΦloc : anrem_LocEq Φ γ := anrem_locEq_fibre hUΓ hfΓ hUΓeq anrem_snd _ hγU
  obtain ⟨U₁, hU₁sub, hU₁, hγU₁⟩ := eventually_nhds_iff.1
    ((anrem_dimension_upper hΦloc hΦdim).and (hUΓ.mem_nhds hγU))
  -- a generic slice isolating the base point in its fibre
  have hloc₀ : ∀ y ∈ Φ ∩ U₁, ∃ U' : Set (Fin (c.n + (T.atlas.chart jd).n) → ℂ), IsOpen U' ∧ y ∈ U' ∧ ∃ (m' : ℕ)
      (g : Fin m' → (Fin (c.n + (T.atlas.chart jd).n) → ℂ) → ℂ), (∀ l, AnalyticOnNhd ℂ (g l) U') ∧
        ∀ z ∈ U', (z ∈ Φ ∩ U₁ ↔ ∀ l, g l z = 0) := fun y hy ↦
    anrem_locEq_of_eqns hUΓ hfΓ hUΓeq anrem_snd (anrem_snd γ) hU₁ ⟨(hU₁sub y hy.2).2, hy.2⟩
  obtain ⟨π, hπ⟩ := anr_slice (fun _ : Unit ↦ Φ ∩ U₁) (fun _ ↦ γ) (fun _ ↦ k)
    (fun _ ↦ hloc₀) (fun _ y hy ↦ by
      rw [anrem_germ_inter_nhds _ U₁ y (hU₁.mem_nhds hy.2)]
      exact (anrem_dimension_le_iff _ y _).1 (hU₁sub y hy.2).1) k
  have hiso0 : ∀ᶠ z in 𝓝 γ, z ∈ Φ ∩ U₁ ∩ {z | π z = π γ} → z = γ := by
    have hmem : γ ∈ Φ ∩ U₁ ∩ {z | π z = π γ} := ⟨⟨⟨hγΓ, rfl⟩, hγU₁⟩, rfl⟩
    refine anr_isolated_of_dims _ γ hmem fun Q hQ ↦ ?_
    have := hπ () γ hmem Q hQ
    simpa using this
  set G : (Fin (c.n + (T.atlas.chart jd).n) → ℂ) →L[ℂ] (Fin ((T.atlas.chart jd).n + k) → ℂ) := anrem_appendL anrem_snd π
  have hisoG : ∀ᶠ u in 𝓝 γ, u ∈ Γ → G u = G γ → u = γ := by
    filter_upwards [hiso0, hU₁.mem_nhds hγU₁] with u h1 h2 huΓ hGu
    simp only [G, anrem_appendL_apply] at hGu
    obtain ⟨hs, hp⟩ := anrem_append_inj hGu
    exact h1 ⟨⟨⟨huΓ, hs⟩, h2⟩, hp⟩
  -- the image lies in the product of `I` with `ℂᵏ`
  have hS : ∀ᶠ u in 𝓝 γ, u ∈ Γ → G u ∈ (anrem_fst ⁻¹' I : Set (Fin ((T.atlas.chart jd).n + k) → ℂ)) := by
    filter_upwards [hUΓ.mem_nhds hγU] with u hu huΓ
    simp only [G, mem_preimage, anrem_appendL_apply, anrem_fst_append]
    obtain ⟨x', hx', hx'O, rfl⟩ : ∃ x' ∈ W ∩ c.dom, c.toFun x' ∈ O ∧
        u = Fin.append (c.toFun x') ((T.atlas.chart jd).toFun (f x')) := by
      obtain ⟨⟨x', hx'W, hx'u⟩, hsnd⟩ := huΓ
      refine ⟨x', hx'W, hx'u ▸ hu, ?_⟩
      have hN' := (hO_N x' hx'W.2 (hx'u ▸ hu)).1
      rw [hFeq x' hN', hx'u, ← hsnd, anrem_append_fst_snd]
    simp only [anrem_snd_append]
    exact hNIsub x' (hO_N x' hx'.2 hx'O).2 hx'.1
  -- the dimension count
  by_contra hcon
  have hWγ : an_dimAt S W x = adim2_dimension (c.n + (T.atlas.chart jd).n) (adim2_germ (c.n + (T.atlas.chart jd).n) Γ γ) :=
    (anrem_graph_dimension A F _ hF).symm
  have h1 := anrem_succ_le_of_not_le hcon
  rw [hWγ] at h1
  obtain ⟨Q, hQ, hQdim⟩ := anrem_exists_minimalPrime_ge h1
  have hγloc : anrem_LocEq Γ γ := ⟨UΓ, hUΓ, hγU, _, fΓ, hfΓ, hUΓeq⟩
  have hD1 := anrem_minimalPrime_le_image hγΓ hγloc G hisoG _ hS Q hQ
  obtain ⟨UI, hUI, hbUI, mI, fI, hfI, hUIeq⟩ := hIloc
  obtain ⟨Ue, hUesub, hUe, hbUe⟩ := eventually_nhds_iff.1
    (anrem_dimension_upper ⟨UI, hUI, hbUI, mI, fI, hfI, hUIeq⟩ he)
  have hbI : (T.atlas.chart jd).toFun (f x) ∈ I := hNIsub x hxNI hx
  have hD3 := anrem_dimension_prod_le (j := k) hbI (hUI.inter hUe) ⟨hbUI, hbUe⟩
    (fun l ↦ (hfI l).mono inter_subset_left) (fun z hz ↦ hUIeq z hz.1) e
    (fun z hz ↦ hUesub z hz.2.2) (π γ)
  have hGγ : G γ = Fin.append ((T.atlas.chart jd).toFun (f x)) (π γ) := by
    simp [G, anrem_appendL_apply, hsndγ]
  rw [hGγ] at hD1
  have h3 := hQdim.trans (hD1.trans hD3)
  have h4 : e + k + 1 ≤ e + k := by exact_mod_cast h3
  omega

/-- Germ dimension is monotone in the set. -/
theorem anrem_dimAt_mono (S : an_ReducedSpace X) {Z Z' : Set X} (h : Z ⊆ Z') (x : X) :
    an_dimAt S Z x ≤ an_dimAt S Z' x :=
  anrem_dimension_mono (Eventually.of_forall fun _ ⟨w, hw, hwz⟩ ↦ ⟨w, ⟨h hw.1, hw.2⟩, hwz⟩)

/-- Closures commute with charts on the chart domain. -/
theorem anrem_mem_closure_chart_iff (c : an_Chart X) (M : Set X) {x : X} (hx : x ∈ c.dom) :
    x ∈ closure M ↔ c.toFun x ∈ closure (c.toFun '' (M ∩ c.dom)) := by
  constructor
  · intro h
    have h1 : x ∈ closure (M ∩ c.dom) := by
      rw [mem_closure_iff_nhds] at h ⊢
      intro t ht
      obtain ⟨w, hw⟩ := h (t ∩ c.dom) (Filter.inter_mem ht (c.isOpen_dom.mem_nhds hx))
      exact ⟨w, hw.1.1, hw.2, hw.1.2⟩
    exact ((anrem_chart_continuousOn c x hx).mono inter_subset_right).mem_closure_image h1
  · intro h
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨O', hO't, hO'o, hxO'⟩ := mem_nhds_iff.1 ht
    obtain ⟨O, hO, hOeq⟩ := anrem_chart_nhd c hO'o
    have hxO : c.toFun x ∈ O := by
      have : x ∈ c.dom ∩ O' := ⟨hx, hxO'⟩
      rw [← hOeq] at this; exact this.2
    obtain ⟨_, hwO, ⟨w, ⟨hwM, hwc⟩, rfl⟩⟩ := mem_closure_iff_nhds.1 h O (hO.mem_nhds hxO)
    have : w ∈ c.dom ∩ O' := by rw [← hOeq]; exact ⟨hwc, hwO⟩
    exact ⟨w, hO't this.2, hwM⟩

/-- The chart image of a closed analytic set has local equations at every point of the open set
carrying the local model. -/
theorem anrem_chart_image_locEq (S : an_ReducedSpace X) {W : Set X} (hW : an_IsClosedAnalytic S W)
    (i : S.atlas.ι) {z : Fin (S.atlas.chart i).n → ℂ} (hz : z ∈ (S.atlas.chart i).U) :
    anrem_LocEq ((S.atlas.chart i).toFun '' (W ∩ (S.atlas.chart i).dom)) z := by
  by_cases hzm : z ∈ (S.atlas.chart i).toFun '' (S.atlas.chart i).dom
  · obtain ⟨x, hx, rfl⟩ := hzm
    have hnear : anrem_AnNear S W x := by
      by_cases hxW : x ∈ W
      · exact hW.2 x hxW
      · exact anrem_anNear_of_not_mem S hW.1 hxW
    exact anrem_anNear_chart S hnear i hx
  · rw [(S.atlas.chart i).image_eq] at hzm
    have : ¬ (S.atlas.chart i).eqns z = 0 := fun h ↦ hzm ⟨hz, h⟩
    obtain ⟨l, hl⟩ : ∃ l, (S.atlas.chart i).eqns z l ≠ 0 := by
      by_contra h; push Not at h; exact this (funext h)
    have hcont : ContinuousAt (fun w ↦ (S.atlas.chart i).eqns w l) z :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (S.atlas.chart i).k ↦ ℂ) l).analyticAt _).comp
        ((S.atlas.chart i).analyticOnNhd_eqns z hz) |>.continuousAt
    obtain ⟨O, hOsub, hO, hzO⟩ := eventually_nhds_iff.1 (hcont.eventually_ne hl)
    refine ⟨O, hO, hzO, 1, fun _ _ ↦ 1, fun _ ↦ analyticOnNhd_const, fun w hw ↦ ?_⟩
    simp only [one_ne_zero, forall_const, iff_false]
    rintro ⟨x, ⟨-, hx⟩, rfl⟩
    have : (S.atlas.chart i).toFun x ∈ (S.atlas.chart i).toFun '' (S.atlas.chart i).dom := mem_image_of_mem _ hx
    rw [(S.atlas.chart i).image_eq] at this
    exact hOsub _ hw (congrFun this.2 l)

/-- **The lower-dimensional part of a closed analytic set.** If a closed analytic set has
dimension at most `e + 1`, the closure of its points of dimension at most `e` is closed analytic
of dimension at most `e`. -/
theorem anrem_lowClosure (hDC : anrem_DimChartStmt.{u}) (S : an_ReducedSpace X) {W : Set X}
    (hW : an_IsClosedAnalytic S W) {e : ℕ}
    (hdim : ∀ x ∈ W, an_dimAt S W x ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    an_IsClosedAnalytic S (closure {x | x ∈ W ∧ an_dimAt S W x ≤ (e : WithBot ℕ∞)}) ∧
      closure {x | x ∈ W ∧ an_dimAt S W x ≤ (e : WithBot ℕ∞)} ⊆ W ∧
      ∀ x ∈ closure {x | x ∈ W ∧ an_dimAt S W x ≤ (e : WithBot ℕ∞)},
        an_dimAt S (closure {x | x ∈ W ∧ an_dimAt S W x ≤ (e : WithBot ℕ∞)}) x ≤
          (e : WithBot ℕ∞) := by
  set low := {x | x ∈ W ∧ an_dimAt S W x ≤ (e : WithBot ℕ∞)}
  have hLW : closure low ⊆ W := closure_minimal (fun x hx ↦ hx.1) hW.1
  -- the chart picture at a point of the closure
  have key : ∀ x ∈ closure low, anrem_LocEq ((S.atlas.chart (S.atlas.chartAt x)).toFun ''
      (closure low ∩ (S.atlas.chart (S.atlas.chartAt x)).dom))
        ((S.atlas.chart (S.atlas.chartAt x)).toFun x) ∧
      an_dimAt S (closure low) x ≤ (e : WithBot ℕ∞) := by
    intro x hx
    set i := S.atlas.chartAt x
    set c := S.atlas.chart i
    have hxi : x ∈ c.dom := S.atlas.mem_chartAt x
    set A := c.toFun '' (W ∩ c.dom)
    have hxA : c.toFun x ∈ A := ⟨x, ⟨hLW hx, hxi⟩, rfl⟩
    have hxU : c.toFun x ∈ c.U := by
      have : c.toFun x ∈ c.toFun '' c.dom := mem_image_of_mem _ hxi
      rw [c.image_eq] at this; exact this.1
    have hAloc : ∀ z ∈ c.U, anrem_LocEq A z := fun z hz ↦ anrem_chart_image_locEq S hW i hz
    have hdimA : ∀ᶠ z in 𝓝 (c.toFun x),
        adim2_dimension c.n (adim2_germ c.n A z) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
      filter_upwards [c.isOpen_U.mem_nhds hxU] with z hz
      by_cases hzA : z ∈ A
      · obtain ⟨x', hx', rfl⟩ := hzA
        rw [← hDC S W i hx'.2]
        exact hdim x' hx'.1
      · rw [anrem_germ_eq_bot_of_not_mem (hAloc z hz) hzA]
        have : adim2_ideal c.n (⊥ : adim2_SetGerm c.n) = ⊤ := by
          ext a
          simp only [Submodule.mem_top, iff_true]
          exact (bot_le : (⊥ : adim2_SetGerm c.n) ≤ adim2_zero c.n a)
        change ringKrullDim (AnalyticGerm c.n ⧸ adim2_ideal c.n ⊥) ≤ _
        rw [this]
        have : Subsingleton (AnalyticGerm c.n ⧸ (⊤ : Ideal (AnalyticGerm c.n))) := by
          infer_instance
        rw [ringKrullDim_eq_bot_of_subsingleton]
        exact bot_le
    obtain ⟨-, -, hLloc, hLdim⟩ := anrem_split hxA (hAloc _ hxU) hdimA
    -- the chart image of the closure of the low points is the closure of the low points of `A`
    have hmodel : ∀ z ∈ c.U, z ∈ closure (c.toFun '' c.dom) → z ∈ c.toFun '' c.dom := by
      intro z hz hzc
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
    set lowA := {z | z ∈ A ∧ adim2_dimension c.n (adim2_germ c.n A z) ≤ (e : WithBot ℕ∞)}
    have hlowA : c.toFun '' (low ∩ c.dom) = lowA := by
      ext w
      constructor
      · rintro ⟨x', ⟨⟨hx'W, hx'd⟩, hx'c⟩, rfl⟩
        exact ⟨⟨x', ⟨hx'W, hx'c⟩, rfl⟩, by rw [← hDC S W i hx'c]; exact hx'd⟩
      · rintro ⟨⟨x', hx', rfl⟩, hd⟩
        exact ⟨x', ⟨⟨hx'.1, by rw [hDC S W i hx'.2]; exact hd⟩, hx'.2⟩, rfl⟩
    have himg : ∀ᶠ z in 𝓝 (c.toFun x), z ∈ c.toFun '' (closure low ∩ c.dom) ↔ z ∈ closure lowA := by
      filter_upwards [c.isOpen_U.mem_nhds hxU] with z hz
      constructor
      · rintro ⟨x', ⟨hx'L, hx'c⟩, rfl⟩
        rw [← hlowA]
        exact (anrem_mem_closure_chart_iff c low hx'c).1 hx'L
      · intro hzc
        have hzA : z ∈ c.toFun '' c.dom := by
          refine hmodel z hz (closure_mono (fun w hw ↦ ?_) hzc)
          obtain ⟨x', hx', rfl⟩ := hw.1
          exact mem_image_of_mem _ hx'.2
        obtain ⟨x', hx'c, rfl⟩ := hzA
        refine ⟨x', ⟨?_, hx'c⟩, rfl⟩
        rw [anrem_mem_closure_chart_iff c low hx'c, hlowA]
        exact hzc
    have hxL : c.toFun x ∈ closure lowA := (himg.self_of_nhds).1 ⟨x, ⟨hx, hxi⟩, rfl⟩
    obtain ⟨O, hOsub, hO, hxO⟩ := eventually_nhds_iff.1 himg
    refine ⟨anrem_locEq_congr hO hxO (by
      ext z; exact ⟨fun h ↦ ⟨(hOsub z h.2).2 h.1, h.2⟩, fun h ↦ ⟨(hOsub z h.2).1 h.1, h.2⟩⟩)
      hLloc, ?_⟩
    change adim2_dimension c.n (adim2_germ c.n (c.toFun '' (closure low ∩ c.dom)) (c.toFun x)) ≤ _
    rw [anrem_germ_congr himg]
    exact hLdim.self_of_nhds hxL
  refine ⟨⟨isClosed_closure, fun x hx ↦ ?_⟩, hLW, fun x hx ↦ (key x hx).2⟩
  exact anrem_anNear_of_chart S (S.atlas.chartAt x) (S.atlas.mem_chartAt x) (key x hx).1

end Rep

end HodgeLean.Foundations.Analytic
