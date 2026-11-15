import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceDefs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs

/-! # Helpers for Remmert's proper mapping theorem on reduced complex analytic spaces

Lane `an-rem`, prefix `anrem_`. Chart bookkeeping, finite sets as closed analytic sets, isolated
points of zero-dimensional germs, the zero-dimensional case of the local proper mapping theorem
(with local compactness of the target as a hypothesis), proper restrictions and closed analytic
subsets of open subsets of manifolds, and the hyperbola computations.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

universe u v

/-! ### Germs of Krull dimension at most zero -/

theorem anrem_ideal_value_eq_zero {n : ℕ} {A : Set (Fin n → ℂ)} {p : Fin n → ℂ} (hp : p ∈ A)
    {g : AnalyticGerm n} (hg : g ∈ adim2_ideal n (adim2_germ n A p)) :
    analyticGermValue n g = 0 := by
  obtain ⟨f, -, hfg⟩ := g.2
  change adim2_germ n A p ≤ g.1.map (· = 0) at hg
  rw [← hfg, adim2_germ, Germ.map_coe, Germ.coe_le] at hg
  have h0 := hg.self_of_nhds (by simpa using hp)
  change g.1.value = 0
  rw [← hfg]
  exact h0

theorem anrem_germ_isolated {n : ℕ} {A : Set (Fin n → ℂ)} {p : Fin n → ℂ} (hp : p ∈ A)
    (h : adim2_dimension n (adim2_germ n A p) ≤ 0) : ∀ᶠ z in 𝓝 p, z ∈ A → z = p := by
  set I := adim2_ideal n (adim2_germ n A p)
  have hI : I ≠ ⊤ := by
    intro hI
    have := anrem_ideal_value_eq_zero hp (hI ▸ Submodule.mem_top : (1 : AnalyticGerm n) ∈ I)
    simp at this
  have : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro a b hab
    rw [analyticGerm_isUnit_iff] at hab
    simp only [map_add] at hab
    by_cases ha : analyticGermValue n a = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [ha] using hab
    · left
      rwa [analyticGerm_isUnit_iff]
  have : Nontrivial (AnalyticGerm n ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (AnalyticGerm n ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : Ring.KrullDimLE 0 (AnalyticGerm n ⧸ I) :=
    Ring.krullDimLE_iff.2 (by rw [Nat.cast_zero]; exact h)
  have hcoord : ∀ i : Fin n, ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → z i = 0 := by
    intro i
    let c : AnalyticGerm n := ⟨↑(fun z : Fin n → ℂ ↦ z i), fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt _, rfl⟩
    have hmem : Ideal.Quotient.mk I c ∈ IsLocalRing.maximalIdeal (AnalyticGerm n ⧸ I) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (AnalyticGerm n ⧸ I)ˣ).1
      have h1 : Ideal.Quotient.mk I (c * v - 1) = 0 := by
        rw [map_sub, map_mul, hv, ← hu, map_one, Units.mul_inv, sub_self]
      have h2 := anrem_ideal_value_eq_zero hp (Ideal.Quotient.eq_zero_iff_mem.1 h1)
      have hc0 : analyticGermValue n c = 0 := rfl
      simp [hc0] at h2
    obtain ⟨k, hk⟩ := (Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal).2 hmem
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    change adim2_germ n A p ≤ (c ^ k).1.map (· = 0) at hk
    have hck : (c ^ k).1 = ↑(fun z : Fin n → ℂ ↦ z i ^ k) := by
      rw [SubmonoidClass.coe_pow, ← Germ.coe_pow]; rfl
    rw [hck, adim2_germ, Germ.map_coe, Germ.coe_le] at hk
    filter_upwards [hk] with z hz hzA
    exact eq_zero_of_pow_eq_zero (hz hzA)
  have hall : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), p + z ∈ A → z = 0 := by
    filter_upwards [eventually_all.2 hcoord] with z hz hzA
    funext i; exact hz i hzA
  have ht : Tendsto (fun w : Fin n → ℂ ↦ w - p) (𝓝 p) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 p)).sub_const p
  filter_upwards [ht.eventually hall] with w hw hwA
  have := hw (by simpa using hwA)
  exact sub_eq_zero.1 this

/-! ### Charts -/

section Charts

variable {X : Type u} [TopologicalSpace X]

theorem anrem_chart_continuousOn (c : an_Chart X) : ContinuousOn c.toFun c.dom :=
  continuousOn_iff_continuous_domRestrict.2 c.isEmbedding.continuous

theorem anrem_chart_injOn (c : an_Chart X) : InjOn c.toFun c.dom := fun x hx y hy h ↦ by
  have := c.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h
  exact congrArg Subtype.val this

/-- The preimage of an open set of `ℂⁿ` under a chart, inside its domain, is open. -/
theorem anrem_chart_isOpen_preimage (c : an_Chart X) {O : Set (Fin c.n → ℂ)} (hO : IsOpen O) :
    IsOpen (c.dom ∩ c.toFun ⁻¹' O) :=
  (anrem_chart_continuousOn c).isOpen_inter_preimage c.isOpen_dom hO

/-- A function read through a chart by an ambient function holomorphic at the image points is
holomorphic. -/
theorem anrem_isHolFun_comp_chart (S : an_ReducedSpace X) (j : S.atlas.ι) {W : Set X}
    (hW : W ⊆ (S.atlas.chart j).dom) (Φ : (Fin (S.atlas.chart j).n → ℂ) → ℂ)
    (hΦ : ∀ w ∈ W, AnalyticAt ℂ Φ ((S.atlas.chart j).toFun w)) :
    S.IsHolFun (fun w : W ↦ Φ ((S.atlas.chart j).toFun w)) := by
  intro w i hwi
  obtain ⟨O, hO, hwO, G, hG, hGeq⟩ := S.isAnalytic i j w ⟨hW w.2, hwi⟩
  have hGw : G ((S.atlas.chart i).toFun w) = (S.atlas.chart j).toFun w :=
    (hGeq w ⟨hW w.2, hwi⟩ hwO).symm
  refine ⟨(S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹' O ∩ (S.atlas.chart j).dom,
    (anrem_chart_isOpen_preimage _ hO).inter (S.atlas.chart j).isOpen_dom, ⟨⟨hwi, hwO⟩, hW w.2⟩,
    Φ ∘ G, (hΦ w w.2).comp_of_eq (hG _ hwO) hGw, fun y hy ↦ ?_⟩
  simp only [Function.comp_apply]
  rw [← hGeq y ⟨hy.1.2, hy.2⟩ hy.1.1.2]

/-- Finite sets are closed analytic: near a point, the chart coordinates minus their values. -/
theorem anrem_isClosedAnalytic_finite (S : an_ReducedSpace X) {F : Set X} (hF : F.Finite) :
    an_IsClosedAnalytic S F := by
  have := S.t2Space
  refine ⟨hF.isClosed, fun y hy ↦ ?_⟩
  set j := S.atlas.chartAt y
  set c := S.atlas.chart j
  have hFy : IsClosed (F \ {y}) := (hF.subset sdiff_subset).isClosed
  refine ⟨c.dom ∩ (F \ {y})ᶜ, c.isOpen_dom.inter hFy.isOpen_compl,
    ⟨S.atlas.mem_chartAt y, fun h ↦ h.2 rfl⟩, c.n,
    fun i w ↦ c.toFun w i - c.toFun y i, fun i ↦ ?_, fun w ↦ ?_⟩
  · exact anrem_isHolFun_comp_chart S j inter_subset_left (fun z ↦ z i - c.toFun y i)
      (fun w _ ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.n ↦ ℂ) i).analyticAt
        _).sub analyticAt_const)
  · simp only [sub_eq_zero]
    constructor
    · intro hw i
      have : (w : X) = y := by
        by_contra hne; exact w.2.2 ⟨hw, hne⟩
      rw [this]
    · intro h
      have : (w : X) = y := anrem_chart_injOn c w.2.1 (S.atlas.mem_chartAt y) (funext h)
      rw [this]; exact hy

/-! ### The zero-dimensional case -/

theorem anrem_isolated_of_dimAt_le_zero (S : an_ReducedSpace X) {Z : Set X} {x : X} (hx : x ∈ Z)
    (h : an_dimAt S Z x ≤ 0) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Z ∩ W ⊆ {x} := by
  set c := S.atlas.chart (S.atlas.chartAt x)
  have hxc : x ∈ c.dom := S.atlas.mem_chartAt x
  obtain ⟨O, hOA, hO, hxO⟩ := eventually_nhds_iff.1
    (anrem_germ_isolated (A := c.toFun '' (Z ∩ c.dom)) ⟨x, ⟨hx, hxc⟩, rfl⟩ h)
  refine ⟨c.dom ∩ c.toFun ⁻¹' O, anrem_chart_isOpen_preimage c hO, ⟨hxc, hxO⟩, ?_⟩
  rintro y ⟨hyZ, hyc, hyO⟩
  exact anrem_chart_injOn c hyc hxc (hOA _ hyO ⟨y, ⟨hyZ, hyc⟩, rfl⟩)

/-- A compact set all of whose points are isolated in `Z` meets `Z` in a finite set. -/
theorem anrem_finite_of_isolated {L Z : Set X} (hL : IsCompact L) (hLZ : L ⊆ Z)
    (hiso : ∀ x ∈ L, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ Z ∩ W ⊆ {x}) : L.Finite := by
  classical
  choose! W hWo hxW hWZ using hiso
  obtain ⟨t, htL, ht⟩ := hL.elim_nhds_subcover W fun x hx ↦ (hWo x hx).mem_nhds (hxW x hx)
  refine t.finite_toSet.subset fun y hy ↦ ?_
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hy)
  have : y = x := hWZ x (htL x hxt) ⟨hLZ hy, hyx⟩
  rw [this]; exact hxt

variable {Y : Type v} [TopologicalSpace Y]

/-- The zero-dimensional case of the local proper mapping theorem, with local compactness of the
target as a hypothesis. -/
theorem anrem_remmert_local_zero [LocallyCompactSpace Y] (S : an_ReducedSpace X)
    (T : an_ReducedSpace Y) (f : X → Y) (hf : an_IsProperHom S T f) {Z : Set X}
    (hZ : an_IsClosedAnalytic S Z) {V : Set Y} (hV : IsOpen V)
    (hdim : ∀ x ∈ Z ∩ f ⁻¹' V, an_dimAt S Z x ≤ 0) :
    ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z) y := by
  intro y hy
  obtain ⟨K, hKy, hKV, hK⟩ := local_compact_nhds (hV.mem_nhds hy)
  have hL : IsCompact (Z ∩ f ⁻¹' K) := (hf.1.isCompact_preimage hK).inter_left hZ.1
  have hLfin : (Z ∩ f ⁻¹' K).Finite := anrem_finite_of_isolated hL inter_subset_left
    fun x hx ↦ anrem_isolated_of_dimAt_le_zero S hx.1 (hdim x ⟨hx.1, hKV hx.2⟩)
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.2 hKy, f '' (Z ∩ f ⁻¹' K),
    anrem_isClosedAnalytic_finite T (hLfin.image f), ?_⟩
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨x, ⟨hx, (interior_subset hz : f x ∈ K)⟩, rfl⟩, hz⟩
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨x, hx.1, rfl⟩, hz⟩

end Charts

/-! ### Open subsets of manifolds -/

/-- The restriction of a proper map to the preimage of an open subset of a locally compact
Hausdorff space is proper. -/
theorem anrem_isProperMap_restrictPreimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] {f : X → Y} (hf : IsProperMap f) (U : Opens Y) :
    IsProperMap ((U : Set Y).restrictPreimage f) := by
  have : LocallyCompactSpace U := U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  refine isProperMap_iff_isCompact_preimage.2 ⟨hf.continuous.restrictPreimage, fun K hK ↦ ?_⟩
  rw [Subtype.isCompact_iff]
  have himg : Subtype.val '' ((U : Set Y).restrictPreimage f ⁻¹' K) =
      f ⁻¹' (Subtype.val '' K) := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, hx, rfl⟩
    · rintro ⟨⟨y, hyU⟩, hy, hxy⟩
      change y = f x at hxy
      subst hxy
      exact ⟨⟨x, hyU⟩, hy, rfl⟩
  rw [himg]
  exact hf.isCompact_preimage (hK.image continuous_subtype_val)

section Opens

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- Closed analytic subsets restrict to open subsets. -/
theorem anrem_isClosedAnalytic_restrict_opens {Z : Set M} (hZ : IsClosedAnalytic H Z)
    (U : Opens M) : IsClosedAnalytic H (Subtype.val ⁻¹' Z : Set U) := by
  refine ⟨hZ.1.preimage continuous_subtype_val, fun x hx ↦ ?_⟩
  obtain ⟨O, hO, hxO, hOt, k, g, hg, hgZ⟩ := hZ.2 x.1 hx
  have hxs : x ∈ (chartAt H x).source := mem_chart_source H x
  have hval : chartAt H x x = chartAt H x.1 x.1 := rfl
  refine ⟨O ∩ (chartAt H x).target, hO.inter (chartAt H x).open_target,
    ⟨hval ▸ hxO, (chartAt H x).map_source hxs⟩, inter_subset_right, k, g,
    fun i ↦ (hg i).mono inter_subset_left, fun z hz ↦ ?_⟩
  have hsymm : ((chartAt H x).symm z : M) = (chartAt H x.1).symm z :=
    (chartAt H x.1).subtypeRestr_symm_apply ⟨x⟩ hz.2
  change ((chartAt H x).symm z : M) ∈ Z ↔ _
  rw [hsymm]
  exact hgZ z hz.1

/-- A closed analytic subset of an open set containing a chart domain gives the local equations at
the centre of the chart. -/
theorem anrem_isClosedAnalytic_of_opens {W : Set M} (U : Opens M) {y : M}
    (hyU : y ∈ U) (hW : IsClosedAnalytic H (Subtype.val ⁻¹' W : Set U)) (hy : y ∈ W) :
    ∃ O : Set H, IsOpen O ∧ chartAt H y y ∈ O ∧
      O ⊆ (chartAt H y).target ∧ ∃ (n : ℕ) (f : Fin n → H → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) O) ∧
        ∀ z ∈ O, ((chartAt H y).symm z ∈ W ↔ ∀ i, f i z = 0) := by
  obtain ⟨O, hO, hyO, hOt, k, g, hg, hgW⟩ := hW.2 ⟨y, hyU⟩ hy
  have ht : (chartAt H (⟨y, hyU⟩ : U)).target ⊆ (chartAt H y).target :=
    (chartAt H y).subtypeRestr_target_subset ⟨⟨y, hyU⟩⟩
  refine ⟨O, hO, hyO, hOt.trans ht, k, g, hg, fun z hz ↦ ?_⟩
  have hsymm : ((chartAt H (⟨y, hyU⟩ : U)).symm z : M) = (chartAt H y).symm z :=
    (chartAt H y).subtypeRestr_symm_apply ⟨⟨y, hyU⟩⟩ (hOt hz)
  rw [← hsymm]
  exact hgW z hz

end Opens

/-! ### The hyperbola -/

theorem anrem_hyperbola_isClosedAnalytic :
    an_IsClosedAnalytic (an_euclidSpace 2) an_hyperbola := by
  have hc : Continuous an_hyperbolaEqn := by
    unfold an_hyperbolaEqn; fun_prop
  have hset : an_hyperbola = an_hyperbolaEqn ⁻¹' {0} := by
    ext z; simp [an_zeroLocus]
  have han : ∀ p : Fin 2 → ℂ, AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ w 0 * w 1 - 1) p := by
    intro p
    have h0 : AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z 0) p :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt _
    have h1 : AnalyticAt ℂ (fun z : Fin 2 → ℂ ↦ z 1) p :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt _
    exact (h0.mul h1).sub analyticAt_const
  refine ⟨hset ▸ isClosed_singleton.preimage hc, fun x _ ↦ ⟨univ, isOpen_univ, mem_univ _, 1,
    fun _ w ↦ (w : Fin 2 → ℂ) 0 * (w : Fin 2 → ℂ) 1 - 1, fun _ z _ _ ↦ ⟨univ, isOpen_univ,
    mem_univ _, (fun w : Fin 2 → ℂ ↦ w 0 * w 1 - 1 : (Fin 2 → ℂ) → ℂ), ?_, fun _ _ ↦ rfl⟩, fun y ↦ ?_⟩⟩
  · exact han _
  · simp only [an_zeroLocus, mem_univ, true_and, mem_ofPred_eq]
    constructor
    · intro h j; exact congrFun h 0
    · intro h; funext i; fin_cases i; exact h 0

theorem anrem_proj0_not_proper : ¬ IsProperMap an_proj0 := by
  intro h
  have hK := h.isCompact_preimage (isCompact_singleton (x := (0 : Fin 1 → ℂ)))
  have hcont : Continuous (fun z : Fin 2 → ℂ ↦ z 1) := continuous_apply 1
  have hu : (univ : Set ℂ) ⊆ (fun z : Fin 2 → ℂ ↦ z 1) '' (an_proj0 ⁻¹' {0}) := fun t _ ↦
    ⟨![0, t], by funext i; simp [an_proj0], by simp⟩
  exact noncompact_univ ℂ ((hK.image hcont).of_isClosed_subset isClosed_univ hu)

theorem anrem_proj0_image_hyperbola :
    an_proj0 '' an_hyperbola = {w | w 0 ≠ 0} := by
  ext w
  simp only [mem_image, an_zeroLocus, mem_univ, true_and, mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩ h
    have := congrFun hz 0
    simp only [an_hyperbolaEqn, Pi.zero_apply] at this
    simp only [an_proj0] at h
    simp [h] at this
  · intro h
    refine ⟨![w 0, (w 0)⁻¹], ?_, ?_⟩
    · funext i; simp [an_hyperbolaEqn, h]
    · funext i; fin_cases i; simp [an_proj0]

theorem anrem_not_closed_image : ¬ IsClosed (an_proj0 '' an_hyperbola) := by
  rw [anrem_proj0_image_hyperbola]
  intro h
  have hmem : (0 : Fin 1 → ℂ) ∈ closure {w : Fin 1 → ℂ | w 0 ≠ 0} := by
    have ht : Tendsto (fun t : ℂ ↦ (fun _ : Fin 1 ↦ t)) (𝓝[≠] 0) (𝓝 0) :=
      ((continuous_pi fun _ ↦ continuous_id).tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun t ht ↦ ht)
  rw [h.closure_eq] at hmem
  exact hmem rfl

/-! ### Local equations, operations and open subspaces -/

/-- Local equations of a subset of `ℂⁿ` at a point: on an open neighbourhood, the common zeros of
finitely many functions analytic there. -/
def anrem_LocEq {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin n → ℂ), IsOpen U ∧ y ∈ U ∧ ∃ (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
    (∀ j, AnalyticOnNhd ℂ (f j) U) ∧ ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)

section Local

variable {X : Type u} [TopologicalSpace X]

/-- A subset of a reduced space is cut out near `x` by finitely many holomorphic functions. -/
def anrem_AnNear (S : an_ReducedSpace X) (W : Set X) (x : X) : Prop :=
  ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ (k : ℕ) (g : Fin k → N → ℂ), (∀ j, S.IsHolFun (g j)) ∧
    ∀ y : N, ((y : X) ∈ W ↔ ∀ j, g j y = 0)

theorem anrem_isClosedAnalytic_iff (S : an_ReducedSpace X) (W : Set X) :
    an_IsClosedAnalytic S W ↔ IsClosed W ∧ ∀ x ∈ W, anrem_AnNear S W x := Iff.rfl

/-- Open subsets of a chart domain are cut out by open subsets of `ℂⁿ`. -/
theorem anrem_chart_nhd (c : an_Chart X) {N : Set X} (hN : IsOpen N) :
    ∃ O : Set (Fin c.n → ℂ), IsOpen O ∧ c.dom ∩ c.toFun ⁻¹' O = c.dom ∩ N := by
  have hopen : IsOpen ((Subtype.val : c.dom → X) ⁻¹' N) := hN.preimage continuous_subtype_val
  obtain ⟨O, hO, hOeq⟩ := c.isEmbedding.isInducing.isOpen_iff.1 hopen
  refine ⟨O, hO, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwO⟩
    refine ⟨hw, ?_⟩
    have : (⟨w, hw⟩ : c.dom) ∈ c.dom.domRestrict c.toFun ⁻¹' O := hwO
    rw [hOeq] at this
    exact this
  · rintro ⟨hw, hwN⟩
    refine ⟨hw, ?_⟩
    have : (⟨w, hw⟩ : c.dom) ∈ (Subtype.val : c.dom → X) ⁻¹' N := hwN
    rw [← hOeq] at this
    exact this

/-- Local analyticity in a chart: the image in the chart has local equations at the image point. -/
theorem anrem_anNear_chart (S : an_ReducedSpace X) {W : Set X} {x : X} (hW : anrem_AnNear S W x)
    (i : S.atlas.ι) (hxi : x ∈ (S.atlas.chart i).dom) :
    anrem_LocEq ((S.atlas.chart i).toFun '' (W ∩ (S.atlas.chart i).dom))
      ((S.atlas.chart i).toFun x) := by
  set c := S.atlas.chart i
  obtain ⟨N, hN, hxN, k, g, hg, hgW⟩ := hW
  choose N' hN' hxN' G hG hGeq using fun j ↦ hg j ⟨x, hxN⟩ i hxi
  set N₀ := N ∩ ⋂ j, N' j
  have hN₀ : IsOpen N₀ := hN.inter (isOpen_iInter_of_finite hN')
  obtain ⟨O₁, hO₁, hO₁eq⟩ := anrem_chart_nhd c hN₀
  have hxO₁ : c.toFun x ∈ O₁ := by
    have : x ∈ c.dom ∩ N₀ := ⟨hxi, hxN, mem_iInter.2 hxN'⟩
    rw [← hO₁eq] at this
    exact this.2
  obtain ⟨O₂, hO₂sub, hO₂, hxO₂⟩ := eventually_nhds_iff.1
    (eventually_all.2 fun j ↦ (hG j).eventually_analyticAt)
  have hxU : c.toFun x ∈ c.U := by
    have : c.toFun x ∈ c.toFun '' c.dom := mem_image_of_mem _ hxi
    rw [c.image_eq] at this
    exact this.1
  refine ⟨O₁ ∩ O₂ ∩ c.U, (hO₁.inter hO₂).inter c.isOpen_U, ⟨⟨hxO₁, hxO₂⟩, hxU⟩, c.k + k,
    Fin.append (fun l z ↦ c.eqns z l) G, fun l ↦ ?_, fun z hz ↦ ?_⟩
  · refine Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
    · intro z hz
      rw [Fin.append_left]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.k ↦ ℂ) l).analyticAt _).comp
        (c.analyticOnNhd_eqns z hz.2)
    · intro z hz
      rw [Fin.append_right]
      exact hO₂sub z hz.1.2 j
  · have hmodel : z ∈ c.toFun '' c.dom ↔ c.eqns z = 0 := by
      rw [c.image_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hz.2, h⟩⟩
    constructor
    · rintro ⟨w, ⟨hwW, hwc⟩, rfl⟩ l
      refine Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
      · rw [Fin.append_left]
        rw [hmodel.1 (mem_image_of_mem _ hwc)]
        rfl
      · rw [Fin.append_right]
        have hw : w ∈ c.dom ∩ N₀ := by rw [← hO₁eq]; exact ⟨hwc, hz.1.1⟩
        rw [← hGeq j ⟨w, hw.2.1⟩ ⟨mem_iInter.1 hw.2.2 j, hwc⟩]
        exact (hgW ⟨w, hw.2.1⟩).1 hwW j
    · intro h
      have he : c.eqns z = 0 := funext fun l ↦ by simpa using h (Fin.castAdd k l)
      obtain ⟨w, hwc, rfl⟩ := hmodel.2 he
      have hw : w ∈ c.dom ∩ N₀ := by rw [← hO₁eq]; exact ⟨hwc, hz.1.1⟩
      refine ⟨w, ⟨(hgW ⟨w, hw.2.1⟩).2 fun j ↦ ?_, hwc⟩, rfl⟩
      rw [hGeq j ⟨w, hw.2.1⟩ ⟨mem_iInter.1 hw.2.2 j, hwc⟩]
      simpa using h (Fin.natAdd c.k j)

/-- Conversely, local equations of the image in one chart give local analyticity. -/
theorem anrem_anNear_of_chart (S : an_ReducedSpace X) {W : Set X} {x : X} (i : S.atlas.ι)
    (hxi : x ∈ (S.atlas.chart i).dom)
    (h : anrem_LocEq ((S.atlas.chart i).toFun '' (W ∩ (S.atlas.chart i).dom))
      ((S.atlas.chart i).toFun x)) :
    anrem_AnNear S W x := by
  set c := S.atlas.chart i
  obtain ⟨U, hU, hxU, m, F, hF, hFW⟩ := h
  refine ⟨c.dom ∩ c.toFun ⁻¹' U, anrem_chart_isOpen_preimage c hU, ⟨hxi, hxU⟩, m,
    fun j w ↦ F j (c.toFun w), fun j ↦ anrem_isHolFun_comp_chart S i inter_subset_left (F j)
      fun w hw ↦ hF j _ hw.2, fun w ↦ ?_⟩
  rw [← hFW _ w.2.2]
  constructor
  · intro hw; exact ⟨w, ⟨hw, w.2.1⟩, rfl⟩
  · rintro ⟨w', ⟨hw'W, hw'c⟩, heq⟩
    rwa [anrem_chart_injOn c hw'c w.2.1 heq] at hw'W


/-- Restriction of a holomorphic function to a smaller subset. -/
theorem anrem_isHolFun_restrict (S : an_ReducedSpace X) {U V : Set X} (hVU : V ⊆ U)
    {g : U → ℂ} (hg : S.IsHolFun g) : S.IsHolFun (fun y : V ↦ g ⟨y, hVU y.2⟩) := by
  intro y i hy
  obtain ⟨N, hN, hyN, G, hG, h⟩ := hg ⟨y, hVU y.2⟩ i hy
  exact ⟨N, hN, hyN, G, hG, fun z hz ↦ h ⟨z, hVU z.2⟩ hz⟩

theorem anrem_isHolFun_mul (S : an_ReducedSpace X) {U : Set X} {g h : U → ℂ}
    (hg : S.IsHolFun g) (hh : S.IsHolFun h) : S.IsHolFun (g * h) :=
  (S.atlas.holSubring U).mul_mem hg hh

theorem anrem_anNear_of_not_mem (S : an_ReducedSpace X) {W : Set X} (hW : IsClosed W) {x : X}
    (hx : x ∉ W) : anrem_AnNear S W x :=
  ⟨Wᶜ, hW.isOpen_compl, hx, 1, fun _ _ ↦ 1, fun _ ↦ (S.atlas.holSubring _).one_mem,
    fun y ↦ by
      simp only [one_ne_zero, forall_const, iff_false]
      exact y.2⟩

theorem anrem_anNear_mono_nhd (S : an_ReducedSpace X) {A B : Set X} {x : X} {O : Set X}
    (hO : IsOpen O) (hxO : x ∈ O) (hAB : A ∩ O = B ∩ O) (hA : anrem_AnNear S A x) :
    anrem_AnNear S B x := by
  obtain ⟨N, hN, hxN, k, g, hg, hgA⟩ := hA
  refine ⟨N ∩ O, hN.inter hO, ⟨hxN, hxO⟩, k, fun j y ↦ g j ⟨y, y.2.1⟩,
    fun j ↦ anrem_isHolFun_restrict S inter_subset_left (hg j), fun y ↦ ?_⟩
  rw [← hgA ⟨y, y.2.1⟩]
  have h1 : (y : X) ∈ A ∩ O ↔ (y : X) ∈ B ∩ O := by rw [hAB]
  simpa [y.2.2] using h1.symm

theorem anrem_anNear_union (S : an_ReducedSpace X) {A B : Set X} {x : X}
    (hA : anrem_AnNear S A x) (hB : anrem_AnNear S B x) : anrem_AnNear S (A ∪ B) x := by
  obtain ⟨N, hN, hxN, k, g, hg, hgA⟩ := hA
  obtain ⟨N', hN', hxN', l, h, hh, hhB⟩ := hB
  refine ⟨N ∩ N', hN.inter hN', ⟨hxN, hxN'⟩, k * l,
    fun j y ↦ g (finProdFinEquiv.symm j).1 ⟨y, y.2.1⟩ * h (finProdFinEquiv.symm j).2 ⟨y, y.2.2⟩,
    fun j ↦ anrem_isHolFun_mul S (anrem_isHolFun_restrict S inter_subset_left (hg _))
      (anrem_isHolFun_restrict S inter_subset_right (hh _)), fun y ↦ ?_⟩
  rw [mem_union, hgA ⟨y, y.2.1⟩, hhB ⟨y, y.2.2⟩]
  constructor
  · rintro (h1 | h1) j
    · simp [h1]
    · simp [h1]
  · intro h1
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
    have := h1 (finProdFinEquiv (a, b))
    simp only [Equiv.symm_apply_apply, mul_eq_zero] at this
    rcases this with h2 | h2
    · exact ha h2
    · exact hb h2

theorem anrem_anNear_inter (S : an_ReducedSpace X) {A B : Set X} {x : X}
    (hA : anrem_AnNear S A x) (hB : anrem_AnNear S B x) : anrem_AnNear S (A ∩ B) x := by
  obtain ⟨N, hN, hxN, k, g, hg, hgA⟩ := hA
  obtain ⟨N', hN', hxN', l, h, hh, hhB⟩ := hB
  refine ⟨N ∩ N', hN.inter hN', ⟨hxN, hxN'⟩, k + l,
    Fin.append (fun j y ↦ g j ⟨y, y.2.1⟩) (fun j y ↦ h j ⟨y, y.2.2⟩), fun j ↦ ?_, fun y ↦ ?_⟩
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · rw [Fin.append_left]; exact anrem_isHolFun_restrict S inter_subset_left (hg j)
    · rw [Fin.append_right]; exact anrem_isHolFun_restrict S inter_subset_right (hh j)
  · rw [mem_inter_iff, hgA ⟨y, y.2.1⟩, hhB ⟨y, y.2.2⟩]
    constructor
    · rintro ⟨h1, h2⟩ j
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
      · simpa using h1 j
      · simpa using h2 j
    · intro h1
      exact ⟨fun j ↦ by simpa using h1 (Fin.castAdd l j),
        fun j ↦ by simpa using h1 (Fin.natAdd k j)⟩

theorem anrem_isClosedAnalytic_union (S : an_ReducedSpace X) {A B : Set X}
    (hA : an_IsClosedAnalytic S A) (hB : an_IsClosedAnalytic S B) :
    an_IsClosedAnalytic S (A ∪ B) := by
  refine ⟨hA.1.union hB.1, fun x hx ↦ ?_⟩
  have hA' : anrem_AnNear S A x := by
    by_cases h : x ∈ A
    · exact hA.2 x h
    · exact anrem_anNear_of_not_mem S hA.1 h
  have hB' : anrem_AnNear S B x := by
    by_cases h : x ∈ B
    · exact hB.2 x h
    · exact anrem_anNear_of_not_mem S hB.1 h
  exact anrem_anNear_union S hA' hB'

theorem anrem_isClosedAnalytic_inter (S : an_ReducedSpace X) {A B : Set X}
    (hA : an_IsClosedAnalytic S A) (hB : an_IsClosedAnalytic S B) :
    an_IsClosedAnalytic S (A ∩ B) :=
  ⟨hA.1.inter hB.1, fun x hx ↦ anrem_anNear_inter S (hA.2 x hx.1) (hB.2 x hx.2)⟩

theorem anrem_isClosedAnalytic_biUnion (S : an_ReducedSpace X) {ι : Type*} (s : Finset ι)
    {A : ι → Set X} (hA : ∀ i ∈ s, an_IsClosedAnalytic S (A i)) :
    an_IsClosedAnalytic S (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using an_isClosedAnalytic_empty S
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact anrem_isClosedAnalytic_union S (hA a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hA i (Finset.mem_insert_of_mem hi))

variable {Y : Type v} [TopologicalSpace Y]

/-- Pull-back of local equations along a holomorphic map. -/
theorem anrem_anNear_preimage (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {W : Set Y} {x : X} (hW : anrem_AnNear T W (f x)) :
    anrem_AnNear S (f ⁻¹' W) x := by
  obtain ⟨N, hN, hxN, k, g, hg, hgW⟩ := hW
  exact ⟨f ⁻¹' N, hN.preimage hf.1, hxN, k, fun j y ↦ g j ⟨f y, y.2⟩,
    fun j ↦ hf.2 N hN (g j) (hg j), fun y ↦ hgW ⟨f y, y.2⟩⟩

theorem anrem_isClosedAnalytic_preimage (S : an_ReducedSpace X) (T : an_ReducedSpace Y)
    {f : X → Y} (hf : an_IsHom S T f) {W : Set Y} (hW : an_IsClosedAnalytic T W) :
    an_IsClosedAnalytic S (f ⁻¹' W) :=
  ⟨hW.1.preimage hf.1, fun _ hx ↦ anrem_anNear_preimage S T hf (hW.2 _ hx)⟩

/-- The fibre of a holomorphic map through a closed analytic subset is closed analytic. -/
theorem anrem_isClosedAnalytic_fibre (S : an_ReducedSpace X) (T : an_ReducedSpace Y)
    {f : X → Y} (hf : an_IsHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (y : Y) :
    an_IsClosedAnalytic S (Z ∩ f ⁻¹' {y}) :=
  anrem_isClosedAnalytic_inter S hZ
    (anrem_isClosedAnalytic_preimage S T hf (anrem_isClosedAnalytic_finite T (finite_singleton y)))


/-! ### Open subspaces -/

/-- The open set of `ℂⁿ` cutting out the part of a chart domain inside an open set. -/
def anrem_chartCut (c : an_Chart X) {O : Set X} (hO : IsOpen O) : Set (Fin c.n → ℂ) :=
  (anrem_chart_nhd c hO).choose

theorem anrem_chartCut_spec (c : an_Chart X) {O : Set X} (hO : IsOpen O) :
    IsOpen (anrem_chartCut c hO) ∧ c.dom ∩ c.toFun ⁻¹' (anrem_chartCut c hO) = c.dom ∩ O :=
  (anrem_chart_nhd c hO).choose_spec

/-- The restriction of a chart to an open subset. -/
def anrem_chartRestrict (c : an_Chart X) {O : Set X} (hO : IsOpen O) : an_Chart O where
  dom := Subtype.val ⁻¹' c.dom
  isOpen_dom := c.isOpen_dom.preimage continuous_subtype_val
  n := c.n
  U := c.U ∩ anrem_chartCut c hO
  isOpen_U := c.isOpen_U.inter (anrem_chartCut_spec c hO).1
  k := c.k
  eqns := c.eqns
  analyticOnNhd_eqns := c.analyticOnNhd_eqns.mono inter_subset_left
  toFun := c.toFun ∘ Subtype.val
  isEmbedding := by
    have h1 : Topology.IsEmbedding (fun x : (Subtype.val ⁻¹' c.dom : Set O) ↦
        (⟨x.1.1, x.2⟩ : c.dom)) :=
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
    exact c.isEmbedding.comp h1
  image_eq := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxc : (x : X) ∈ c.dom ∩ O := ⟨hx, x.2⟩
      rw [← (anrem_chartCut_spec c hO).2] at hxc
      have : c.toFun x ∈ c.toFun '' c.dom := mem_image_of_mem _ hx
      rw [c.image_eq] at this
      exact ⟨⟨this.1, hxc.2⟩, this.2⟩
    · rintro ⟨⟨hzU, hzO⟩, hz⟩
      have : z ∈ an_zeroLocus c.U c.eqns := ⟨hzU, hz⟩
      rw [← c.image_eq] at this
      obtain ⟨x, hx, rfl⟩ := this
      have hxc : x ∈ c.dom ∩ c.toFun ⁻¹' anrem_chartCut c hO := ⟨hx, hzO⟩
      rw [(anrem_chartCut_spec c hO).2] at hxc
      exact ⟨⟨x, hxc.2⟩, hx, rfl⟩

/-- The atlas of an open subset. -/
def anrem_openAtlas (A : an_Atlas X) {O : Set X} (hO : IsOpen O) : an_Atlas O where
  ι := A.ι
  chart i := anrem_chartRestrict (A.chart i) hO
  covers x := ⟨A.chartAt x, A.mem_chartAt x⟩

/-- An open subset of a reduced complex analytic space. -/
def anrem_openSpace (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O) : an_ReducedSpace O where
  t2Space := by have := S.t2Space; infer_instance
  secondCountable := by have := S.secondCountable; infer_instance
  atlas := anrem_openAtlas S.atlas hO
  isAnalytic := by
    intro i j x hx
    obtain ⟨W, hW, hxW, G, hG, h⟩ := S.isAnalytic i j x ⟨hx.1, hx.2⟩
    exact ⟨W, hW, hxW, G, hG, fun y hy hyW ↦ h y ⟨hy.1, hy.2⟩ hyW⟩

theorem anrem_openSpace_chart (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O)
    (i : S.atlas.ι) :
    (anrem_openSpace S hO).atlas.chart i = anrem_chartRestrict (S.atlas.chart i) hO := rfl

/-- Local equations transfer to and from an open subspace. -/
theorem anrem_anNear_openSpace_iff (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O)
    (W : Set O) (x : O) :
    anrem_AnNear (anrem_openSpace S hO) W x ↔ anrem_AnNear S (Subtype.val '' W) x := by
  set i := S.atlas.chartAt x
  have hxi : (x : X) ∈ (S.atlas.chart i).dom := S.atlas.mem_chartAt x
  have himg : ((anrem_openSpace S hO).atlas.chart i).toFun ''
      (W ∩ ((anrem_openSpace S hO).atlas.chart i).dom) =
      (S.atlas.chart i).toFun '' (Subtype.val '' W ∩ (S.atlas.chart i).dom) := by
    ext z
    constructor
    · rintro ⟨w, ⟨hwW, hwd⟩, rfl⟩
      exact ⟨w, ⟨⟨w, hwW, rfl⟩, hwd⟩, rfl⟩
    · rintro ⟨_, ⟨⟨w, hwW, rfl⟩, hwd⟩, rfl⟩
      exact ⟨w, ⟨hwW, hwd⟩, rfl⟩
  constructor
  · intro h
    have := anrem_anNear_chart (anrem_openSpace S hO) h i hxi
    rw [himg] at this
    exact anrem_anNear_of_chart S i hxi this
  · intro h
    have := anrem_anNear_chart S h i hxi
    rw [← himg] at this
    exact anrem_anNear_of_chart (anrem_openSpace S hO) i hxi this

/-- Holomorphic functions restrict to an open subspace. -/
theorem anrem_isHolFun_openSpace (S : an_ReducedSpace X) {O : Set X} (hO : IsOpen O)
    {U : Set X} {g : U → ℂ} (hg : S.IsHolFun g) :
    (anrem_openSpace S hO).IsHolFun (fun y : (Subtype.val ⁻¹' U : Set O) ↦ g ⟨y.1.1, y.2⟩) := by
  intro y i hy
  obtain ⟨N, hN, hyN, G, hG, h⟩ := hg ⟨y.1.1, y.2⟩ i hy
  exact ⟨Subtype.val ⁻¹' N, hN.preimage continuous_subtype_val, hyN, G, hG,
    fun z hz ↦ h ⟨z.1.1, z.2⟩ hz⟩


/-- A holomorphic map restricts to open subspaces. -/
theorem anrem_isHom_openSpace (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {O : Set X} (hO : IsOpen O) {O' : Set Y} (hO' : IsOpen O')
    (hmaps : MapsTo f O O') :
    an_IsHom (anrem_openSpace S hO) (anrem_openSpace T hO') (hmaps.restrict f O O') := by
  refine ⟨(hf.1.comp continuous_subtype_val).subtype_mk _, fun V hV g hg ↦ ?_⟩
  have hVY : IsOpen (Subtype.val '' V : Set Y) := hO'.isOpenMap_subtype_val V hV
  let g' : (Subtype.val '' V : Set Y) → ℂ := fun y ↦ g ⟨y.2.choose, y.2.choose_spec.1⟩
  have hg' : T.IsHolFun g' := by
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
  have h1 := anrem_isHolFun_openSpace S hO (hf.2 _ hVY g' hg')
  have hsub : (MapsTo.restrict f O O' hmaps) ⁻¹' V ⊆
      (Subtype.val ⁻¹' (f ⁻¹' (Subtype.val '' V)) : Set O) :=
    fun x hx ↦ ⟨_, hx, rfl⟩
  have h2 := anrem_isHolFun_restrict (anrem_openSpace S hO) hsub h1
  convert h2 using 2 with x
  change g _ = g _
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact (Exists.choose_spec (⟨_, x.2, rfl⟩ : ∃ v ∈ V, (v : Y) = f x)).2.symm

end Local

end HodgeLean.Foundations.Analytic
