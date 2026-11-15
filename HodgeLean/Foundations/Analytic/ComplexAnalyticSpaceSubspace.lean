import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceBase

/-! # Closed analytic subspaces

Helpers prefixed `anb_`. Near a point of a closed analytic subset `Z`, a chart of the space and
the local equations of `Z`, read in the chart, give a chart of `Z` onto the local model cut out by
the chart's equations and those of `Z`. These charts form an analytic atlas on `Z`, the inclusion
is holomorphic, and a map into `Z` is holomorphic as soon as it is into the space.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations

universe u w

variable {X : Type u} [TopologicalSpace X]

/-- Local data of a closed analytic subset `Z` in a chart `i`: an open `N` in the chart domain,
an open `O` of the ambient `ℂⁿ` tracing `N`, and functions `G` analytic on `O` whose common zeros,
read through the chart, are `Z` on `N`. -/
structure anb_SubData (S : an_ReducedSpace X) (Z : Set X) where
  i : S.atlas.ι
  N : Set X
  isOpen_N : IsOpen N
  N_sub : N ⊆ (S.atlas.chart i).dom
  k : ℕ
  G : Fin k → (Fin (S.atlas.chart i).n → ℂ) → ℂ
  O : Set (Fin (S.atlas.chart i).n → ℂ)
  isOpen_O : IsOpen O
  analytic_G : ∀ j, AnalyticOnNhd ℂ (G j) O
  trace : ∀ y ∈ (S.atlas.chart i).dom, ((S.atlas.chart i).toFun y ∈ O ↔ y ∈ N)
  zeros : ∀ y ∈ N, (y ∈ Z ↔ ∀ j, G j ((S.atlas.chart i).toFun y) = 0)

/-- Every point of a closed analytic subset has local data. -/
theorem anb_exists_subData (S : an_ReducedSpace X) {Z : Set X} (hZ : an_IsClosedAnalytic S Z)
    {x : X} (hx : x ∈ Z) : ∃ D : anb_SubData S Z, x ∈ D.N := by
  obtain ⟨W, hW, hxW, k, g, hg, hgZ⟩ := hZ.2 x hx
  obtain ⟨i, hxi⟩ := S.atlas.covers x
  set c := S.atlas.chart i
  have hk := fun j ↦ hg j ⟨x, hxW⟩ i hxi
  choose Nj hNj hxNj G hG hgG using hk
  let O2 : Set (Fin c.n → ℂ) := ⋂ j, {w | AnalyticAt ℂ (G j) w}
  have hO2 : IsOpen O2 := isOpen_iInter_of_finite fun j ↦ isOpen_analyticAt ℂ (G j)
  let N := W ∩ (⋂ j, Nj j) ∩ (c.dom ∩ c.toFun ⁻¹' O2)
  have hN : IsOpen N := (hW.inter (isOpen_iInter_of_finite hNj)).inter
    ((anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hO2)
  obtain ⟨O1, hO1, hO1N⟩ := anb_exists_open_trace c hN
  refine ⟨⟨i, N, hN, fun y hy ↦ hy.2.1, k, G, O1 ∩ O2, hO1.inter hO2,
    fun j w hw ↦ mem_iInter.1 hw.2 j, fun y hy ↦ ⟨fun h ↦ (hO1N y hy).1 h.1,
      fun h ↦ ⟨(hO1N y hy).2 h, h.2.2⟩⟩, fun y hy ↦ ?_⟩,
    ⟨⟨hxW, mem_iInter.2 hxNj⟩, hxi, mem_iInter.2 hG⟩⟩
  rw [hgZ ⟨y, hy.1.1⟩]
  exact forall_congr' fun j ↦ by rw [hgG j ⟨y, hy.1.1⟩ ⟨mem_iInter.1 hy.1.2 j, hy.2.1⟩]

namespace anb_SubData

variable {S : an_ReducedSpace X} {Z : Set X} (D : anb_SubData S Z)

/-- The equations of the restricted chart: those of the chart followed by those of `Z`. -/
def eqns : (Fin (S.atlas.chart D.i).n → ℂ) → (Fin ((S.atlas.chart D.i).k + D.k) → ℂ) :=
  fun w ↦ Fin.append ((S.atlas.chart D.i).eqns w) (fun j ↦ D.G j w)

theorem analyticOnNhd_eqns : AnalyticOnNhd ℂ D.eqns ((S.atlas.chart D.i).U ∩ D.O) := by
  intro w hw
  refine analyticAt_pi_iff.2 fun l ↦ ?_
  refine Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
  · simp only [eqns, Fin.append_left]
    exact analyticAt_pi_iff.1 ((S.atlas.chart D.i).analyticOnNhd_eqns w hw.1) l
  · simp only [eqns, Fin.append_right]
    exact D.analytic_G j w hw.2

theorem eqns_eq_zero (w : Fin (S.atlas.chart D.i).n → ℂ) :
    D.eqns w = 0 ↔ (S.atlas.chart D.i).eqns w = 0 ∧ ∀ j, D.G j w = 0 := by
  constructor
  · intro h
    refine ⟨funext fun l ↦ ?_, fun j ↦ ?_⟩
    · have := congrFun h (Fin.castAdd D.k l)
      simpa [eqns] using this
    · have := congrFun h (Fin.natAdd _ j)
      simpa [eqns] using this
  · rintro ⟨h1, h2⟩
    funext l
    refine Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
    · simp [eqns, h1]
    · simp [eqns, h2 j]

/-- The chart of `Z` restricted from the chart `D.i`. -/
def toChart : an_Chart Z where
  dom := Subtype.val ⁻¹' D.N
  isOpen_dom := D.isOpen_N.preimage continuous_subtype_val
  n := (S.atlas.chart D.i).n
  U := (S.atlas.chart D.i).U ∩ D.O
  isOpen_U := (S.atlas.chart D.i).isOpen_U.inter D.isOpen_O
  k := (S.atlas.chart D.i).k + D.k
  eqns := D.eqns
  analyticOnNhd_eqns := D.analyticOnNhd_eqns
  toFun := (S.atlas.chart D.i).toFun ∘ Subtype.val
  isEmbedding := (S.atlas.chart D.i).isEmbedding.comp
    ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
      fun y ↦ D.N_sub y.2)
  image_eq := by
    set c := S.atlas.chart D.i
    ext w
    constructor
    · rintro ⟨y, hyN, rfl⟩
      have hyd : (y : X) ∈ c.dom := D.N_sub hyN
      have hmod : c.toFun y ∈ an_zeroLocus c.U c.eqns := c.image_eq ▸ mem_image_of_mem _ hyd
      refine ⟨⟨hmod.1, (D.trace y hyd).2 hyN⟩, (D.eqns_eq_zero _).2 ⟨hmod.2, ?_⟩⟩
      exact (D.zeros y hyN).1 y.2
    · rintro ⟨hwU, hw0⟩
      rw [D.eqns_eq_zero] at hw0
      have : w ∈ c.toFun '' c.dom := c.image_eq ▸ ⟨hwU.1, hw0.1⟩
      obtain ⟨y, hyd, rfl⟩ := this
      have hyN : y ∈ D.N := (D.trace y hyd).1 hwU.2
      exact ⟨⟨y, (D.zeros y hyN).2 hw0.2⟩, hyN, rfl⟩

end anb_SubData

variable (S : an_ReducedSpace X) {Z : Set X} (hZ : an_IsClosedAnalytic S Z)

/-- The chosen local data at a point of `Z`. -/
def anb_subDataAt (z : Z) : anb_SubData S Z := (anb_exists_subData S hZ z.2).choose

theorem anb_mem_subDataAt (z : Z) : (z : X) ∈ (anb_subDataAt S hZ z).N :=
  (anb_exists_subData S hZ z.2).choose_spec

/-- The atlas of `Z` by restricted charts, one at each point. -/
def anb_subAtlas : an_Atlas Z where
  ι := Z
  chart z := (anb_subDataAt S hZ z).toChart
  covers z := ⟨z, anb_mem_subDataAt S hZ z⟩

theorem anb_subAtlas_isAnalytic : (anb_subAtlas S hZ).IsAnalytic := by
  intro a b y hy
  obtain ⟨W, hW, hyW, H, hH, h⟩ := S.isAnalytic (anb_subDataAt S hZ a).i
    (anb_subDataAt S hZ b).i y.1
    ⟨(anb_subDataAt S hZ b).N_sub hy.1, (anb_subDataAt S hZ a).N_sub hy.2⟩
  exact ⟨W, hW, hyW, H, hH, fun y' hy' hy'W ↦
    h y'.1 ⟨(anb_subDataAt S hZ b).N_sub hy'.1, (anb_subDataAt S hZ a).N_sub hy'.2⟩ hy'W⟩

/-- A closed analytic subset as a reduced complex analytic space. -/
def anb_subSpace : an_ReducedSpace Z where
  t2Space := by have := S.t2Space; infer_instance
  secondCountable := by have := S.secondCountable; infer_instance
  atlas := anb_subAtlas S hZ
  isAnalytic := anb_subAtlas_isAnalytic S hZ

/-- The inclusion of a closed analytic subspace is holomorphic. -/
theorem anb_subSpace_val_isHom : an_IsHom (anb_subSpace S hZ) S Subtype.val := by
  refine ⟨continuous_subtype_val, fun V hV g hg y a hya ↦ ?_⟩
  obtain ⟨N, hN, hyN, G, hG, hgG⟩ := hg ⟨y.1.1, y.2⟩ (anb_subDataAt S hZ a).i
    ((anb_subDataAt S hZ a).N_sub hya)
  exact ⟨Subtype.val ⁻¹' N, hN.preimage continuous_subtype_val, hyN, G, hG,
    fun y' hy' ↦ hgG ⟨y'.1.1, y'.2⟩ ⟨hy'.1, (anb_subDataAt S hZ a).N_sub hy'.2⟩⟩

/-- A map into `Z` that is holomorphic into the space is holomorphic into the subspace. -/
theorem anb_subSpace_lift {W : Type w} [TopologicalSpace W] (C : an_ReducedSpace W)
    (h : W → Z) (hh : an_IsHom C S (Subtype.val ∘ h)) : an_IsHom C (anb_subSpace S hZ) h := by
  have hcont : Continuous h := continuous_induced_rng.2 hh.1
  refine ⟨hcont, fun V hV g hg w j hwj ↦ ?_⟩
  set D := anb_subDataAt S hZ (h w)
  set c := S.atlas.chart D.i
  have hya : h w ∈ ((anb_subAtlas S hZ).chart (h w)).dom := anb_mem_subDataAt S hZ (h w)
  obtain ⟨N', hN', hyN', G, hG, hgG⟩ := hg ⟨h w, w.2⟩ (h w) hya
  let Ω : Set X := c.dom ∩ c.toFun ⁻¹' {u | AnalyticAt ℂ G u}
  have hΩ : IsOpen Ω :=
    (anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom (isOpen_analyticAt ℂ G)
  let φ : Ω → ℂ := fun u ↦ G (c.toFun u)
  have hφ : S.IsHolFun φ := anb_isHolFun_of_chart S.atlas S.isAnalytic fun u ↦
    ⟨D.i, u.2.1, univ, isOpen_univ, mem_univ _, G, u.2.2, fun _ _ ↦ rfl⟩
  have hwΩ : (Subtype.val ∘ h) w ∈ Ω := ⟨D.N_sub hya, hG⟩
  obtain ⟨Nj, hNj, hwNj, G', hG', hG'eq⟩ := hh.2 Ω hΩ φ hφ ⟨w, hwΩ⟩ j hwj
  have hdom : IsOpen ((anb_subAtlas S hZ).chart (h w)).dom :=
    ((anb_subAtlas S hZ).chart (h w)).isOpen_dom
  refine ⟨Nj ∩ (Subtype.val ∘ h) ⁻¹' Ω ∩ h ⁻¹' (N' ∩ ((anb_subAtlas S hZ).chart (h w)).dom),
    (hNj.inter (hΩ.preimage hh.1)).inter ((hN'.inter hdom).preimage hcont),
    ⟨⟨hwNj, hwΩ⟩, hyN', hya⟩, G', hG', fun w' hw' ↦ ?_⟩
  change g ⟨h w', w'.2⟩ = _
  rw [hgG ⟨h w', w'.2⟩ hw'.1.2]
  exact hG'eq ⟨w', hw'.1.1.2⟩ ⟨hw'.1.1.1, hw'.2⟩

end HodgeLean.Foundations.Analytic
