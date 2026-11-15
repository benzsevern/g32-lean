import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceBase

/-! # Stalks of the structure sheaf in a chart

Helpers prefixed `anb_`. In a chart `c` at `x`, an analytic germ `F` at the origin of `ℂⁿ` gives
the germ at `x` of the section `y ↦ F (c y - c x)`. This is a surjective ring map from the analytic
germs onto the stalk at `x`, with kernel the vanishing ideal of the germ of the model at `c x`, so
the stalk is the reduced local ring `𝒪_{ℂⁿ, c x} / I` and has the same Krull dimension.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Two sections have the same germ at `x` when they agree on an open neighbourhood of `x`. -/
theorem anb_germ_eq_of_eqOn (S : an_ReducedSpace X) {U V W : Opens (TopCat.of X)} {x : X}
    (hxU : x ∈ U) (hxV : x ∈ V) (hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V)
    (s : S.structureSheaf.presheaf.obj (Opposite.op U))
    (t : S.structureSheaf.presheaf.obj (Opposite.op V))
    (h : ∀ y : W, s.1 ⟨y, hWU y.2⟩ = t.1 ⟨y, hWV y.2⟩) :
    S.structureSheaf.presheaf.germ U x hxU s = S.structureSheaf.presheaf.germ V x hxV t :=
  TopCat.Presheaf.germ_ext _ W hxW (homOfLE hWU) (homOfLE hWV) (Subtype.ext (funext h))

section ChartGerm

variable (S : an_ReducedSpace X) (i : S.atlas.ι)

/-- The open set of the chart domain on which `y ↦ F (c y - c x)` is analytic. -/
def anb_domF (x : X) (F : (Fin (S.atlas.chart i).n → ℂ) → ℂ) : Opens (TopCat.of X) :=
  ⟨(S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹'
      {w | AnalyticAt ℂ F (w - (S.atlas.chart i).toFun x)},
    (anb_continuousOn_toFun _).isOpen_inter_preimage (S.atlas.chart i).isOpen_dom
      ((isOpen_analyticAt ℂ F).preimage (continuous_id.sub continuous_const))⟩

/-- The section `y ↦ F (c y - c x)`. -/
def anb_secF (x : X) (F : (Fin (S.atlas.chart i).n → ℂ) → ℂ) :
    S.structureSheaf.presheaf.obj (Opposite.op (anb_domF S i x F)) :=
  ⟨fun y ↦ F ((S.atlas.chart i).toFun y - (S.atlas.chart i).toFun x),
    anb_isHolFun_of_chart S.atlas S.isAnalytic fun y ↦ ⟨i, y.2.1, univ, isOpen_univ, mem_univ _,
      fun w ↦ F (w - (S.atlas.chart i).toFun x),
      (y.2.2 : AnalyticAt ℂ F _).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl,
      fun _ _ ↦ rfl⟩⟩

theorem anb_mem_domF {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    {F : (Fin (S.atlas.chart i).n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) :
    x ∈ anb_domF S i x F :=
  ⟨hx, by simpa using hF⟩

/-- The germ at `x` of `y ↦ F (c y - c x)`. -/
def anb_germF {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    (F : (Fin (S.atlas.chart i).n → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) :
    S.structureSheaf.presheaf.stalk (x : TopCat.of X) :=
  S.structureSheaf.presheaf.germ _ x (anb_mem_domF S i hx hF) (anb_secF S i x F)

/-- Germs eventually equal at the origin give the same germ at `x`. -/
theorem anb_germF_congr {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    {F G : (Fin (S.atlas.chart i).n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (h : F =ᶠ[𝓝 0] G) :
    anb_germF S i hx F hF = anb_germF S i hx G hG := by
  obtain ⟨t, ht, hto, h0t⟩ := eventually_nhds_iff.1 h
  let W : Opens (TopCat.of X) := anb_domF S i x F ⊓ anb_domF S i x G ⊓
    ⟨(S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹'
        ((fun w ↦ w - (S.atlas.chart i).toFun x) ⁻¹' t),
      (anb_continuousOn_toFun _).isOpen_inter_preimage (S.atlas.chart i).isOpen_dom
        (hto.preimage (continuous_id.sub continuous_const))⟩
  refine anb_germ_eq_of_eqOn S _ _ (x := x) (W := W)
    ⟨⟨anb_mem_domF S i hx hF, anb_mem_domF S i hx hG⟩, hx, by simpa using h0t⟩
    (fun y hy ↦ hy.1.1) (fun y hy ↦ hy.1.2) _ _ fun y ↦ ht _ y.2.2.2

/-- Germs of sums: the germ of `F + G` is the sum of the germs. -/
theorem anb_germF_add {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    {F G : (Fin (S.atlas.chart i).n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) :
    anb_germF S i hx (F + G) (hF.add hG) = anb_germF S i hx F hF + anb_germF S i hx G hG := by
  let W := anb_domF S i x F ⊓ anb_domF S i x G
  have hxW : x ∈ W := ⟨anb_mem_domF S i hx hF, anb_mem_domF S i hx hG⟩
  rw [anb_germF, anb_germF, anb_germF,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) x hxW,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_right : W ≤ _)) x hxW, ← map_add]
  exact anb_germ_eq_of_eqOn S _ _ (x := x) (W := W ⊓ anb_domF S i x (F + G))
    ⟨hxW, anb_mem_domF S i hx (hF.add hG)⟩ (fun y hy ↦ hy.2) (fun y hy ↦ hy.1) _ _
    fun y ↦ rfl

/-- Germs of products. -/
theorem anb_germF_mul {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    {F G : (Fin (S.atlas.chart i).n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) :
    anb_germF S i hx (F * G) (hF.mul hG) = anb_germF S i hx F hF * anb_germF S i hx G hG := by
  let W := anb_domF S i x F ⊓ anb_domF S i x G
  have hxW : x ∈ W := ⟨anb_mem_domF S i hx hF, anb_mem_domF S i hx hG⟩
  rw [anb_germF, anb_germF, anb_germF,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) x hxW,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_right : W ≤ _)) x hxW, ← map_mul]
  exact anb_germ_eq_of_eqOn S _ _ (x := x) (W := W ⊓ anb_domF S i x (F * G))
    ⟨hxW, anb_mem_domF S i hx (hF.mul hG)⟩ (fun y hy ↦ hy.2) (fun y hy ↦ hy.1) _ _
    fun y ↦ rfl

/-- The germ of the constant `1` is `1`. -/
theorem anb_germF_one {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    anb_germF S i hx (fun _ ↦ 1) analyticAt_const = 1 := by
  rw [anb_germF, ← map_one (ConcreteCategory.hom (S.structureSheaf.presheaf.germ
    (anb_domF S i x fun _ ↦ 1) x (anb_mem_domF S i hx analyticAt_const)))]
  exact anb_germ_eq_of_eqOn S _ _ (x := x) (anb_mem_domF S i hx analyticAt_const) le_rfl le_rfl
    _ _ fun y ↦ rfl

/-- The germ of the constant `0` is `0`. -/
theorem anb_germF_zero {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    anb_germF S i hx (fun _ ↦ 0) analyticAt_const = 0 := by
  rw [anb_germF, ← map_zero (ConcreteCategory.hom (S.structureSheaf.presheaf.germ
    (anb_domF S i x fun _ ↦ 0) x (anb_mem_domF S i hx analyticAt_const)))]
  exact anb_germ_eq_of_eqOn S _ _ (x := x) (anb_mem_domF S i hx analyticAt_const) le_rfl le_rfl
    _ _ fun y ↦ rfl

/-- The ring map from the analytic germs at the origin of `ℂⁿ` to the stalk at `x`, through the
chart: `F ↦ germ of y ↦ F (c y - c x)`. -/
def anb_germHom {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    AnalyticGerm (S.atlas.chart i).n →+* S.structureSheaf.presheaf.stalk (x : TopCat.of X) where
  toFun f := anb_germF S i hx f.property.choose f.property.choose_spec.1
  map_one' := by
    rw [← anb_germF_one S i hx]
    exact anb_germF_congr S i hx _ _ (Filter.Germ.coe_eq.1
      (1 : AnalyticGerm (S.atlas.chart i).n).property.choose_spec.2)
  map_mul' f g := by
    rw [← anb_germF_mul]
    refine anb_germF_congr S i hx _ _ (Filter.Germ.coe_eq.1 ?_)
    exact (f * g).property.choose_spec.2.trans
      (congrArg₂ (· * ·) f.property.choose_spec.2 g.property.choose_spec.2).symm
  map_zero' := by
    rw [← anb_germF_zero S i hx]
    exact anb_germF_congr S i hx _ _ (Filter.Germ.coe_eq.1
      (0 : AnalyticGerm (S.atlas.chart i).n).property.choose_spec.2)
  map_add' f g := by
    rw [← anb_germF_add]
    refine anb_germF_congr S i hx _ _ (Filter.Germ.coe_eq.1 ?_)
    exact (f + g).property.choose_spec.2.trans
      (congrArg₂ (· + ·) f.property.choose_spec.2 g.property.choose_spec.2).symm

theorem anb_germHom_apply {x : X} (hx : x ∈ (S.atlas.chart i).dom)
    (f : AnalyticGerm (S.atlas.chart i).n) {F : (Fin (S.atlas.chart i).n → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F 0) (hFf : Filter.Germ.ofFun F = f.val) :
    anb_germHom S i hx f = anb_germF S i hx F hF :=
  anb_germF_congr S i hx f.property.choose_spec.1 hF
    (Filter.Germ.coe_eq.1 (f.property.choose_spec.2.trans hFf.symm))

theorem anb_germHom_surjective {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    Function.Surjective (anb_germHom S i hx) := by
  intro t
  set c := S.atlas.chart i
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  obtain ⟨N, hN, hxN, G, hG, hsG⟩ := s.2 ⟨x, hxU⟩ i hx
  have hG' : AnalyticAt ℂ G (c.toFun x) := hG
  have hF0 : AnalyticAt ℂ (fun z ↦ G (c.toFun x + z)) 0 :=
    hG'.comp_of_eq (f := fun z ↦ c.toFun x + z) (analyticAt_const.add analyticAt_id) (by simp)
  refine ⟨⟨Filter.Germ.ofFun (fun z ↦ G (c.toFun x + z)), _, hF0, rfl⟩, ?_⟩
  rw [anb_germHom_apply S i hx _ hF0 rfl, anb_germF]
  let W : Opens (TopCat.of X) := anb_domF S i x (fun z ↦ G (c.toFun x + z)) ⊓ U ⊓ ⟨N, hN⟩
  refine anb_germ_eq_of_eqOn S _ _ (x := x) (W := W) ⟨⟨anb_mem_domF S i hx hF0, hxU⟩, hxN⟩
    (fun y hy ↦ hy.1.1) (fun y hy ↦ hy.1.2) _ _ fun y ↦ ?_
  have := hsG ⟨y, y.2.1.2⟩ ⟨y.2.2, y.2.1.1.1⟩
  change G (c.toFun x + (c.toFun y - c.toFun x)) = s.1 ⟨y, y.2.1.2⟩
  rw [add_sub_cancel, this]

theorem anb_germHom_ker {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    RingHom.ker (anb_germHom S i hx) = adim2_ideal (S.atlas.chart i).n
      (adim2_germ (S.atlas.chart i).n
        ((S.atlas.chart i).toFun '' (univ ∩ (S.atlas.chart i).dom))
          ((S.atlas.chart i).toFun x)) := by
  set c := S.atlas.chart i
  ext f
  obtain ⟨F, hF, hFf⟩ := f.property
  rw [RingHom.mem_ker, anb_germHom_apply S i hx f hF hFf, anb_mem_ideal_germ_iff hFf, anb_germF]
  constructor
  · intro h0
    rw [← map_zero (ConcreteCategory.hom (S.structureSheaf.presheaf.germ
      (anb_domF S i x F) x (anb_mem_domF S i hx hF)))] at h0
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq S.structureSheaf.presheaf x
      (anb_mem_domF S i hx hF) (anb_mem_domF S i hx hF) _ _ h0
    have hval : ∀ y : W, F (c.toFun y - c.toFun x) = 0 := fun y ↦
      congrFun (congrArg Subtype.val hW) y
    obtain ⟨O, hO, hOW⟩ := anb_exists_open_trace c W.isOpen
    have hxO : c.toFun x ∈ O := (hOW x hx).2 hxW
    filter_upwards [anb_eventually_add_mem hO hxO] with z hzO hzA
    obtain ⟨y, ⟨-, hy⟩, hyz⟩ := hzA
    have hyW : y ∈ W := (hOW y hy).1 (hyz ▸ hzO)
    have := hval ⟨y, hyW⟩
    rwa [hyz, add_sub_cancel_left] at this
  · intro h
    obtain ⟨t, ht, hto, h0t⟩ := eventually_nhds_iff.1 h
    rw [← map_zero (ConcreteCategory.hom (S.structureSheaf.presheaf.germ
      (anb_domF S i x F) x (anb_mem_domF S i hx hF)))]
    let W : Opens (TopCat.of X) := anb_domF S i x F ⊓
      ⟨c.dom ∩ c.toFun ⁻¹' ((fun w ↦ w - c.toFun x) ⁻¹' t),
        (anb_continuousOn_toFun _).isOpen_inter_preimage c.isOpen_dom
          (hto.preimage (continuous_id.sub continuous_const))⟩
    refine anb_germ_eq_of_eqOn S _ _ (x := x) (W := W)
      ⟨anb_mem_domF S i hx hF, hx, by simpa using h0t⟩ (fun y hy ↦ hy.1) (fun y hy ↦ hy.1) _ _
      fun y ↦ ?_
    change F (c.toFun y - c.toFun x) = 0
    refine ht _ y.2.2.2 ?_
    rw [add_sub_cancel]
    exact ⟨y, ⟨mem_univ _, y.2.2.1⟩, rfl⟩

/-- The Krull dimension of the stalk at `x` is that of the germ of the model, read in any chart at
`x`. -/
theorem anb_ringKrullDim_stalk {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    ringKrullDim (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) =
      adim2_dimension (S.atlas.chart i).n (adim2_germ (S.atlas.chart i).n
        ((S.atlas.chart i).toFun '' (univ ∩ (S.atlas.chart i).dom))
          ((S.atlas.chart i).toFun x)) := by
  rw [adim2_dimension, ← anb_germHom_ker S i hx]
  exact (ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (anb_germHom_surjective S i hx))).symm

end ChartGerm

end HodgeLean.Foundations.Analytic
