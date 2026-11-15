import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceStalk
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceSubspace
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceGeomDim
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceDefs
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFinite
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertStein
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRank
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibre
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmert
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertDim
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertSlice
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertProper
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertMain
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertExtension

/-! # Proof obligations for the reduced complex analytic space specification -/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations

universe u v w

/-! ### F2: local models -/

theorem an_restrict_ker_aux {n : ℕ} (U Z : Set (Fin n → ℂ)) (h : Z ⊆ U) :
    RingHom.ker (an_restrict U Z h) = an_reducedIdeal U Z := by
  ext g
  rw [RingHom.mem_ker]
  constructor
  · intro hg z hz
    exact congrFun hg ⟨z, hz⟩
  · intro hg
    funext z
    exact hg ⟨z, h z.2⟩ z.2

theorem an_reducedIdeal_isRadical_aux {n : ℕ} (U Z : Set (Fin n → ℂ)) :
    (an_reducedIdeal U Z).IsRadical := by
  rintro g ⟨k, hk⟩ z hz
  have h := hk z hz
  rw [SubmonoidClass.coe_pow, Pi.pow_apply] at h
  exact pow_eq_zero_iff'.1 h |>.1

theorem an_restrict_isLocRestr_aux {n : ℕ} (U Z : Set (Fin n → ℂ)) (hU : IsOpen U)
    (h : Z ⊆ U) (g : an_holRing U) :
    an_IsLocRestr Z (S := univ) (fun x ↦ an_restrict U Z h g x.1) := by
  obtain ⟨G, hG, hgG⟩ := g.2
  intro x
  exact ⟨U, hU, h (x : Z).2, G, hG, fun y _ ↦ hgG ⟨_, h (y : Z).2⟩⟩

/-! ### F2: the structure sheaf -/

theorem an_isHolFun_continuous_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {U : Set X} {g : U → ℂ} (hg : S.IsHolFun g) : Continuous g :=
  anb_isHolFun_continuous S.atlas hg

theorem an_chart_restrict_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (i : S.atlas.ι) {U : Set X} (hU : U ⊆ (S.atlas.chart i).dom) (g : U → ℂ) :
    S.IsHolFun g ↔ ∃ h : (S.atlas.chart i).modelImage U → ℂ,
      an_IsLocRestr (an_zeroLocus (S.atlas.chart i).U (S.atlas.chart i).eqns) h ∧
        ∀ x : U, g x = h ((S.atlas.chart i).toModelImage hU x) := by
  set c := S.atlas.chart i with hc
  constructor
  · intro hg
    let pt : c.modelImage U → U := fun z ↦ ⟨z.2.choose, z.2.choose_spec.1.1⟩
    have hpt_dom : ∀ z, ((pt z : U) : X) ∈ c.dom := fun z ↦ z.2.choose_spec.1.2
    have hpt_val : ∀ z, c.toFun (pt z) = ((z : an_zeroLocus c.U c.eqns) : Fin c.n → ℂ) :=
      fun z ↦ z.2.choose_spec.2
    refine ⟨fun z ↦ g (pt z), fun z ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨N, hN, hxN, G, hG, hgG⟩ := hg (pt z) i (hpt_dom z)
      obtain ⟨O, hO, hON⟩ := anb_exists_open_trace c hN
      refine ⟨O ∩ {w | AnalyticAt ℂ G w}, hO.inter (isOpen_analyticAt ℂ G), ?_, G,
        fun w hw ↦ hw.2, fun y hy ↦ ?_⟩
      · rw [← hpt_val z]
        exact ⟨(hON _ (hpt_dom z)).2 hxN, hG⟩
      · rw [← hpt_val y] at hy ⊢
        exact hgG (pt y) ⟨(hON _ (hpt_dom y)).1 hy.1, hpt_dom y⟩
    · congr 1
      apply Subtype.ext
      symm
      apply anb_injOn_toFun c (hpt_dom _) (hU x.2)
      rw [hpt_val]; rfl
  · rintro ⟨h, hh, hgh⟩
    refine anb_isHolFun_of_chart S.atlas S.isAnalytic fun x ↦ ⟨i, hU x.2, ?_⟩
    obtain ⟨W, hW, hxW, G, hG, hGh⟩ := hh (c.toModelImage hU x)
    refine ⟨c.dom ∩ c.toFun ⁻¹' W,
      (anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hW, ⟨hU x.2, hxW⟩, G,
      hG _ hxW, fun y hy ↦ ?_⟩
    rw [hgh y]
    exact hGh _ hy.1.2

theorem an_structureSheaf_isLocal_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (x : X) :
    IsLocalRing (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) ∧
      ∀ s, s ∈ nonunits (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) ↔
        S.evalStalk x s = 0 := by
  have key : ∀ s, IsUnit s ↔ S.evalStalk x s ≠ 0 := by
    intro s
    constructor
    · intro hs
      exact (hs.map (S.evalStalk x)).ne_zero
    · intro hs
      obtain ⟨U, hxU, f, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ s
      rw [an_ReducedSpace.evalStalk, an_Atlas.evalStalk_germ] at hs
      have hcont : Continuous f.1 := anb_isHolFun_continuous S.atlas f.2
      let V : TopologicalSpace.Opens (TopCat.of X) :=
        ⟨Subtype.val '' (f.1 ⁻¹' {0}ᶜ),
          U.isOpen.isOpenMap_subtype_val _ (isOpen_compl_singleton.preimage hcont)⟩
      have hVU : V ≤ U := by rintro _ ⟨y, -, rfl⟩; exact y.2
      have hxV : x ∈ V := ⟨⟨x, hxU⟩, hs, rfl⟩
      have hne : ∀ y : V, f.1 ⟨y, hVU y.2⟩ ≠ 0 := by
        rintro ⟨_, ⟨y, hy, rfl⟩⟩
        exact hy
      let t : S.structureSheaf.presheaf.obj (Opposite.op V) :=
        ⟨fun y ↦ (f.1 ⟨y, hVU y.2⟩)⁻¹, fun y j hyj ↦ by
          obtain ⟨N, hN, hyN, G, hG, hfG⟩ := f.2 ⟨y, hVU y.2⟩ j hyj
          have hG0 : G ((S.atlas.chart j).toFun y) ≠ 0 := by
            rw [← hfG ⟨y, hVU y.2⟩ ⟨hyN, hyj⟩]; exact hne y
          exact ⟨N, hN, hyN, G⁻¹, hG.inv hG0, fun z hz ↦ by
            simp [hfG ⟨z, hVU z.2⟩ hz]⟩⟩
      have hres : S.structureSheaf.presheaf.map (CategoryTheory.homOfLE hVU).op f * t = 1 := by
        apply Subtype.ext
        funext y
        exact mul_inv_cancel₀ (hne y)
      refine IsUnit.of_mul_eq_one (S.structureSheaf.presheaf.germ V x hxV t) ?_
      rw [← TopCat.Presheaf.germ_res_apply _ (CategoryTheory.homOfLE hVU) x hxV, ← map_mul, hres,
        map_one]
  have hnu : ∀ s, s ∈ nonunits (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) ↔
      S.evalStalk x s = 0 := fun s ↦ by
    rw [mem_nonunits_iff, key, not_not]
  have hnt : Nontrivial (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) := by
    refine nontrivial_of_ne 0 1 fun h ↦ ?_
    have := congrArg (S.evalStalk x) h
    simp at this
  refine ⟨IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_, hnu⟩
  rw [hnu] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

theorem an_isHom_iff_chart_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y) :
    an_IsHom S T f ↔ Continuous f ∧
      ∀ j, S.atlas.IsHolOn ((T.atlas.chart j).toFun ∘ f) (f ⁻¹' (T.atlas.chart j).dom) := by
  constructor
  · rintro ⟨hf, hpull⟩
    refine ⟨hf, fun j i x hx ↦ ?_⟩
    set d := T.atlas.chart j
    set c := S.atlas.chart i
    have hcoord : ∀ k : Fin d.n, T.IsHolFun (fun y : d.dom ↦ d.toFun y k) := fun k ↦
      anb_isHolFun_of_chart T.atlas T.isAnalytic fun y ↦ ⟨j, y.2, univ, isOpen_univ, mem_univ _,
        fun z ↦ z k, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d.n ↦ ℂ) k).analyticAt _,
        fun _ _ ↦ rfl⟩
    have hk := fun k ↦ hpull d.dom d.isOpen_dom _ (hcoord k) ⟨x, hx.1⟩ i hx.2
    choose N hN hxN G hG hNG using hk
    let N' := (⋂ k, N k) ∩ f ⁻¹' d.dom
    have hN' : IsOpen N' := (isOpen_iInter_of_finite hN).inter (d.isOpen_dom.preimage hf)
    obtain ⟨O, hO, hON⟩ := anb_exists_open_trace c hN'
    let G' : (Fin c.n → ℂ) → (Fin d.n → ℂ) := fun z k ↦ G k z
    have hG' : AnalyticAt ℂ G' (c.toFun x) := analyticAt_pi_iff.2 hG
    refine ⟨O ∩ {w | AnalyticAt ℂ G' w}, hO.inter (isOpen_analyticAt ℂ G'),
      ⟨(hON x hx.2).2 ⟨mem_iInter.2 hxN, hx.1⟩, hG'⟩, G', fun w hw ↦ hw.2, fun y hy hyW ↦ ?_⟩
    have hyN := (hON y hy.2).1 hyW.1
    funext k
    exact hNG k ⟨y, hy.1⟩ ⟨mem_iInter.1 hyN.1 k, hy.2⟩
  · rintro ⟨hf, hH⟩
    refine ⟨hf, fun V hV g hg ↦ anb_isHolFun_of_chart S.atlas S.isAnalytic fun x ↦ ?_⟩
    obtain ⟨i, hxi⟩ := S.atlas.covers x
    obtain ⟨j, hfxj⟩ := T.atlas.covers (f x)
    set d := T.atlas.chart j
    set c := S.atlas.chart i
    obtain ⟨Ng, hNg, hfxNg, G, hG, hgG⟩ := hg ⟨f x, x.2⟩ j hfxj
    obtain ⟨W, hW, hxW, Hm, hHm, hHmeq⟩ := hH j i x ⟨hfxj, hxi⟩
    refine ⟨i, hxi, f ⁻¹' (Ng ∩ d.dom) ∩ (c.dom ∩ c.toFun ⁻¹' W),
      ((hNg.inter d.isOpen_dom).preimage hf).inter
        ((anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hW),
      ⟨⟨hfxNg, hfxj⟩, hxi, hxW⟩, G ∘ Hm,
      hG.comp_of_eq (hHm _ hxW) (hHmeq x ⟨hfxj, hxi⟩ hxW).symm, fun y hy ↦ ?_⟩
    rw [hgG ⟨f y, y.2⟩ hy.1.1, Function.comp_apply]
    exact congrArg G (hHmeq y ⟨hy.1.1.2, hy.2⟩ hy.1.2.2)

/-! ### F2: manifolds -/

theorem an_manifold_isHolFun_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (g : M → ℂ)
    {U : Set M} (hU : IsOpen U) :
    (an_manifoldSpace E M).IsHolFun (fun x : U ↦ g x) ↔ ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω g U :=
  anb_manifold_isHolFun_iff g hU

theorem an_manifold_isHom_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {M' : Type*}
    [TopologicalSpace M'] [T2Space M'] [SecondCountableTopology M'] [ChartedSpace E' M']
    [IsManifold 𝓘(ℂ, E') ω M'] (f : M → M') :
    an_IsHom (an_manifoldSpace E M) (an_manifoldSpace E' M') f ↔
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f := by
  constructor
  · rintro ⟨hf, hpull⟩ x
    rw [contMDiffAt_iff_target]
    refine ⟨hf.continuousAt, ?_⟩
    set e' := chartAt E' (f x)
    change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E') ω (e' ∘ f) x
    have hx : x ∈ f ⁻¹' e'.source := mem_chart_source E' (f x)
    have hk : ∀ k, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun y ↦ an_coord E' (e' (f y)) k) x := by
      intro k
      let L : E' →L[ℂ] ℂ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (Module.finrank ℂ E') ↦ ℂ) k).comp
          (an_coord E').toContinuousLinearMap
      have h1 : ContMDiffOn 𝓘(ℂ, E') 𝓘(ℂ, ℂ) ω (fun y ↦ L (e' y)) e'.source :=
        L.contMDiff.comp_contMDiffOn contMDiffOn_chart
      have h2 := hpull e'.source e'.open_source _
        ((anb_manifold_isHolFun_iff (fun y ↦ L (e' y)) e'.open_source).2 h1)
      have h3 := (anb_manifold_isHolFun_iff (fun y ↦ L (e' (f y)))
        (e'.open_source.preimage hf)).1 h2
      exact h3.contMDiffAt ((e'.open_source.preimage hf).mem_nhds hx)
    have h4 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ E') → ℂ) ω
        (fun y ↦ an_coord E' (e' (f y))) x := contMDiffAt_pi_space.2 hk
    have h5 := ((an_coord E').symm.toContinuousLinearMap.contMDiff.contMDiffAt).comp x h4
    convert h5 using 1
    funext y
    simp
  · intro hf
    classical
    refine ⟨hf.continuous, fun V hV g hg ↦ ?_⟩
    let g' : M' → ℂ := fun y ↦ if h : y ∈ V then g ⟨y, h⟩ else 0
    have hg' : (fun y : V ↦ g' y) = g := funext fun y ↦ by simp [g', y.2]
    have h1 : ContMDiffOn 𝓘(ℂ, E') 𝓘(ℂ, ℂ) ω g' V :=
      (anb_manifold_isHolFun_iff g' hV).1 (by rw [hg']; exact hg)
    have h2 : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (g' ∘ f) (f ⁻¹' V) :=
      h1.comp hf.contMDiffOn (mapsTo_preimage f V)
    have h3 := (anb_manifold_isHolFun_iff (g' ∘ f) (hV.preimage hf.continuous)).2 h2
    have : (fun x : f ⁻¹' V ↦ g ⟨f x, x.2⟩) = fun x : f ⁻¹' V ↦ (g' ∘ f) x :=
      funext fun x ↦ by simp [g', show f x ∈ V from x.2]
    rw [this]
    exact h3

theorem an_manifold_isClosedAnalytic_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (Z : Set M) :
    an_IsClosedAnalytic (an_manifoldSpace E M) Z ↔ IsClosedAnalytic E Z := by
  classical
  constructor
  · rintro ⟨hZc, hZ⟩
    refine ⟨hZc, fun x hx ↦ ?_⟩
    obtain ⟨W, hW, hxW, k, g, hg, hgZ⟩ := hZ x hx
    set e := chartAt E x
    have hxs : x ∈ e.source := mem_chart_source E x
    let U := e.target ∩ e.symm ⁻¹' W
    have hU : IsOpen U := e.continuousOn_symm.isOpen_inter_preimage e.open_target hW
    let f : Fin k → E → ℂ := fun j z ↦ if h : e.symm z ∈ W then g j ⟨e.symm z, h⟩ else 0
    have hfz : ∀ j, ∀ z, ∀ h : e.symm z ∈ W, f j z = g j ⟨e.symm z, h⟩ := fun j z h ↦ by
      simp [f, h]
    refine ⟨U, hU, ⟨e.map_source hxs, by simpa [U, e.left_inv hxs] using hxW⟩,
      inter_subset_left, k, f, fun j z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have hys : e.symm z ∈ e.source := e.map_target hz.1
      obtain ⟨N, hN, hyN, G, hG, hgG⟩ := hg j ⟨e.symm z, hz.2⟩ x hys
      have hG' : AnalyticAt ℂ G (an_coord E (e (e.symm z))) := hG
      rw [e.right_inv hz.1] at hG'
      have hGc : AnalyticAt ℂ (G ∘ an_coord E) z :=
        hG'.comp_of_eq ((an_coord E).toContinuousLinearMap.analyticAt z) rfl
      refine hGc.congr ?_
      have hO : IsOpen (e.target ∩ e.symm ⁻¹' (W ∩ N)) :=
        e.continuousOn_symm.isOpen_inter_preimage e.open_target (hW.inter hN)
      filter_upwards [hO.mem_nhds ⟨hz.1, hz.2, hyN⟩] with z' hz'
      rw [hfz j z' hz'.2.1]
      have := hgG ⟨e.symm z', hz'.2.1⟩ ⟨hz'.2.2, e.map_target hz'.1⟩
      change g j _ = G (an_coord E (e (e.symm z'))) at this
      rw [e.right_inv hz'.1] at this
      exact this.symm
    · rw [hgZ ⟨e.symm z, hz.2⟩]
      exact forall_congr' fun j ↦ by rw [hfz j z hz.2]
  · rintro ⟨hZc, hZ⟩
    refine ⟨hZc, fun x hx ↦ ?_⟩
    obtain ⟨U, hU, hxU, -, n, f, hf, hZf⟩ := hZ x hx
    set e := chartAt E x
    let W := e.source ∩ e ⁻¹' U
    have hW : IsOpen W := e.continuousOn.isOpen_inter_preimage e.open_source hU
    refine ⟨W, hW, ⟨mem_chart_source E x, hxU⟩, n, fun j y ↦ f j (e y), fun j ↦ ?_,
      fun y ↦ ?_⟩
    · refine anb_isHolFun_of_chart _ (an_manifoldSpace E M).isAnalytic fun y ↦
        ⟨x, y.2.1, univ, isOpen_univ, mem_univ _, f j ∘ (an_coord E).symm, ?_, fun y' _ ↦ ?_⟩
      · refine (hf j (e y) y.2.2).comp_of_eq
          ((an_coord E).symm.toContinuousLinearMap.analyticAt _) ?_
        change (an_coord E).symm (an_coord E (e y)) = e y
        simp
      · change f j (e y') = f j ((an_coord E).symm (an_coord E (e y')))
        simp
    · have := hZf (e y) y.2.2
      rw [e.left_inv y.2.1] at this
      exact this

theorem an_manifold_dim_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] (x : M) :
    an_dim (an_manifoldSpace E M) x = ((Module.finrank ℂ E : ℕ∞) : WithBot ℕ∞) := by
  set S := an_manifoldSpace E M
  set c := S.atlas.chart (S.atlas.chartAt x)
  have hx : x ∈ c.dom := S.atlas.mem_chartAt x
  have himg : c.toFun '' (univ ∩ c.dom) = c.U := by
    rw [univ_inter, c.image_eq]
    ext z
    change z ∈ c.U ∧ (0 : Fin 0 → ℂ) = 0 ↔ z ∈ c.U
    simp
  have hmem : c.toFun '' (univ ∩ c.dom) ∈ 𝓝 (c.toFun x) := by
    rw [himg]
    exact c.isOpen_U.mem_nhds (himg ▸ mem_image_of_mem _ ⟨mem_univ _, hx⟩)
  exact anb_dimension_germ_of_mem_nhds hmem

/-! ### F2: closed analytic subspaces -/

theorem an_closedSubspace_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) :
    ∃ SZ : an_ReducedSpace Z, an_IsHom SZ S Subtype.val ∧
      ∀ (W : Type w) [TopologicalSpace W] (C : an_ReducedSpace W) (h : W → Z),
        an_IsHom C S (Subtype.val ∘ h) → an_IsHom C SZ h :=
  ⟨anb_subSpace S hZ, anb_subSpace_val_isHom S hZ, fun _ _ C h hh ↦ anb_subSpace_lift S hZ C h hh⟩

/-! ### F2: dimension -/

theorem an_dimAt_eq_chart_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (Z : Set X) (i : S.atlas.ι) {x : X} (hx : x ∈ (S.atlas.chart i).dom) :
    an_dimAt S Z x = adim2_dimension (S.atlas.chart i).n
      (adim2_germ (S.atlas.chart i).n ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom))
        ((S.atlas.chart i).toFun x)) :=
  anb_dimension_chart_eq S.atlas S.isAnalytic Z _ i (S.atlas.mem_chartAt x) hx

theorem an_dim_eq_stalk_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) (x : X) :
    an_dim S x = ringKrullDim (S.structureSheaf.presheaf.stalk (x : TopCat.of X)) :=
  (anb_ringKrullDim_stalk S _ (S.atlas.mem_chartAt x)).symm

theorem an_dimAt_eq_geomDim_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (x : X) :
    an_dimAt S Z x = an_geomDim S Z x :=
  anb_dimAt_eq_geomDim S hZ x

theorem an_dim_euclid_aux (n : ℕ) (x : Fin n → ℂ) :
    an_dim (an_euclidSpace n) x = ((n : ℕ∞) : WithBot ℕ∞) :=
  anb_dimension_germ_of_mem_nhds (n := n) (A := id '' (univ ∩ univ)) (by simp)

theorem an_dim_node_aux :
    an_dim an_nodeSpace ⟨0, mem_univ _, by funext i; simp [an_nodeEqn]⟩ = 1 := by
  refine anb_dimension_node (Subtype.val '' (univ ∩ univ)) fun z ↦ ?_
  constructor
  · rintro ⟨w, -, rfl⟩
    exact congrFun w.2.2 0
  · intro hz
    refine ⟨⟨z, mem_univ _, ?_⟩, ⟨mem_univ _, mem_univ _⟩, rfl⟩
    funext i
    fin_cases i
    exact hz

/-! ### F3: locality and finiteness -/

theorem an_isClosedAnalytic_of_locally_aux {Y : Type v} [TopologicalSpace Y]
    (T : an_ReducedSpace Y) {Z : Set Y} (hZ : IsClosed Z)
    (h : ∀ y ∈ Z, an_IsLocallyAnalyticAt T Z y) :
    an_IsClosedAnalytic T Z := by
  refine ⟨hZ, fun y hy ↦ ?_⟩
  obtain ⟨V, hV, hyV, T', hT', hZT'⟩ := h y hy
  have hyT' : y ∈ T' := ((Set.ext_iff.1 hZT' y).1 ⟨hy, hyV⟩).1
  obtain ⟨W, hW, hyW, k, g, hg, hgZ⟩ := hT'.2 y hyT'
  refine ⟨W ∩ V, hW.inter hV, ⟨hyW, hyV⟩, k,
    fun j w ↦ g j ⟨w, w.2.1⟩, fun j ↦ anb_isHolFun_restrict T.atlas inter_subset_left (hg j),
    fun w ↦ ?_⟩
  rw [← hgZ ⟨w, w.2.1⟩]
  have := Set.ext_iff.1 hZT' w
  simp only [mem_inter_iff, w.2.2, and_true] at this
  exact this

theorem an_locallyCompactSpace_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) :
    LocallyCompactSpace X := by
  refine ⟨fun x n hn ↦ ?_⟩
  obtain ⟨i, hi⟩ := S.atlas.covers x
  let c := S.atlas.chart i
  have := anb_locallyCompact_dom c
  have hn' : (Subtype.val : c.dom → X) ⁻¹' n ∈ 𝓝 (⟨x, hi⟩ : c.dom) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hn
  obtain ⟨K, hK, hKn, hKc⟩ := local_compact_nhds hn'
  refine ⟨Subtype.val '' K, ?_, by rintro _ ⟨y, hy, rfl⟩; exact hKn hy,
    hKc.image continuous_subtype_val⟩
  exact c.isOpen_dom.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hK

theorem an_dimAt_bounded_aux {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X)
    (Z : Set X) {K : Set X} (hK : IsCompact K) :
    ∃ d : ℕ, ∀ x ∈ K, an_dimAt S Z x ≤ ((d : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ (i : S.atlas.ι) (x : X), x ∈ (S.atlas.chart i).dom →
      an_dimAt S Z x ≤ (((S.atlas.chart i).n : ℕ∞) : WithBot ℕ∞) := by
    intro i x hx
    rw [an_dimAt_eq_chart_aux S Z i hx, adim2_dimension]
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [adim6_parameter_dimension]
    rfl
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i ↦ (S.atlas.chart i).dom)
    (fun i ↦ (S.atlas.chart i).isOpen_dom) (fun x _ ↦ mem_iUnion.2 (S.atlas.covers x))
  refine ⟨t.sup fun i ↦ (S.atlas.chart i).n, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  refine (hle i x hxi).trans ?_
  exact_mod_cast Finset.le_sup (f := fun i ↦ (S.atlas.chart i).n) hi

/-! ### F3: the finite case -/

theorem an_finite_projection_aux (m k : ℕ) (T : Set ((Fin m → ℂ) × (Fin k → ℂ)))
    (hT : IsClosedAnalytic ((Fin m → ℂ) × (Fin k → ℂ)) T)
    (hproper : IsProperMap (fun a : T ↦ (a : (Fin m → ℂ) × (Fin k → ℂ)).1))
    (hfin : ∀ y, {a | a ∈ T ∧ a.1 = y}.Finite) :
    IsClosedAnalytic (Fin m → ℂ) (Prod.fst '' T) :=
  anf_finite_projection m k T hT hproper hfin

theorem an_finite_mapping_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z)
    (hfin : ∀ y, (Z ∩ f ⁻¹' {y}).Finite) :
    an_IsClosedAnalytic T (f '' Z) :=
  anf_finite_mapping S T f hf hZ hfin

/-! ### F3: rank and fibre dimension -/

theorem an_cartan_remmert_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (k : ℕ) :
    an_IsClosedAnalytic S
      {x | x ∈ Z ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ an_dimAt S (Z ∩ f ⁻¹' {f x}) x} :=
  ancr_cartan_remmert_of_chart S T f hf hZ k fun Z' i _ hx ↦ an_dimAt_eq_chart_aux S Z' i hx

theorem an_constant_rank_aux (n m r : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin m → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hr : ∀ z ∈ U, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ g z : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))) = r)
    {x : Fin n → ℂ} (hx : x ∈ U) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin m → ℂ)), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsOpen V ∧
      g '' W ⊆ V ∧
      (∃ (k : ℕ) (F : (Fin m → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ g '' W ↔ F y = 0)) ∧
      adim2_dimension m (adim2_germ m (g '' W) (g x)) = ((r : ℕ∞) : WithBot ℕ∞) :=
  ancr_constant_rank n m r U hU g hg hr hx

/-! ### F3: Remmert–Stein -/

theorem an_remmert_stein_aux (n p : ℕ) (T B : Set (Fin n → ℂ))
    (hT : IsClosedAnalytic (Fin n → ℂ) T) (hBT : Disjoint B T)
    (hB : ∀ z ∉ T, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ Disjoint V T ∧
      ∃ (k : ℕ) (F : (Fin n → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ B ↔ F y = 0))
    (hpure : ∀ z ∈ B, adim2_dimension n (adim2_germ n B z) = ((p : ℕ∞) : WithBot ℕ∞))
    (hdimT : ∀ z ∈ T, adim2_dimension n (adim2_germ n T z) < ((p : ℕ∞) : WithBot ℕ∞)) :
    IsClosedAnalytic (Fin n → ℂ) (closure B) :=
  anr_remmert_stein n p T B hT hBT hB hpure hdimT

/-! ### F3: induction on dimension -/

theorem an_remmert_local_zero_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) {V : Set Y}
    (hV : IsOpen V) (hdim : ∀ x ∈ Z ∩ f ⁻¹' V, an_dimAt S Z x ≤ 0) :
    ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z) y :=
  have := an_locallyCompactSpace_aux T
  anrem_remmert_local_zero S T f hf hZ hV hdim

set_option linter.unusedVariables false in
theorem an_remmert_local_succ_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) (d : ℕ)
    (ih : ∀ Z' : Set X, an_IsClosedAnalytic S Z' → ∀ V : Set Y, IsOpen V →
      (∀ x ∈ Z' ∩ f ⁻¹' V, an_dimAt S Z' x ≤ ((d : ℕ∞) : WithBot ℕ∞)) →
      ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z') y)
    {Z : Set X} (hZ : an_IsClosedAnalytic S Z) {V : Set Y} (hV : IsOpen V)
    (hdim : ∀ x ∈ Z ∩ f ⁻¹' V, an_dimAt S Z x ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z) y := by
  intro y _
  have := an_locallyCompactSpace_aux T
  refine ⟨univ, isOpen_univ, mem_univ _, f '' Z, ?_, rfl⟩
  exact anrem_remmert (fun S T f hf _ hZ hfin ↦ an_finite_mapping_aux S T f hf hZ hfin)
    (fun S _ hZ ↦ (an_closedSubspace_aux.{0, 0} S hZ).elim fun SZ h ↦ ⟨SZ, h.1⟩)
    (fun S Z i _ hx ↦ an_dimAt_eq_chart_aux S Z i hx)
    (fun S Z i _ hx ↦ an_dimAt_eq_chart_aux S Z i hx)
    (fun S T f hf _ hZ k ↦ an_cartan_remmert_aux S T f hf hZ k)
    anrem_local_remmert_stein S T (fun Z' _ hK ↦ an_dimAt_bounded_aux S Z' hK) hf hZ

/-! ### F3: the proper mapping theorem -/

theorem an_remmert_aux {X : Type u} [TopologicalSpace X] {Y : Type v}
    [TopologicalSpace Y] (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) :
    an_IsClosedAnalytic T (f '' Z) := by
  have key : ∀ d : ℕ, ∀ Z' : Set X, an_IsClosedAnalytic S Z' → ∀ V : Set Y, IsOpen V →
      (∀ x ∈ Z' ∩ f ⁻¹' V, an_dimAt S Z' x ≤ ((d : ℕ∞) : WithBot ℕ∞)) →
      ∀ y ∈ V, an_IsLocallyAnalyticAt T (f '' Z') y := by
    intro d
    induction d with
    | zero =>
      intro Z' hZ' V hV hdim
      exact an_remmert_local_zero_aux S T f hf hZ' hV (by simpa using hdim)
    | succ d ih =>
      intro Z' hZ' V hV hdim
      exact an_remmert_local_succ_aux S T f hf d ih hZ' hV hdim
  have := an_locallyCompactSpace_aux T
  refine an_isClosedAnalytic_of_locally_aux T (hf.1.isClosedMap _ hZ.1) fun y _ ↦ ?_
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  obtain ⟨d, hd⟩ := an_dimAt_bounded_aux S Z (hf.1.isCompact_preimage hK)
  exact key d Z hZ (interior K) isOpen_interior
    (fun x hx ↦ hd x (interior_subset (s := K) hx.2)) y (mem_interior_iff_mem_nhds.2 hKy)

theorem an_remmert_not_proper_aux :
    an_IsClosedAnalytic (an_euclidSpace 2) an_hyperbola ∧
      an_IsHom (an_euclidSpace 2) (an_euclidSpace 1) an_proj0 ∧ ¬ IsProperMap an_proj0 ∧
      ¬ an_IsClosedAnalytic (an_euclidSpace 1) (an_proj0 '' an_hyperbola) :=
  ⟨anrem_hyperbola_isClosedAnalytic, an_proj0_isHom, anrem_proj0_not_proper,
    fun h ↦ anrem_not_closed_image h.1⟩

theorem an_remmert_manifold_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ω M] {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω P] (π : P → M)
    (hπ : IsProperMap π) (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, E) ω π) {Z : Set P}
    (hZ : IsClosedAnalytic (Fin d → ℂ) Z) : IsClosedAnalytic E (π '' Z) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  refine ⟨hπ.isClosedMap _ hZ.1, fun y hy ↦ ?_⟩
  let V : Opens M := ⟨(chartAt E y).source, (chartAt E y).open_source⟩
  have hyV : y ∈ V := mem_chart_source E y
  let W : Opens P := ⟨π ⁻¹' (V : Set M), (chartAt E y).open_source.preimage hπ.continuous⟩
  let π' : W → V := (V : Set M).restrictPreimage π
  have hπ' : IsProperMap π' := anrem_isProperMap_restrictPreimage hπ V
  have : SecondCountableTopology V :=
    (chartAt E y).toHomeomorphSourceTarget.secondCountableTopology
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace E V
  have : SigmaCompactSpace W := by
    obtain ⟨K, hK, hKu⟩ := SigmaCompactSpace.exists_compact_covering (X := V)
    refine SigmaCompactSpace_iff_exists_compact_covering.2
      ⟨fun n ↦ π' ⁻¹' K n, fun n ↦ hπ'.isCompact_preimage (hK n), ?_⟩
    rw [← preimage_iUnion, hKu, preimage_univ]
  have : SecondCountableTopology W := ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℂ) W
  have hhol' : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, E) ω π' :=
    fun x ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, E) ω) π' univ x).1
        ((hhol.comp contMDiff_subtype_val) x)
  have hZ' : an_IsClosedAnalytic (an_manifoldSpace (Fin d → ℂ) W) (Subtype.val ⁻¹' Z) :=
    (an_manifold_isClosedAnalytic_iff_aux _).2 (anrem_isClosedAnalytic_restrict_opens hZ W)
  have himg := an_remmert_aux (an_manifoldSpace (Fin d → ℂ) W) (an_manifoldSpace E V) π'
    ⟨hπ', (an_manifold_isHom_iff_aux π').2 hhol'⟩ hZ'
  have heq : π' '' (Subtype.val ⁻¹' Z) = Subtype.val ⁻¹' (π '' Z) := by
    ext ⟨v, hv⟩
    constructor
    · rintro ⟨⟨x, hx⟩, hxZ, hxv⟩
      exact ⟨x, hxZ, congrArg Subtype.val hxv⟩
    · rintro ⟨x, hxZ, hxv⟩
      exact ⟨⟨x, show π x ∈ (V : Set M) from hxv ▸ hv⟩, hxZ, Subtype.ext hxv⟩
  rw [heq] at himg
  exact anrem_isClosedAnalytic_of_opens V hyV ((an_manifold_isClosedAnalytic_iff_aux _).1 himg) hy

end HodgeLean.Foundations.Analytic
