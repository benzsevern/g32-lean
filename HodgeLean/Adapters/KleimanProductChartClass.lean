import HodgeLean.Adapters.KleimanProductCharts
import HodgeLean.Adapters.CycleClassSmoothChartsProofs

/-! # Restricted prime classes in holomorphic normal charts

Near a smooth point of a component support the supported prime class restricts to a
normal-projection coclass of a holomorphic flattening chart. A holomorphic normal map that cuts
out the support as a submersion pulls back the normalized class to the same coclass, by the
orientation invariance of complex-differentiable changes of normal coordinates. Purity along the
singular filtration on an arbitrary open removes the singular locus, and lowest-degree germ
detection then identifies the two classes.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.Limits
open Filter Topology Set

open HodgeLean.RealDefs AlgebraicTopology.Singular TopologicalSpace
open scoped ContDiff Manifold
namespace HodgeLean.Adapters

attribute [local instance] overSpecAlgebra

private theorem hc9k_cc_chartNormalProjectionCoclass_pullback
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (V : Set M) (W : Set N) (hV : V ⊆ e.source) (hW : W ⊆ d.source)
    (φ : neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair W T)
    (hφ : ∀ y : V, (d (TopPair.Hom.fst φ y).1).2 = (e y.1).2) :
    relativeCohomologyMap ℚ (2 * c) φ
      (chartNormalProjectionCoclass F c d T hT W hW) =
        chartNormalProjectionCoclass E c e S hS V hV := by
  have hcomp : φ ≫ chartNormalProjectionPair F c d T hT W hW =
      chartNormalProjectionPair E c e S hS V hV := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      apply Subtype.ext
      change (d (TopPair.Hom.snd φ y).1.1).2 = (e y.1.1).2
      have hw : (TopPair.Hom.snd φ y).1 = TopPair.Hom.fst φ y.1 :=
        TopPair.Hom.w_apply φ y
      rw [hw]
      exact hφ y.1
    · ext y
      exact hφ y
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp]


private theorem hc9k_cc_smoothClosedSupportCoclass_germ_eq_normalChart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d - m) → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0)
    (he : Point.map i z ∈ e.source)
    (ht : AnalyticAt ℂ
      ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e)
      (closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z)))
    (hti : AnalyticAt ℂ
      ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e).symm
      (((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e)
        (closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z)))) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm (Point.map i z)
      (smoothClosedSupportCoclassSection X Y i m d) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m)) ⟨e.source, e.open_source⟩
      (Point.map i z) he
      (chartNormalProjectionCoclass (Fin m → ℂ) (d - m) e
        (Set.range (Point.map i)) hS e.source (le_refl _)) := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z _
      (mem_smoothClosedSupportChartOpen X Y i m d z)]
  obtain ⟨W, hW, hW', hxW, hclasses⟩ :=
    exists_open_chartNormalProjectionCoclass_eq (d - m)
      (closedImmersionHolomorphicFlatteningChart X Y i m d z) e
      (Set.range (Point.map i))
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
      hS (Point.map i z) (mem_smoothClosedSupportChartOpen X Y i m d z)
      ((closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z _
        (mem_smoothClosedSupportChartOpen X Y i m d z)).mp ⟨z, rfl⟩) he ht hti
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    hW hW' (Point.map i z) hxW
  exact (chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    hW (le_refl _)).trans (hclasses.trans
      (chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
        e (Set.range (Point.map i)) hS hW' (le_refl _)).symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hc9k_cc_supportOpenIso_toSheaf
    {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
    (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B) (n : ℕ) :
    supportRelativeCohomologyToSheaf Y B n ≫
      (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom =
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (supportRelativeCohomologyToSheaf X S n) := by
  let := hf.functor_isContinuous
  let := hf.functor_isCocontinuous
  change toSheafify (Opens.grothendieckTopology Y) _ ≫
    ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv).hom ≫
    (supportOpenEmbeddingSheafificationIso f hf _).hom.hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact hf.functor.toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (supportRelativeCohomologyPresheaf X S n)

set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_smoothClosedSupportCoclass_restrict_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.map
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection X Y i m d) =
    smoothClosedSupportChartSheafSection X Y i m d z := by
  apply TopCat.Presheaf.section_ext
  intro a ha
  rw [TopCat.Presheaf.germ_res_apply]
  exact (smoothClosedSupportCoclassSection_germ X Y i m d a).trans
    (smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z a ha)

set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_smoothClosedSupportCoclass_openImage_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i)) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.map
      (hf.functor.map (homOfLE
        (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top))).op
      (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d)) =
    (supportRelativeCohomologyToSheaf M S (2 * (d - m))).app
      (Opposite.op (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)))
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
        (2 * (d - m))).inv.app (Opposite.op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  have hn := ConcreteCategory.congr_hom
    ((supportRelativeCohomologySheafOpenIso f hf S (Set.range (Point.map i)) hS
      (2 * (d - m))).hom.hom.naturality
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op)
    (smoothClosedSupportCoclassSection X Y i m d)
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (hc9k_cc_supportOpenIso_toSheaf f hf S
      (Set.range (Point.map i)) hS (2 * (d - m)))
      (Opposite.op (smoothClosedSupportChartOpen X Y i m d z)))
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))
  change _ = _ at hn
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    hc9k_cc_smoothClosedSupportCoclass_restrict_chart] at hn
  exact hn.symm.trans hu


set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_smoothClosedSupportCoclass_transported_germ
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (U : Opens M) (hU : hf.functor.obj ⊤ = U) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ U
      (f (Point.map i z)) (hU ▸ ⟨Point.map i z, Set.mem_univ _, rfl⟩)
      (supportRelativeCohomologySectionOnOpen f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) U hU (smoothClosedSupportCoclassSection X Y i m d)) =
    supportRelativeCohomologyGerm M S (2 * (d - m))
      (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)) (f (Point.map i z))
      ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
        (2 * (d - m))).inv.app (Opposite.op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  subst U
  change (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ _ _ _
    ((supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.map (𝟙 _)
      (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d))) = _
  rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have h := (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ_res_apply
    (hf.functor.map (homOfLE
      (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)))
    (f (Point.map i z))
    ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩
    (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
      (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d))
  rw [hc9k_cc_smoothClosedSupportCoclass_openImage_chart] at h
  exact h.symm


set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_chartNormalProjectionCoclass_openImage
    {M N E : Type} [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (f : M → N) (hf : IsOpenEmbedding f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (B : Set M) (S : Set N) (hB : f ⁻¹' S = B)
    (he : ∀ y ∈ e.source, y ∈ B ↔ (e y).2 = 0)
    (he' : ∀ y ∈ (e.lift_openEmbedding hf).source,
      y ∈ S ↔ (e.lift_openEmbedding hf y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) :
    (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W B S
      (fun y _ => by rw [← hB]; rfl) (2 * c)).symm
      (chartNormalProjectionCoclass E c e B he W hW) =
    chartNormalProjectionCoclass E c (e.lift_openEmbedding hf) S he'
      (f '' W) (Set.image_mono hW) := by
  apply (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W B S
    (fun y _ => by rw [← hB]; rfl) (2 * c)).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = relativeCohomologyMap ℚ (2 * c)
    (neighborhoodSupportPairImageIso f hf.isEmbedding W B S
      (fun y _ => by rw [← hB]; rfl)).hom _
  symm
  apply hc9k_cc_chartNormalProjectionCoclass_pullback
  intro y
  change (e.lift_openEmbedding hf (f y.1)).2 = (e y.1).2
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]


private theorem hc9k_cc_product_normal_chart
    {E F G K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (c : ℕ) (g : E → F) (φ : OpenPartialHomeomorph E (F × K))
    (hφg : ∀ y, (φ y).1 = g y)
    (d : OpenPartialHomeomorph F (G × (Fin c → ℂ)))
    (S : Set F) (hS : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (a : E) (ha : a ∈ φ.source) (hga : g a ∈ d.source)
    (hφ : AnalyticAt ℂ φ a) (hφi : AnalyticAt ℂ φ.symm (φ a))
    (hd : AnalyticAt ℂ d (g a)) (hdi : AnalyticAt ℂ d.symm (d (g a))) :
    ∃ e : OpenPartialHomeomorph E ((G × K) × (Fin c → ℂ)),
      a ∈ e.source ∧ (∀ y, (e y).2 = (d (g y)).2) ∧
      (∀ y ∈ e.source, y ∈ g ⁻¹' S ↔ (e y).2 = 0) ∧
      AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm (e a) := by
  let p := d.prod (OpenPartialHomeomorph.refl K)
  let r : ((G × (Fin c → ℂ)) × K) ≃L[ℂ] ((G × K) × (Fin c → ℂ)) :=
    (ContinuousLinearEquiv.prodAssoc ℂ G (Fin c → ℂ) K).trans
      (((ContinuousLinearEquiv.refl ℂ G).prodCongr
        (ContinuousLinearEquiv.prodComm ℂ (Fin c → ℂ) K)).trans
          (ContinuousLinearEquiv.prodAssoc ℂ G K (Fin c → ℂ)).symm)
  let e := (φ.trans p).trans r.toHomeomorph.toOpenPartialHomeomorph
  have hpa : φ a ∈ p.source := ⟨(hφg a).symm ▸ hga, Set.mem_univ _⟩
  have hea : a ∈ e.source := ⟨⟨ha, hpa⟩, Set.mem_univ _⟩
  have hen : ∀ y, (e y).2 = (d (g y)).2 := by
    intro y
    change (d (φ y).1).2 = _
    rw [hφg]
  have hp : AnalyticAt ℂ p (φ a) :=
    (show AnalyticAt ℂ d (φ a).1 from (hφg a).symm ▸ hd).comp analyticAt_fst |>.prod
      analyticAt_snd
  have hdi' : AnalyticAt ℂ d.symm (p (φ a)).1 := by
    change AnalyticAt ℂ d.symm (d (φ a).1)
    rw [hφg]
    exact hdi
  have hpi : AnalyticAt ℂ p.symm (p (φ a)) :=
    (hdi'.comp (f := Prod.fst) (x := p (φ a)) analyticAt_fst).prod analyticAt_snd
  refine ⟨e, hea, hen, ?_, ?_, ?_⟩
  · intro y hy
    rw [hen]
    exact hS (g y) ((hφg y) ▸ hy.1.2.1)
  · exact (r.toContinuousLinearMap.analyticAt _).comp (hp.comp hφ)
  · have hpir : AnalyticAt ℂ p.symm (r.symm (r (p (φ a)))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hpi
    have hφir : AnalyticAt ℂ φ.symm (p.symm (r.symm (r (p (φ a))))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply, p.left_inv hpa] using hφi
    exact hφir.comp (f := fun w => p.symm (r.symm w)) (x := r (p (φ a)))
      (hpir.comp (f := r.symm) (x := r (p (φ a)))
        (r.symm.toContinuousLinearMap.analyticAt _))


set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_smoothClosedSupportCoclass_ambient_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (U : Opens M) (hU : hf.functor.obj ⊤ = U) :
    ∃ (e : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin (d - m) → ℂ))),
      e = (closedImmersionHolomorphicFlatteningChart X Y i m d z).lift_openEmbedding hf ∧
      ∃ (he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
      (ha : f (Point.map i z) ∈ e.source),
      (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ U
        (f (Point.map i z)) (hU ▸ ⟨Point.map i z, Set.mem_univ _, rfl⟩)
        (supportRelativeCohomologySectionOnOpen f hf S (Set.range (Point.map i)) hS
          (2 * (d - m)) U hU (smoothClosedSupportCoclassSection X Y i m d)) =
      supportRelativeCohomologyGerm M S (2 * (d - m)) ⟨e.source, e.open_source⟩
        (f (Point.map i z)) ha
        (chartNormalProjectionCoclass (Fin m → ℂ) (d - m) e S he e.source (le_refl _)) := by
  let e₀ := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e := e₀.lift_openEmbedding hf
  have he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    change f y ∈ S ↔ (e₀.lift_openEmbedding hf (f y)).2 = 0
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change y ∈ f ⁻¹' S ↔ _
    rw [hS]
    exact closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z y hy
  refine ⟨e, rfl, he, ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩, ?_⟩
  have h := hc9k_cc_smoothClosedSupportCoclass_transported_germ X Y i m d z f hf S hS U hU
  convert h using 1
  congr 1
  exact (hc9k_cc_chartNormalProjectionCoclass_openImage (d - m) f hf e₀
    (Set.range (Point.map i)) S hS
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) he
    e₀.source (le_refl _)).symm
private theorem hc9k_cc_component_smoothLift_point
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (a : ComplexPoint X)
    (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ z : ComplexPoint (cycleComponentSmoothLocusOver X x),
      cycleComponentSmoothClosedLiftAmbientMap X x
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) = a := by
  have hrange : a ∈ Set.range (cycleComponentSmoothClosedLiftAmbientMap X x) := by
    rw [← Set.image_univ]
    change a ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤
    rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact ha
  obtain ⟨b, rfl⟩ := hrange
  have hb : b ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
    exact haS
  obtain ⟨z, rfl⟩ := hb
  exact ⟨z, rfl⟩
private theorem hc9k_cc_openEmbedding_chart_analytic
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    [Etale i.left] (hi : IsOpenEmbedding (Point.map i)) (b : ComplexPoint Y) :
    let e := (localChart X d (Point.map i b)).symm.trans
      ((localChart Y d b).lift_openEmbedding hi)
    AnalyticAt ℂ e (localChart X d (Point.map i b) (Point.map i b)) ∧
    AnalyticAt ℂ e.symm (e (localChart X d (Point.map i b) (Point.map i b))) := by
  let C := localChart X d (Point.map i b)
  let D := localChart Y d b
  let e := C.symm.trans (D.lift_openEmbedding hi)
  have hb : D b ∈ e.symm.source := by
    refine ⟨D.map_source (mem_localChart_source Y d b), ?_⟩
    change Point.map i (D.symm (D b)) ∈ C.source
    rw [D.left_inv (mem_localChart_source Y d b)]
    exact mem_localChart_source X d (Point.map i b)
  have he : e.symm (D b) = C (Point.map i b) := by
    change C (Point.map i (D.symm (D b))) = _
    rw [D.left_inv (mem_localChart_source Y d b)]
  have he' : e (C (Point.map i b)) = D b := by
    rw [← he]
    exact e.symm.left_inv hb
  have ha : AnalyticAt ℂ e.symm (D b) :=
    analyticAt_inclusionInComplexCharts X Y i d d b
  have hd := ccm5_etale_chart_derivative_bijective_aux Y X i d d b
  let L := ContinuousLinearEquiv.ofBijective
    (fderiv ℂ (inclusionInComplexCharts X Y i d d b) (D b)) (LinearMap.ker_eq_bot.mpr hd.1) (LinearMap.range_eq_top.mpr hd.2)
  have hinv := e.symm.analyticAt_symm' (i := L) hb ha rfl
  change AnalyticAt ℂ e (C (Point.map i b)) ∧ AnalyticAt ℂ e.symm (e (C (Point.map i b)))
  refine ⟨?_, ?_⟩
  · simpa only [OpenPartialHomeomorph.symm_symm, he] using hinv
  · rwa [he']
private theorem hc9k_cc_lifted_flatteningChart_analytic
    (X Y O : Over (Spec ↧ℂ)) (i : Y ⟶ X) (j : X ⟶ O) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension d O.hom] [IsClosedImmersion i.left]
    [Etale j.left] (hj : IsOpenEmbedding (Point.map j)) (z : ComplexPoint Y) :
    let e := (closedImmersionHolomorphicFlatteningChart X Y i m d z).lift_openEmbedding hj
    let C := localChart O d (Point.map j (Point.map i z))
    AnalyticAt ℂ (C.symm.trans e) (C (Point.map j (Point.map i z))) ∧
    AnalyticAt ℂ (C.symm.trans e).symm (e (Point.map j (Point.map i z))) := by
  let b := Point.map i z
  let C := localChart O d (Point.map j b)
  let D := localChart X d b
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  let e₀ := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e := e₀.lift_openEmbedding hj
  let t := C.symm.trans (D.lift_openEmbedding hj)
  have hb : b ∈ e₀.source := mem_smoothClosedSupportChartOpen X Y i m d z
  have hA : AnalyticAt ℂ A (D b) ∧ AnalyticAt ℂ A.symm (e₀ b) :=
    ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hb.1.2).2
  have ht := hc9k_cc_openEmbedding_chart_analytic O X j d hj b
  have htval : t (C (Point.map j b)) = D b := by
    change (D.lift_openEmbedding hj) (C.symm (C (Point.map j b))) = _
    rw [C.left_inv (mem_localChart_source O d (Point.map j b)),
      OpenPartialHomeomorph.lift_openEmbedding_apply]
  have hcenter : C (Point.map j b) ∈ t.source := by
    refine ⟨C.map_source (mem_localChart_source O d (Point.map j b)), ?_⟩
    change C.symm (C (Point.map j b)) ∈ (D.lift_openEmbedding hj).source
    rw [C.left_inv (mem_localChart_source O d (Point.map j b))]
    exact ⟨b, mem_localChart_source X d b, rfl⟩
  have heval : e (Point.map j b) = e₀ b := OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have hAval : A.symm (e₀ b) = D b := A.left_inv hb.1.2.1
  change AnalyticAt ℂ (C.symm.trans e) (C (Point.map j b)) ∧
    AnalyticAt ℂ (C.symm.trans e).symm (e (Point.map j b))
  constructor
  · have hcomp : AnalyticAt ℂ (A ∘ t) (C (Point.map j b)) :=
      (htval.symm ▸ hA.1).comp ht.1
    apply hcomp.congr
    filter_upwards [t.open_source.mem_nhds hcenter] with v hv
    obtain ⟨y, hy, heq⟩ := hv.2
    change Point.map j y = C.symm v at heq
    change A ((D.lift_openEmbedding hj) (C.symm v)) = e (C.symm v)
    rw [← heq, OpenPartialHomeomorph.lift_openEmbedding_apply,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  · rw [heval]
    have hti : AnalyticAt ℂ t.symm (A.symm (e₀ b)) := by
      rw [hAval, ← htval]
      exact ht.2
    exact hti.comp hA.2

set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_componentClass_germ_exists_normalChart
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)))
      (he : ∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0)
      (hae : a ∈ e.source),
      ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x) (2 * q) a
        (cycleComponentSupportedInjectiveClass X x hx) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * q) ⟨e.source, e.open_source⟩ a hae
        (chartNormalProjectionCoclass (Fin (dim X.left - q) → ℂ) q e
          (cycleComponentSupport X x) he e.source (le_refl _)) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e)
        (localChart X (dim X.left) a a) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e).symm (e a) := by
  obtain ⟨z, rfl⟩ := hc9k_cc_component_smoothLift_point X x a ha haS
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have h := hc9k_cc_smoothClosedSupportCoclass_ambient_chart
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - q) (dim X.left) z
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x) (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
  obtain ⟨e, heq, he, hae, hg⟩ := h
  have : Etale (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)).left := by
    change Etale (cycleComponentSmoothLocusAmbientOpen X x).ι
    infer_instance
  have hA := hc9k_cc_lifted_flatteningChart_analytic
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x) X
    (cycleComponentSmoothLocusClosedLiftOver X x)
    (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x))
    (dim X.left - q) (dim X.left)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x) z
  rw [← heq] at hA
  rw [ccm5_componentClass_normalized_germ_aux X q x hx _ ha]
  unfold cycleComponentSmoothSupportCoclassSection cycleComponentSmoothClosedLiftCoclassSection
  have hcod := cycleComponentSmoothClosedLift_codimension X x hx
  generalize_proofs at *
  generalize hm : dim X.left - q = m at *
  cases hcod
  exact ⟨e, he, hae, hg, hA⟩

set_option backward.isDefEq.respectTransparency false in
private theorem hc9k_cc_supportGerm_exists_restrict_eq
    (X : TopCat.{0}) (S : Set X) (n : ℕ) {U V : Opens X}
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : supportRelativeCohomologyGerm X S n U x hxU a =
      supportRelativeCohomologyGerm X S n V x hxV b) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWU S) a =
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWV S) b := by
  let P := supportRelativeCohomologyPresheaf X S n
  let η := supportRelativeCohomologyToSheaf X S n
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  have h' : P.germ U x hxU a = P.germ V x hxV b := by
    apply (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).1
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact h
  obtain ⟨W, hxW, iU, iV, he⟩ := P.germ_eq x hxU hxV a b h'
  exact ⟨W, hxW, leOfHom iU, leOfHom iV, he⟩
set_option backward.isDefEq.respectTransparency false in
/-- Near a smooth support point, the supported prime class restricts to the normal-projection
coclass of a holomorphic flattening chart. -/
theorem hc9k_cc_componentClass_restrict_normalChart
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)))
      (he : ∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0),
      a ∈ e.source ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e)
        (localChart X (dim X.left) a a) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e).symm (e a) ∧
      ∃ (W : Opens (ComplexPoint X)) (_haW : a ∈ W) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source),
        relativeCohomologyMap ℚ (2 * q)
          (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆ Set.univ from Set.subset_univ _)
            (cycleComponentSupport X x))
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) (2 * q)
            (cycleComponentSupportedInjectiveClass X x hx)) =
        chartNormalProjectionCoclass (Fin (dim X.left - q) → ℂ) q e
          (cycleComponentSupport X x) he W hWe := by
  obtain ⟨e, he, hae, hg, heA, heI⟩ := hc9k_cc_componentClass_germ_exists_normalChart X q x hx a ha haS
  obtain ⟨W, haW, hWU, hWV, hW⟩ :=
    hc9k_cc_supportGerm_exists_restrict_eq (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * q) a (show a ∈ (⊤ : Opens (ComplexPoint X)) from trivial)
      hae _ _ hg
  refine ⟨e, he, hae, heA, heI, W, haW, hWV, ?_⟩
  exact hW.trans (chartNormalProjectionCoclass_restrict (Fin (dim X.left - q) → ℂ)
    q e (cycleComponentSupport X x) he hWV (le_refl _))



/-- The normal map of a chart read along the normal slice through a point.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, normal slices. -/
def hc9k_sliceNormalMap {M E : Type} [TopologicalSpace M] [TopologicalSpace E] (c : ℕ)
    (U : Opens M) (f : C(U, Fin c → ℂ)) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (a : E)
    (v : Fin c → ℂ) : Fin c → ℂ := by
  classical
  exact if h : e.symm (a, v) ∈ U then f ⟨_, h⟩ else 0

/-- A holomorphic submersion on an open, read in a coordinate chart at a point of `U`, is
differentiable with surjective derivative there. -/
theorem hc9k_chart_rep_fderiv {d c : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
    (U : Opens M) (f : C(U, Fin c → ℂ))
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) ω f) (u : U)
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) f u)) :
    DifferentiableAt ℂ (fun w => f ((chartAt (Fin d → ℂ) u).symm w)) (chartAt (Fin d → ℂ) u u) ∧
    Function.Surjective (fderiv ℂ (fun w => f ((chartAt (Fin d → ℂ) u).symm w))
      (chartAt (Fin d → ℂ) u u)) := by
  have hm : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) f u :=
    (hhol u).mdifferentiableAt (by simp)
  have hd := hm.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id] at hd
  refine ⟨hd, ?_⟩
  rw [hm.mfderiv] at hsub
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, range_id, fderivWithin_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id] at hsub
  intro y
  obtain ⟨v, hv⟩ := hsub ((tangentSpaceCastModel 𝓘(ℂ, Fin c → ℂ) (f u)).symm y)
  refine ⟨(tangentSpaceCastModel 𝓘(ℂ, Fin d → ℂ) u) v, ?_⟩
  have := congrArg (tangentSpaceCastModel 𝓘(ℂ, Fin c → ℂ) (f u)) hv
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply] at this
  exact this

/-- Along the normal slice of a holomorphic flattening chart, a holomorphic submersion cutting
out the flattened support has invertible complex derivative at the support point. -/
theorem hc9k_sliceNormalMap_hasFDerivAt {d m c : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
    (U : Opens M) (S : Set M) (f : C(U, Fin c → ℂ)) (hf : ∀ u : U, f u = 0 ↔ u.1 ∈ S)
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) ω f)
    (e : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (a : M) (haU : a ∈ U) (hae : a ∈ e.source)
    (ha0 : (e a).2 = 0)
    (hR : AnalyticAt ℂ ((chartAt (Fin d → ℂ) a).symm.trans e) (chartAt (Fin d → ℂ) a a))
    (hT : AnalyticAt ℂ ((chartAt (Fin d → ℂ) a).symm.trans e).symm (e a))
    (hsub : Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) f ⟨a, haU⟩)) :
    ∃ L : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ), Function.Injective L ∧
      HasFDerivAt (hc9k_sliceNormalMap c U f e (e a).1) L 0 := by
  classical
  let C := chartAt (Fin d → ℂ) a
  let u : U := ⟨a, haU⟩
  let CU := chartAt (Fin d → ℂ) u
  have hCU : CU = C.subtypeRestr ⟨u⟩ := rfl
  let a₀ := (e a).1
  have hea : e a = (a₀, 0) := Prod.ext rfl ha0
  have haC : a ∈ C.source := mem_chart_source _ a
  let w₀ := C a
  let F₀ : (Fin d → ℂ) → (Fin c → ℂ) := fun w => f (CU.symm w)
  have hCUu : CU u = w₀ := rfl
  obtain ⟨hF₀d, hF₀s⟩ := hc9k_chart_rep_fderiv U f hhol u hsub
  let T : (Fin m → ℂ) × (Fin c → ℂ) → (Fin d → ℂ) := fun v => C (e.symm v)
  let R : (Fin d → ℂ) → (Fin m → ℂ) × (Fin c → ℂ) := fun w => e (C.symm w)
  have hTa : AnalyticAt ℂ T (e a) := hT
  have hRa : AnalyticAt ℂ R w₀ := hR
  have hRw : R w₀ = e a := by
    change e (C.symm (C a)) = e a
    rw [C.left_inv haC]
  have hTe : T (e a) = w₀ := by
    change C (e.symm (e a)) = C a
    rw [e.left_inv hae]
  -- the derivative of `T` is surjective
  have hTs : Function.Surjective (fderiv ℂ T (e a)) := by
    rw [← hRw]
    apply hc9k_fderiv_surjective_of_rightInverse T R w₀ (hRw ▸ hTa.differentiableAt)
      hRa.differentiableAt
    have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C.target := C.open_target.mem_nhds (C.map_source haC)
    have h2 : ∀ᶠ w in 𝓝 w₀, C.symm w ∈ e.source := by
      have hc : ContinuousAt C.symm w₀ := C.continuousAt_symm (C.map_source haC)
      apply hc
      rw [show C.symm w₀ = a from C.left_inv haC]
      exact e.open_source.mem_nhds hae
    filter_upwards [h1, h2] with w hw1 hw2
    change C (e.symm (e (C.symm w))) = w
    rw [e.left_inv hw2, C.right_inv hw1]
  let G : (Fin m → ℂ) × (Fin c → ℂ) → (Fin c → ℂ) := fun v => F₀ (T v)
  have hF₀d' : DifferentiableAt ℂ F₀ (T (e a)) := by rw [hTe]; exact hF₀d
  have hF₀s' : Function.Surjective (fderiv ℂ F₀ (T (e a))) := by rw [hTe]; exact hF₀s
  have hGd : DifferentiableAt ℂ G (e a) := hF₀d'.comp (e a) hTa.differentiableAt
  have hKc : fderiv ℂ G (e a) = (fderiv ℂ F₀ (T (e a))).comp (fderiv ℂ T (e a)) :=
    fderiv_comp (e a) hF₀d' hTa.differentiableAt
  have hK' : Function.Surjective (fderiv ℂ G (e a)) := by
    intro y
    obtain ⟨w, hw⟩ := hF₀s' y
    obtain ⟨v, rfl⟩ := hTs w
    exact ⟨v, by rw [hKc]; exact hw⟩
  rw [hea] at hGd hK'
  let K := fderiv ℂ G (a₀, 0)
  have hK : Function.Surjective K := hK'
  -- points of the slice and of the flattened support near the center
  have hgood : ∀ᶠ v in 𝓝 (e a), v ∈ e.target ∧ e.symm v ∈ U ∧ e.symm v ∈ C.source := by
    have h1 : ∀ᶠ v in 𝓝 (e a), v ∈ e.target := e.open_target.mem_nhds (e.map_source hae)
    have hc : ContinuousAt e.symm (e a) := e.continuousAt_symm (e.map_source hae)
    have h2 : ∀ᶠ v in 𝓝 (e a), e.symm v ∈ (U : Set M) ∩ C.source := by
      apply hc
      rw [e.left_inv hae]
      exact (U.isOpen.inter C.open_source).mem_nhds ⟨haU, haC⟩
    filter_upwards [h1, h2] with v hv1 hv2
    exact ⟨hv1, hv2.1, hv2.2⟩
  have hGval : ∀ v, v ∈ e.target → ∀ h : e.symm v ∈ U, e.symm v ∈ C.source →
      G v = f ⟨e.symm v, h⟩ := by
    intro v hv h hC
    change f (CU.symm (C (e.symm v))) = _
    congr 1
    apply Subtype.ext
    have hmem : C (e.symm v) ∈ CU.target := by
      have hs : (⟨e.symm v, h⟩ : U) ∈ CU.source := by
        rw [hCU, OpenPartialHomeomorph.subtypeRestr_source]
        exact hC
      exact CU.map_source hs
    have := C.subtypeRestr_symm_eqOn ⟨u⟩ (hCU ▸ hmem)
    simp only [Function.comp_apply] at this
    rw [hCU, ← this, C.left_inv hC]
  -- `K` kills the tangent directions of the support
  have hKinl : K.comp (ContinuousLinearMap.inl ℂ (Fin m → ℂ) (Fin c → ℂ)) = 0 := by
    have hcomp := (hGd.hasFDerivAt.comp a₀
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) a₀ (0 : Fin c → ℂ)))
    have hzero : (fun t => G (t, 0)) =ᶠ[𝓝 a₀] fun _ => 0 := by
      have hcont : ContinuousAt (fun t : Fin m → ℂ => (t, (0 : Fin c → ℂ))) a₀ :=
        (continuous_id.prodMk continuous_const).continuousAt
      have := hcont.preimage_mem_nhds (hea ▸ hgood)
      filter_upwards [this] with t ht
      obtain ⟨h1, h2, h3⟩ := ht
      rw [hGval _ h1 h2 h3]
      apply (hf _).mpr
      apply (hS _ (e.map_target h1)).mpr
      change (e (e.symm (t, 0))).2 = 0
      rw [e.right_inv h1]
    have h0 := (hasFDerivAt_const (𝕜 := ℂ) (0 : Fin c → ℂ) a₀).congr_of_eventuallyEq hzero
    exact hcomp.unique h0
  let L := K.comp (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin c → ℂ))
  have hLs : Function.Surjective L := by
    intro y
    obtain ⟨w, hw⟩ := hK y
    refine ⟨w.2, ?_⟩
    have hw' : w = ContinuousLinearMap.inl ℂ (Fin m → ℂ) (Fin c → ℂ) w.1 +
        ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin c → ℂ) w.2 := by
      ext <;> simp
    have h1 := congrArg (fun A => A w.1) hKinl
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      zero_apply] at h1
    rw [hw', map_add, h1, zero_add] at hw
    exact hw
  refine ⟨L, LinearMap.injective_iff_surjective.mpr hLs, ?_⟩
  have hcomp := hGd.hasFDerivAt.comp (0 : Fin c → ℂ)
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) a₀ (0 : Fin c → ℂ))
  apply hcomp.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun v : Fin c → ℂ => (a₀, v)) 0 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have := hcont.preimage_mem_nhds (hea ▸ hgood)
  filter_upwards [this] with v hv
  obtain ⟨h1, h2, h3⟩ := hv
  change (if h : e.symm (a₀, v) ∈ U then f ⟨_, h⟩ else 0) = G (a₀, v)
  rw [dite_eq_left_of_eq_true (eq_true (show e.symm (a₀, v) ∈ U from h2)), hGval _ h1 h2 h3]



/-- A holomorphic normal map pulls the normalized class back to the chart coclass on a flattened
neighborhood, once its slice derivative is invertible. -/
theorem hc9k_normalMap_pullback_eq_chartCoclass {M E : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ) (U : Opens M) (S : Set M)
    (f : C(U, Fin c → ℂ)) (hf : ∀ u : U, f u = 0 ↔ u.1 ∈ S)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (hsU : e.source ⊆ U)
    (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)
    (L : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) (hL : Function.Injective L)
    (hd : HasFDerivAt (hc9k_sliceNormalMap c U f e (e x).1) L 0) :
    relativeCohomologyMap ℚ (2 * c)
        (neighborhoodSupportInclusionPairMap
          ((flattenedSupportNeighborhood_subset_source E c e x hx).trans hsU) S)
        (relativeCohomologyMap ℚ (2 * c)
          (hc9k_normalCoordinatePair U S c f (fun u => (hf u).mp)) (normalizedPointCoclass c)) =
      chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx) := by
  classical
  let W := flattenedSupportNeighborhood E c e x hx
  let a := (e x).1
  let g := hc9k_sliceNormalMap c U f e a
  have hex : e x = (a, (0 : Fin c → ℂ)) := Prod.ext rfl h0
  let U₀ : Set (Fin c → ℂ) := {v | (a, v) ∈ e.target ∧ e.symm (a, v) ∈ W}
  have hU₀ : IsOpen U₀ :=
    (e.isOpen_inter_preimage_symm W.isOpen).preimage (continuous_const.prodMk continuous_id)
  have h0U : (0 : Fin c → ℂ) ∈ U₀ := by
    change (a, 0) ∈ e.target ∧ e.symm (a, 0) ∈ W
    rw [← hex, e.left_inv hx]
    exact ⟨e.map_source hx, mem_flattenedSupportNeighborhood E c e x hx⟩
  have hWU : (W : Set M) ⊆ U := (flattenedSupportNeighborhood_subset_source E c e x hx).trans hsU
  have hgU : ∀ v ∈ U₀, ∃ h : e.symm (a, v) ∈ U, g v = f ⟨_, h⟩ := fun v hv =>
    ⟨hWU hv.2, by
      change (if h : e.symm (a, v) ∈ U then f ⟨_, h⟩ else 0) = _
      rw [dite_eq_left_of_eq_true (eq_true (show e.symm (a, v) ∈ U from hWU hv.2))]⟩
  have hgc : ContinuousOn g U₀ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : U₀.domRestrict g = fun v : U₀ => f ⟨e.symm (a, v.1), hWU v.2.2⟩ := by
      funext v
      exact (hgU v.1 v.2).2
    rw [this]
    refine f.continuous.comp (Continuous.subtype_mk ?_ _)
    exact e.continuousOn_symm.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun v => v.2.1)
  have hg0 : g 0 = 0 := by
    obtain ⟨h, hg⟩ := hgU 0 h0U
    rw [hg]
    apply (hf _).mpr
    change e.symm (a, 0) ∈ S
    rw [← hex, e.left_inv hx]
    exact (hS x hx).mpr h0
  let A := complexMatrixOfContinuousLinearMap c L
  have hA := complexMatrixOfContinuousLinearMap_det_ne_zero c L hL
  have hAL : (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) = L :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec c L)
  obtain ⟨V, hV, hne, hVo, h0V, hclass⟩ :=
    exists_open_complexDifferentiable_localClass_invariance c A hA U₀ hU₀ h0U g hgc hg0
      (hAL ▸ hd)
  have hfiber : ∀ v ∈ V, (a, v) ∈ e.target ∧ e.symm (a, v) ∈ W := fun _ hv => hV hv
  let F := chartNormalFiberPair c e S hS a W V hfiber
  obtain ⟨z, hz⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * c)).2 (standardComplexLocalClass ℚ c)
  have hFz : relativeHomologyMap ℚ (2 * c) F z =
      flattenedSupportNormalClass E c e x hx S hS h0 := by
    apply chartNormalProjection_relativeHomologyMap_injective E c e S hS x hx h0
    rw [chartNormalProjection_normalClass, ← LinearMap.comp_apply, ← relativeHomologyMap_comp]
    change relativeHomologyMap ℚ (2 * c)
      (chartNormalFiberPair c e S hS a W V hfiber ≫ chartNormalProjectionPair E c e S hS W _) z = _
    rw [chartNormalFiber_comp_projection]
    exact hz
  have hcomp : F ≫ neighborhoodSupportInclusionPairMap hWU S ≫
      hc9k_normalCoordinatePair U S c f (fun u => (hf u).mp) =
      complexNeighborhoodPuncturedPairMapOf c V g (hgc.mono hV) hne := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      apply Subtype.ext
      exact ((hgU v.1.1 (hV v.1.2)).2).symm
    · ext v
      exact ((hgU v.1 (hV v.2)).2).symm
  apply chartNormalProjectionCoclass_unique E c e S hS x hx h0
  have hpull : relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hWU S)
      (relativeCohomologyMap ℚ (2 * c)
        (hc9k_normalCoordinatePair U S c f (fun u => (hf u).mp)) (normalizedPointCoclass c)) =
      relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hWU S ≫
        hc9k_normalCoordinatePair U S c f (fun u => (hf u).mp)) (normalizedPointCoclass c) := by
    rw [relativeCohomologyMap_comp]
    rfl
  rw [hpull, ← hFz, relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    ← LinearMap.comp_apply (relativeHomologyMap ℚ (2 * c) _), ← relativeHomologyMap_comp, hcomp,
    hclass z hz]
  change relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ c) (2 * c)
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ c)
      (standardComplexLocalClass_ne_zero_for_chart c)) (standardComplexLocalClass ℚ c) = 1
  rw [relativeCohomologyEquivDualHomology_normalizedRelativeCoclass, normalizedDual_apply_self]



/-- On an open avoiding the next singular stratum, supported sections of the singular filtration
have no cohomology below `2(p+1)`. -/
theorem hc9k_singularLayer_homology_isZero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p) (k : ℕ) (V : Opens (ComplexPoint X))
    (hV : V ≤ (cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentSingularAnalyticClosedFiltration X x k).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy W hyW =>
      cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x hx k j (hj.trans_lt hn) y (hV hy) W hyW

/-- Relative Ext of an open and its part off a closed set, as supported section cohomology.
Source: `TopCat.Sheaf.relHAddEquivSupportedSectionsHomology`. -/
def hc9k_relHOnOpenEquiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (Z : Closeds (ComplexPoint X)) (V W : Opens (ComplexPoint X)) (hW : V ⊓ Z.compl = W)
    (n : ℕ) :=
  @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    (TopCat.of (ComplexPoint X)) Z.compl V W hW inferInstance
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n

/-- Purity along the singular filtration on an arbitrary open. -/
theorem hc9k_singularFiltration_relH_subsingleton
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p) (n : ℕ) (hn : n < 2 * (p + 1))
    (k : ℕ) (hk : k ≤ cycleComponentSingularFiltrationLength X x) (V : Opens (ComplexPoint X)) :
    Subsingleton (CategoryTheory.Sheaf.relH
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n
      (homOfLE (show (cycleComponentSingularAnalyticClosedFiltration X x k).compl ⊓ V ≤ V
        from inf_le_right))) := by
  let T := TopCat.of (ComplexPoint X)
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let Φ := cycleComponentSingularAnalyticClosedFiltration X x
  induction hk using Nat.decreasingInduction generalizing V with
  | self =>
    let e := hc9k_relHOnOpenEquiv X (Φ (cycleComponentSingularFiltrationLength X x)) V
      ((Φ (cycleComponentSingularFiltrationLength X x)).compl ⊓ V) (inf_comm _ _) n
    refine @Function.Injective.subsingleton _ _ _ e.injective ?_
    apply AddCommGrpCat.subsingleton_of_isZero
    have hN : (Φ (cycleComponentSingularFiltrationLength X x)).compl = ⊤ := by
      have h := cycleComponentSingularAnalyticClosedFiltration_length X x
      ext y
      change y ∉ Φ (cycleComponentSingularFiltrationLength X x) ↔ y ∈ Set.univ
      change y ∉ cycleComponentSingularAnalyticClosedFiltration X x
        (cycleComponentSingularStratification X x).length ↔ y ∈ Set.univ
      rw [h]
      exact iff_of_true (fun hy => hy) trivial
    change IsZero ((((TopCat.Sheaf.supportEvaluation T V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((TopCat.Sheaf.sheafSectionsSupportedOutside T
        (Φ (cycleComponentSingularFiltrationLength X x)).compl).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (ambientRationalInjectiveComplex X))).homology n)
    rw [hN]
    exact TopCat.Sheaf.supportedSections_top_homology_isZero T V _ n
  | of_succ k hk ih =>
    let f : (Φ k).compl ⊓ V ⟶ (Φ (k + 1)).compl ⊓ V :=
      homOfLE (inf_le_inf_right V fun y hy hy' =>
        hy (cycleComponentSingularAnalyticClosedFiltration_antitone X x (Nat.le_succ k) hy'))
    let g : (Φ (k + 1)).compl ⊓ V ⟶ V := homOfLE inf_le_right
    have hlayer : Subsingleton (CategoryTheory.Sheaf.relH F n f) := by
      have hW : ((Φ (k + 1)).compl ⊓ V) ⊓ (Φ k).compl = (Φ k).compl ⊓ V := by
        apply le_antisymm
        · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
        · exact le_inf (leOfHom f) inf_le_left
      let e := hc9k_relHOnOpenEquiv X (Φ k) ((Φ (k + 1)).compl ⊓ V) ((Φ k).compl ⊓ V) hW n
      refine @Function.Injective.subsingleton _ _ _ e.injective ?_
      apply AddCommGrpCat.subsingleton_of_isZero
      exact hc9k_singularLayer_homology_isZero X x p hx k _ inf_le_left n (by omega)
    exact ccm5_relH_nested_middle_subsingleton T F f g n (ih V) hlayer

set_option maxRecDepth 4096 in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction from an open to its part off a closed subset `B` of the support is injective in
any degree where relative Ext of the open off `B` vanishes. -/
theorem hc9k_restrict_injective_of_relH
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S B : Closeds (ComplexPoint X)) (hBS : B ≤ S) (U : Opens (ComplexPoint X)) (n : ℕ)
    (hvan : Subsingleton (CategoryTheory.Sheaf.relH
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n
      (homOfLE (show B.compl ⊓ U ≤ U from inf_le_right)))) :
    Function.Injective (relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap
        (show ((B.compl ⊓ U : Opens (ComplexPoint X)) : Set (ComplexPoint X)) ⊆ U from
          fun _ h => h.2) (S : Set (ComplexPoint X)))) := by
  let T := TopCat.of (ComplexPoint X)
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let U' := B.compl ⊓ U
  have hU'U : U' ≤ U := inf_le_right
  have hSB : S.compl ≤ B.compl := fun y hy hyB => hy (hBS hyB)
  have hW' : U' ⊓ S.compl = S.compl ⊓ U := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans hSB) inf_le_right) inf_le_left
  have := ambientRationalInjectiveComplex_isKInjective X
  have := ambientRationalInjectiveSingleAugmentation_quasiIso X
  let EU := ccm5_supportedSingularClassOnOpen X S U n
  let E' := (hc9k_relHOnOpenEquiv X S U' (S.compl ⊓ U) hW' n).trans
    (complexSupportInjectiveSectionCohomologyEquiv X S U' n)
  let f : S.compl ⊓ U ⟶ U' := homOfLE (le_inf (inf_le_left.trans hSB) inf_le_right)
  let g : U' ⟶ U := homOfLE hU'U
  let r := CategoryTheory.Sheaf.relH.restrict F (f ≫ g) f (𝟙 _) g (by simp) n
  have hnat : ∀ z, E' (r z) = relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap
        (show ((B.compl ⊓ U : Opens (ComplexPoint X)) : Set (ComplexPoint X)) ⊆ U from
          fun _ h => h.2) (S : Set (ComplexPoint X))) (EU z) := by
    intro z
    have h := TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_restrict T
      (inf_comm U S.compl) hW' (le_refl S.compl) hU'U (le_refl (S.compl ⊓ U)) F
      (ambientRationalInjectiveComplex X) (ambientRationalInjectiveSingleAugmentation X) n z
    rw [TopCat.Sheaf.supportedSectionsRestriction_refl] at h
    dsimp only [E', EU, ccm5_supportedSingularClassOnOpen, AddEquiv.trans_apply,
      hc9k_relHOnOpenEquiv]
    exact (congrArg (complexSupportInjectiveSectionCohomologyEquiv X S U' n) h).trans
      (ccm5_injectiveSectionEquiv_restrict X S (U := U') (V := U) hU'U n _)
  have hmono : Function.Injective r := by
    let Sq := Abelian.Ext.contravariantSequence
      (CategoryTheory.Sheaf.pairNestedShortComplex_shortExact (J := Opens.grothendieckTopology T)
        f g) F n (n + 1) (by omega)
    have hS := CategoryTheory.Sheaf.relH.nestedSequence_exact F f g n (n + 1) (by omega)
    let q := AddCommGrpCat.ofHom r
    have hq : Mono q := by
      change Mono (Sq.map' 1 2 (by omega) (by omega))
      exact (hS.exact 0).mono_g
        ((@AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
          (CategoryTheory.Sheaf.relH F n g)) hvan).eq_zero_of_src _)
    exact (AddCommGrpCat.mono_iff_injective q).mp hq
  intro α β hαβ
  apply EU.symm.injective
  apply hmono
  apply E'.injective
  rw [hnat, hnat, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact hαβ

/-- Off the singular locus, lowest-degree classes supported on a component are determined by
their germs. -/
theorem hc9k_germs_injective_offSingular
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p) (V : Opens (ComplexPoint X))
    (hV : V ≤ cycleComponentSmoothSupportAmbientOpen X x) :
    Function.Injective (fun z => fun a : V =>
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)) (2 * p) V a.1 a.2 z) := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  apply ccm5_relativeGerms_injective_of_lowerVanishing (TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X x) V (2 * p)
  intro j hj
  have hI : IsZero ((((V.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (j : ℤ)) := by
    apply TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    intro a ha W haW
    exact cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
      X x hx j (by omega) a (hV ha) W haW
  exact IsZero.of_iso hI
    (complexSupportInjectiveCohomologySheafIsoRelative_restrict X
      (cycleComponentAnalyticClosedSupport X x) V j).symm

/-- Two neighborhood restrictions compose to one. -/
theorem hc9k_restrict_restrict {M : Type} [TopologicalSpace M] {W V U : Set M} (h1 : W ⊆ V)
    (h2 : V ⊆ U) (S : Set M) (n : ℕ)
    (z : RelativeCohomology ℚ (neighborhoodSupportComplementPair U S) n) :
    relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap h1 S)
        (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap h2 S) z) =
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap (h1.trans h2) S) z := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusionPairMap_comp]

/-- The singular locus of a component lies on its support. -/
theorem hc9k_singularFiltration_zero_le_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    cycleComponentSingularAnalyticClosedFiltration X x 0 ≤
      cycleComponentAnalyticClosedSupport X x := by
  intro y hy
  obtain ⟨z, _, hz⟩ := hy
  change y.underlying ∈ closure ({x} : Set X.left)
  rw [← range_cycleComponentι X.left x]
  exact ⟨z, hz⟩

/-- On a holomorphic normal chart, the supported prime class restricts to the pullback of the
normalized class along the normal map.
Source: SGA 1, Exposé XII, 3.1; Bott--Tu, *Differential Forms in Algebraic Topology*, §6. -/
theorem hc9k_prime_supportedClass_chart_of_charts
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (x : X.left) (hx : Order.coheight x = p)
    (U : Opens (ComplexPoint X)) (f : C(U, Fin p → ℂ))
    (hzero : ∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x)
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f)
    (hsub : ∀ u : U, f u = 0 →
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u)) :
    relativeCohomologyMap ℚ (2 * p)
        (neighborhoodSupportInclusionPairMap
          (show (U : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
          (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))
        (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) (2 * p)
          (cycleComponentSupportedInjectiveClass X x hx)) =
      relativeCohomologyMap ℚ (2 * p)
        (hc9k_normalCoordinatePair U (cycleComponentAnalyticClosedSupport X x) p f
          (fun u => (hzero u).mp))
        (normalizedPointCoclass p) := by
  obtain rfl : dim X.left = d := SmoothOfRelativeDimension.dim_eq X.hom d
  let S := cycleComponentAnalyticClosedSupport X x
  let B := cycleComponentSingularAnalyticClosedFiltration X x 0
  let U' : Opens (ComplexPoint X) := B.compl ⊓ U
  have hU'U : (U' : Set (ComplexPoint X)) ⊆ U := fun _ h => h.2
  apply hc9k_restrict_injective_of_relH X S B (hc9k_singularFiltration_zero_le_support X x) U
    (2 * p) (hc9k_singularFiltration_relH_subsingleton X x p hx (2 * p) (by omega) 0
      (Nat.zero_le _) U)
  apply hc9k_germs_injective_offSingular X x p hx U' inf_le_left
  funext ⟨a, haU'⟩
  dsimp only
  by_cases haS : a ∈ S
  · obtain ⟨e, he, hae, heA, heI, W, haW, hWe, hW⟩ :=
      hc9k_cc_componentClass_restrict_normalChart X p x hx a haU'.1 haS
    let O : Opens (ComplexPoint X) := U' ⊓ W
    let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
    have he' : ∀ y ∈ e'.source, y ∈ cycleComponentSupport X x ↔ (e' y).2 = 0 :=
      fun y hy => he y hy.1
    have hsO : e'.source ⊆ O := fun _ hy => hy.2
    have hsU : e'.source ⊆ U := fun _ hy => hU'U (hsO hy).1
    have haU : a ∈ U := haU'.2
    have hae' : a ∈ e'.source := ⟨hae, haU', haW⟩
    have ha0 : (e' a).2 = 0 := (he a hae).mp haS
    obtain ⟨L, hL, hd⟩ := hc9k_sliceNormalMap_hasFDerivAt U S f hzero hhol e' he' a haU hae'
      ha0 heA heI (hsub ⟨a, haU⟩ ((hzero _).mpr haS))
    have hpull := hc9k_normalMap_pullback_eq_chartCoclass p U S f hzero e' he' hsU a hae' ha0
      L hL hd
    let N := flattenedSupportNeighborhood (Fin (dim X.left - p) → ℂ) p e' a hae'
    have hNs : (N : Set (ComplexPoint X)) ⊆ e'.source :=
      flattenedSupportNeighborhood_subset_source _ p e' a hae'
    have hNU' : N ≤ U' := fun _ h => (hsO (hNs h)).1
    have hNW : (N : Set (ComplexPoint X)) ⊆ W := fun _ h => (hsO (hNs h)).2
    refine supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) (2 * p) (W := N) hNU' hNU' a
      (mem_flattenedSupportNeighborhood _ p e' a hae') _ _ ?_
    rw [hc9k_restrict_restrict, hc9k_restrict_restrict, hc9k_restrict_restrict]
    have hL1 := congrArg (relativeCohomologyMap ℚ (2 * p)
      (neighborhoodSupportInclusionPairMap hNW (cycleComponentSupport X x))) hW
    rw [hc9k_restrict_restrict, chartNormalProjectionCoclass_restrict] at hL1
    rw [← hc9k_restrict_restrict (hNU'.trans hU'U) (le_refl _)] at hpull
    exact hL1.trans (hpull.symm.trans (by rw [hc9k_restrict_restrict]))
  · rw [supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _ S.isClosed _ _ _ haS,
      supportRelativeCohomologyGerm_eq_zero_of_not_mem _ _ _ S.isClosed _ _ _ haS]

end HodgeLean.Adapters
