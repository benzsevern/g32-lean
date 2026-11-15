import HodgeLean.Adapters.CycleClassSmoothCharts

/-! # Component normalization in an anchored normal chart

Implication from a smooth point of an actual cycle component to local normalization.
The exponential-cover transport and regular-domain gluing are separate steps.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- The actual component class restricts to its complex normal-chart coclass near the anchor.
Source: `cycleComponentSupportedInjectiveClass_normalization` and
CycleClassSmoothChartsProofs, the smooth closed-lift chart and germ construction. -/
private theorem bh11_supportOpenIso_toSheaf
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
private theorem bh11_smoothClosedSupportCoclass_restrict_chart
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
private theorem bh11_smoothClosedSupportCoclass_openImage_chart
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
    (NatTrans.congr_app (bh11_supportOpenIso_toSheaf f hf S
      (Set.range (Point.map i)) hS (2 * (d - m)))
      (Opposite.op (smoothClosedSupportChartOpen X Y i m d z)))
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))
  change _ = _ at hn
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    bh11_smoothClosedSupportCoclass_restrict_chart] at hn
  exact hn.symm.trans hu


set_option backward.isDefEq.respectTransparency false in
private theorem bh11_smoothClosedSupportCoclass_transported_germ
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
  rw [bh11_smoothClosedSupportCoclass_openImage_chart] at h
  exact h.symm


set_option backward.isDefEq.respectTransparency false in
private theorem bh11_chartNormalProjectionCoclass_pullback
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

private theorem bh11_chartNormalProjectionCoclass_openImage
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
  apply bh11_chartNormalProjectionCoclass_pullback
  intro y
  change (e.lift_openEmbedding hf (f y.1)).2 = (e y.1).2
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]


private theorem bh11_product_normal_chart
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
private theorem bh11_smoothClosedSupportCoclass_ambient_chart
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
  have h := bh11_smoothClosedSupportCoclass_transported_germ X Y i m d z f hf S hS U hU
  convert h using 1
  congr 1
  exact (bh11_chartNormalProjectionCoclass_openImage (d - m) f hf e₀
    (Set.range (Point.map i)) S hS
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) he
    e₀.source (le_refl _)).symm
private theorem bh11_component_smoothLift_point
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
private theorem bh11_openEmbedding_chart_analytic
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
private theorem bh11_lifted_flatteningChart_analytic
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
  have ht := bh11_openEmbedding_chart_analytic O X j d hj b
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
private theorem bh11_componentClass_germ_exists_normalChart
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
  obtain ⟨z, rfl⟩ := bh11_component_smoothLift_point X x a ha haS
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have h := bh11_smoothClosedSupportCoclass_ambient_chart
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
  have hA := bh11_lifted_flatteningChart_analytic
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
private theorem bh11_supportGerm_exists_restrict_eq
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
theorem bh11_component_normal_chart_aux
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
  obtain ⟨e, he, hae, hg, heA, heI⟩ :=
    bh11_componentClass_germ_exists_normalChart X q x hx a ha haS
  obtain ⟨W, haW, hWU, hWV, hW⟩ :=
    bh11_supportGerm_exists_restrict_eq (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * q) a
      (show a ∈ (⊤ : Opens (ComplexPoint X)) from trivial) hae _ _ hg
  refine ⟨e, he, hae, heA, heI, W, haW, hWV, ?_⟩
  exact hW.trans (chartNormalProjectionCoclass_restrict
    (Fin (dim X.left - q) → ℂ) q e (cycleComponentSupport X x) he hWV (le_refl _))

end HodgeLean.Adapters
