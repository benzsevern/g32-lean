import HodgeLean.Adapters.CycleClassSmoothCharts
import HodgeLean.Foundations.Port.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-! # Generic-germ detection for finite component unions

Boundary vanishing and excision restrict a lowest-degree supported class of a finite union of
equal-codimension components to the complement of the component boundary, where lower local
vanishing makes it a section determined by its germs.
-/

noncomputable section
set_option maxHeartbeats 400000
-- Germ maps unfold through `supportH` instances, which needs defeq past instance transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs AlgebraicTopology.Singular TopologicalSpace

namespace HodgeLean.Adapters

/-- Germs at the points off the component boundary determine a lowest-degree class supported on
a finite union of distinct components of equal codimension. -/
theorem hc9k_componentUnion_goodOpen_germs_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (y : Fin r → X.left) (hy : Function.Injective y)
    (hc : ∀ i, Order.coheight (y i) = q)
    (u v : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (⨆ i, cycleComponentAnalyticClosedSupport X (y i))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) (2 * q))
    (h : ∀ a ∈ (ccm5_componentBoundary X r y).compl,
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) a u =
        ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) a v) :
    u = v := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  let S : Closeds (ComplexPoint X) := ⨆ i, cycleComponentAnalyticClosedSupport X (y i)
  let U := (ccm5_componentBoundary X r y).compl
  apply (ccm5_componentRestriction_bijective_aux X r q y hy hc).1
  change ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) S U (2 * q) u =
    ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) S U (2 * q) v
  apply (ccm5_supportedSingularClassOnOpen X S U (2 * q)).injective
  apply ccm5_relativeGerms_injective_of_lowerVanishing (TopCat.of (ComplexPoint X)) S U (2 * q)
    (fun j hj => ccm5_componentUnion_lowerSheaf_vanishing X r q y hc j hj)
  funext a
  exact (ccm5_supportGerm_via_openRestriction X S U (2 * q) a.1 a.2 u).trans
    ((h a.1 a.2).trans
      (ccm5_supportGerm_via_openRestriction X S U (2 * q) a.1 a.2 v).symm)

/-- A vanishing sheaf germ of a relative class vanishes after restriction to a neighborhood. -/
theorem hc9k_supportGerm_eq_zero_exists_restrict
    (T : TopCat.{0}) (S : Set T) (n : ℕ) {V : Opens T} (x : T) (hxV : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set T) S) n)
    (h : supportRelativeCohomologyGerm T S n V x hxV a = 0) :
    ∃ (W : Opens T) (_hxW : x ∈ W) (hWV : W ≤ V),
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWV S) a = 0 := by
  let P := supportRelativeCohomologyPresheaf T S n
  let η := supportRelativeCohomologyToSheaf T S n
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  have h' : P.germ V x hxV a = P.germ V x hxV 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).1
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change supportRelativeCohomologyGerm T S n V x hxV a = _
    rw [h, map_zero, map_zero]
  obtain ⟨W, hxW, iU, iV, he⟩ := P.germ_eq x hxV hxV a 0 h'
  refine ⟨W, hxW, leOfHom iU, ?_⟩
  have he' : relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap (leOfHom iU) S) a =
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap (leOfHom iV) S) 0 := he
  rw [he', map_zero]

/-- In a support-flattening chart, a top-normal-degree class whose germ vanishes at one support
point of the flattened neighborhood vanishes on that neighborhood. -/
theorem hc9k_flattened_restrict_eq_zero_of_germ
    {M : Type} [TopologicalSpace M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (b : M) (hb : b ∈ e.source)
    (hb0 : (e b).2 = 0)
    (α : RelativeCohomology ℚ (neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood E c e b hb : Set M) S) (2 * c))
    (z : M) (hz : z ∈ flattenedSupportNeighborhood E c e b hb) (hzS : z ∈ S)
    (h : supportRelativeCohomologyGerm (TopCat.of M) S (2 * c) (flattenedSupportNeighborhood E c e b hb)
      z hz α = 0) :
    α = 0 := by
  let N := flattenedSupportNeighborhood E c e b hb
  have hNe : (N : Set M) ⊆ e.source := flattenedSupportNeighborhood_subset_source E c e b hb
  obtain ⟨W, hzW, hWN, hW⟩ := hc9k_supportGerm_eq_zero_exists_restrict (TopCat.of M) S (2 * c) z hz α h
  let e' := e.restrOpen (W : Set M) W.isOpen
  have he'S : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0 := fun y hy => hS y hy.1
  have hze' : z ∈ e'.source := ⟨hNe hz, hzW⟩
  have hz0 : (e' z).2 = 0 := (hS z (hNe hz)).mp hzS
  let N' := flattenedSupportNeighborhood E c e' z hze'
  have hN'W : (N' : Set M) ⊆ W := fun y hy =>
    (flattenedSupportNeighborhood_subset_source E c e' z hze' hy).2
  have hN'N : (N' : Set M) ⊆ N := fun y hy => hWN (hN'W hy)
  let ι := neighborhoodSupportInclusionPairMap hN'N S
  let n := flattenedSupportNormalClass E c e b hb S hS hb0
  let n' := flattenedSupportNormalClass E c e' z hze' S he'S hz0
  have hproj : ι ≫ chartNormalProjectionPair E c e S hS N hNe =
      chartNormalProjectionPair E c e' S he'S N'
        (flattenedSupportNeighborhood_subset_source E c e' z hze') := rfl
  have hιn : relativeHomologyMap ℚ (2 * c) ι n' = n := by
    apply chartNormalProjection_relativeHomologyMap_injective E c e S hS b hb hb0
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hproj,
      chartNormalProjection_normalClass E c e' S he'S z hze' hz0,
      chartNormalProjection_normalClass E c e S hS b hb hb0]
  have hres : relativeCohomologyMap ℚ (2 * c) ι α = 0 := by
    have hcomp : ι = neighborhoodSupportInclusionPairMap hN'W S ≫
        neighborhoodSupportInclusionPairMap hWN S := rfl
    rw [hcomp, relativeCohomologyMap_comp, LinearMap.comp_apply, hW, map_zero]
  have hval : relativeCohomologyEquivDualHomology ℚ
      (neighborhoodSupportComplementPair (N : Set M) S) (2 * c) α n = 0 := by
    rw [← hιn, ← relativeCohomologyEquivDualHomology_relativeCohomologyMap, hres, map_zero,
      LinearMap.zero_apply]
  apply (relativeCohomologyEquivDualHomology ℚ
    (neighborhoodSupportComplementPair (N : Set M) S) (2 * c)).injective
  rw [map_zero]
  apply LinearMap.ext
  intro w
  have hw : w ∈ Submodule.span ℚ {n} := by
    rw [span_flattenedSupportNormalClass_eq_top E c e S hS b hb hb0]
    trivial
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, hval, smul_zero, LinearMap.zero_apply]

/-- Every smooth point of a component support has an ambient chart flattening that support. -/
theorem hc9k_component_flatteningChart
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)),
      (∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0) ∧ a ∈ e.source := by
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
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  let f := cycleComponentSmoothClosedLiftAmbientMap X x
  have hf := cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x
  let e₀ := closedImmersionHolomorphicFlatteningChart
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - q) (dim X.left) z
  let e := e₀.lift_openEmbedding hf
  have he : ∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    change f y ∈ cycleComponentSupport X x ↔ (e₀.lift_openEmbedding hf (f y)).2 = 0
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change y ∈ f ⁻¹' cycleComponentSupport X x ↔ _
    rw [cycleComponentSmoothClosedLiftAmbientMap_support]
    exact closedImmersionHolomorphicFlatteningChart_mem_range_iff _ _ _ _ _ z y hy
  have hae : f (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) ∈ e.source :=
    ⟨_, mem_smoothClosedSupportChartOpen _ _ _ _ _ z, rfl⟩
  have hcod := cycleComponentSmoothClosedLift_codimension X x hx
  have key : ∀ (c : ℕ), c = q → ∀ e : OpenPartialHomeomorph (ComplexPoint X)
      ((Fin (dim X.left - q) → ℂ) × (Fin c → ℂ)),
      (∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0) →
      f (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) ∈ e.source →
      ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)),
      (∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0) ∧
        f (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) ∈ e.source := by
    rintro c rfl e he hae
    exact ⟨e, he, hae⟩
  exact key _ hcod e he hae

/-- Membership in the component boundary: a singular stratum or two distinct components. -/
theorem hc9k_mem_componentBoundary
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (y : Fin r → X.left) (c : ComplexPoint X) :
    c ∈ ccm5_componentBoundary X r y ↔
      (∃ i, c ∈ cycleComponentSingularAnalyticClosedFiltration X (y i) 0) ∨
        ∃ i k, i ≠ k ∧ c ∈ cycleComponentAnalyticClosedSupport X (y i) ∧
          c ∈ cycleComponentAnalyticClosedSupport X (y k) := by
  classical
  unfold ccm5_componentBoundary
  change c ∈ ((_ ⊔ _ : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) ↔ _
  rw [Closeds.coe_sup, Set.mem_union]
  apply or_congr (ccm5_mem_finiteClosedSup _ c)
  rw [SetLike.mem_coe, ccm5_mem_finiteClosedSup]
  apply exists_congr
  intro i
  rw [ccm5_mem_finiteClosedSup]
  apply exists_congr
  intro k
  split_ifs with hik
  · simp only [hik, ne_eq, not_true_eq_false, false_and, iff_false]
    intro h
    exact h
  · change c ∈ ((_ ⊓ _ : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) ↔ _
    rw [Closeds.coe_inf]
    exact ⟨fun h => ⟨hik, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-- The singular stratum of a component lies in its support. -/
theorem hc9k_singular_mem_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (c : ComplexPoint X)
    (hc : c ∈ cycleComponentSingularAnalyticClosedFiltration X x 0) :
    c ∈ cycleComponentAnalyticClosedSupport X x := by
  obtain ⟨w, _, hw⟩ := hc
  change c.underlying ∈ closure ({x} : Set X.left)
  rw [← range_cycleComponentι]
  exact ⟨w, hw⟩

/-- Off the boundary, each component support is the image of the complex points of a nonempty
open subscheme of its smooth locus, hence preconnected. -/
theorem hc9k_goodOpen_component_isPreconnected
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (y : Fin r → X.left) (hc : ∀ i, Order.coheight (y i) = q) (j : Fin r) :
    IsPreconnected (((ccm5_componentBoundary X r y).compl : Set (ComplexPoint X)) ∩
      (cycleComponentAnalyticClosedSupport X (y j) : Set (ComplexPoint X))) := by
  classical
  let Z := cycleComponentSmoothLocusOver X (y j)
  let G : Z ⟶ X := Over.homMk
    ((cycleComponentι X.left (y j) ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left (y j)) rfl
  let C : Closeds X.left :=
    ⨆ k : {k : Fin r // k ≠ j}, ⟨closure {y k.1}, isClosed_closure⟩
  let O' : Z.left.Opens := G.left ⁻¹ᵁ C.compl
  let Y := openScheme Z O'
  let Φ : Y ⟶ X := openInclusion Z O' ≫ G
  have hGamb : ∀ z : ComplexPoint Z, Point.map G z =
      cycleComponentSmoothClosedLiftAmbientMap X (y j)
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X (y j)) z) := by
    intro z
    change z ≫ G = (z ≫ cycleComponentSmoothLocusClosedLiftOver X (y j)) ≫
      openInclusion X (cycleComponentSmoothLocusAmbientOpen X (y j))
    rw [Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    exact (cycleComponentSmoothLocusClosedLift_ι X (y j)).symm
  have hsmooth : ∀ z : ComplexPoint Z,
      Point.map G z ∈ cycleComponentSmoothSupportAmbientOpen X (y j) := by
    intro z
    rw [hGamb, ← cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact ⟨_, trivial, rfl⟩
  have hsupp : ∀ z : ComplexPoint Z,
      Point.map G z ∈ cycleComponentAnalyticClosedSupport X (y j) := by
    intro z
    change (Point.map G z).underlying ∈ closure ({y j} : Set X.left)
    rw [Point.underlying_map, ← range_cycleComponentι]
    exact ⟨_, rfl⟩
  have hlift : ∀ c ∈ cycleComponentSmoothSupportAmbientOpen X (y j),
      c ∈ cycleComponentAnalyticClosedSupport X (y j) → ∃ z, Point.map G z = c := by
    intro c hcU hcS
    have hrange : c ∈ Set.range (cycleComponentSmoothClosedLiftAmbientMap X (y j)) := by
      rw [← Set.image_univ]
      change c ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X (y j)).functor.obj ⊤
      rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
      exact hcU
    obtain ⟨b, rfl⟩ := hrange
    have hb : b ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X (y j))) := by
      rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
      exact hcS
    obtain ⟨z, rfl⟩ := hb
    exact ⟨z, hGamb z⟩
  have hO : ∀ z : ComplexPoint Z, z ∈ Point.overOpen O' ↔
      ∀ k, k ≠ j → Point.map G z ∉ cycleComponentAnalyticClosedSupport X (y k) := by
    intro z
    change G.left z.underlying ∈ (C.compl : Set X.left) ↔ _
    change G.left z.underlying ∉ (C : Set X.left) ↔ _
    rw [SetLike.mem_coe, ccm5_mem_finiteClosedSup]
    constructor
    · intro h k hk hz
      exact h ⟨⟨k, hk⟩, hz⟩
    · rintro h ⟨k, hz⟩
      exact h k.1 k.2 hz
  have key : ((ccm5_componentBoundary X r y).compl : Set (ComplexPoint X)) ∩
      (cycleComponentAnalyticClosedSupport X (y j) : Set (ComplexPoint X)) =
      Set.range (Point.map Φ) := by
    ext c
    constructor
    · rintro ⟨hcB, hcS⟩
      have hcU : c ∈ cycleComponentSmoothSupportAmbientOpen X (y j) := fun hs =>
        hcB ((hc9k_mem_componentBoundary X r y c).mpr (Or.inl ⟨j, hs⟩))
      obtain ⟨z, rfl⟩ := hlift c hcU hcS
      have hz : z ∈ Point.overOpen O' := by
        rw [hO]
        intro k hk hzk
        exact hcB ((hc9k_mem_componentBoundary X r y _).mpr
          (Or.inr ⟨j, k, hk.symm, hcS, hzk⟩))
      refine ⟨asOpenPoint Z O' z hz, ?_⟩
      change Point.map G (Point.map (openInclusion Z O') (asOpenPoint Z O' z hz)) = _
      congr 1
      exact congrArg Subtype.val ((openEquiv Z O').apply_symm_apply ⟨z, hz⟩)
    · rintro ⟨p, rfl⟩
      let z := Point.map (openInclusion Z O') p
      have hz : z ∈ Point.overOpen O' := ((openEquiv Z O') p).2
      have hzO := (hO z).mp hz
      change Point.map G z ∈ _
      refine ⟨fun hB => ?_, hsupp z⟩
      rcases (hc9k_mem_componentBoundary X r y _).mp hB with ⟨i, hi⟩ | ⟨i, k, hik, hi, hk⟩
      · by_cases hij : i = j
        · subst hij
          exact hsmooth z hi
        · exact hzO i hij (hc9k_singular_mem_support X (y i) _ hi)
      · by_cases hij : i = j
        · subst hij
          exact hzO k (Ne.symm hik) hk
        · exact hzO i hij hi
  rw [key]
  rcases isEmpty_or_nonempty (ComplexPoint Y) with hY | hY
  · rw [Set.range_eq_empty]
    exact isPreconnected_empty
  obtain ⟨p⟩ := hY
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X (y j) (hc j)
  have : Nonempty Y.left := ⟨p.underlying⟩
  have : IsIntegral Y.left :=
    isIntegral_of_isOpenImmersion (O'.ι ≫ (cycleComponentι X.left (y j) ≫ X.hom).smoothLocus.ι)
  have : Smooth Y.hom := by
    have : Smooth Z.hom := SmoothOfRelativeDimension.smooth (dim X.left - q) Z.hom
    change Smooth (O'.ι ≫ Z.hom)
    infer_instance
  have : QuasiSeparatedSpace Y.left := by
    have : QuasiSeparated Y.hom := by
      change QuasiSeparated (O'.ι ≫ ((cycleComponentι X.left (y j) ≫ X.hom).smoothLocus.ι ≫
        cycleComponentι X.left (y j)) ≫ X.hom)
      infer_instance
    exact quasiSeparatedSpace_of_quasiSeparated Y.hom
  have := ComplexPoint.connectedSpace Y
  exact isPreconnected_range (Point.continuousMap Φ).continuous

/-- Near a boundary-free point of one component, a vanishing germ at any support point of a
flattened neighborhood forces the germ at the center to vanish. -/
theorem hc9k_componentUnion_germ_zero_near
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (y : Fin r → X.left) (hc : ∀ i, Order.coheight (y i) = q)
    (w : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (⨆ i, cycleComponentAnalyticClosedSupport X (y i))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) (2 * q))
    (j : Fin r) (b : ComplexPoint X) (hbB : b ∈ (ccm5_componentBoundary X r y).compl)
    (hbS : b ∈ cycleComponentAnalyticClosedSupport X (y j)) :
    ∃ W : Opens (ComplexPoint X), b ∈ W ∧ ∀ c ∈ W,
      c ∈ (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) →
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) c w = 0 →
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) b w = 0 := by
  have hbU : b ∈ cycleComponentSmoothSupportAmbientOpen X (y j) := fun hs =>
    hbB ((hc9k_mem_componentBoundary X r y b).mpr (Or.inl ⟨j, hs⟩))
  have hother : ∀ k, k ≠ j → b ∉ cycleComponentAnalyticClosedSupport X (y k) :=
    fun k hk hbk => hbB ((hc9k_mem_componentBoundary X r y b).mpr
      (Or.inr ⟨j, k, hk.symm, hbS, hbk⟩))
  obtain ⟨e, he, hbe⟩ := hc9k_component_flatteningChart X q (y j) (hc j) b hbU hbS
  obtain ⟨W₀, hW₀e, hbW₀, hW₀⟩ := ccm5_finiteSupport_local_eq
    (fun i => cycleComponentAnalyticClosedSupport X (y i)) j b hother
    ⟨e.source, e.open_source⟩ hbe
  generalize hS : (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) = S at w hW₀ ⊢
  let e' := e.restrOpen (W₀ : Set (ComplexPoint X)) W₀.isOpen
  have he' : ∀ z ∈ e'.source, z ∈ (S : Set (ComplexPoint X)) ↔ (e' z).2 = 0 :=
    fun z hz => (hW₀ z hz.2).trans (he z hz.1)
  have hbe' : b ∈ e'.source := ⟨hbe, hbW₀⟩
  have hb0 : (e' b).2 = 0 := (he b hbe).mp hbS
  let N := flattenedSupportNeighborhood (Fin (dim X.left - q) → ℂ) q e' b hbe'
  refine ⟨N, mem_flattenedSupportNeighborhood _ q e' b hbe', ?_⟩
  intro c hcN hcS hc0
  let α := relativeCohomologyMap ℚ (2 * q)
    (neighborhoodSupportInclusionPairMap
      (show (N : Set (ComplexPoint X)) ⊆ (⊤ : Opens (ComplexPoint X)) from le_top)
      (S : Set (ComplexPoint X)))
    (supportedSingularClass X S (2 * q) w)
  have h1 := ccm5_supportGerm_restriction X S N (2 * q) c hcN w
  have h2 : supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) (2 * q) N c hcN α = 0 := by
    rw [← hc0]
    exact h1
  have hα : α = 0 :=
    hc9k_flattened_restrict_eq_zero_of_germ q e'
      (S : Set (ComplexPoint X)) he' b hbe' hb0 α c hcN hcS h2
  have hbN := mem_flattenedSupportNeighborhood _ q e' b hbe'
  have h4 := ccm5_supportGerm_restriction X S N (2 * q) b hbN w
  have h5 : supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) (2 * q) N b hbN α = 0 := by
    rw [hα]
    simp only [supportRelativeCohomologyGerm, map_zero]
  exact h4.symm.trans h5

/-- A germ vanishing at one point of a boundary-free component piece vanishes along the piece,
by connectedness of the piece and local constancy of top normal-degree germs. -/
theorem hc9k_componentUnion_germ_zero_on_piece
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (y : Fin r → X.left) (hc : ∀ i, Order.coheight (y i) = q)
    (w : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (⨆ i, cycleComponentAnalyticClosedSupport X (y i))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) (2 * q))
    (j : Fin r) (a b : ComplexPoint X)
    (haB : a ∈ (ccm5_componentBoundary X r y).compl)
    (haS : a ∈ cycleComponentAnalyticClosedSupport X (y j))
    (ha0 : ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) a w = 0)
    (hbB : b ∈ (ccm5_componentBoundary X r y).compl)
    (hbS : b ∈ cycleComponentAnalyticClosedSupport X (y j)) :
    ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) b w = 0 := by
  by_contra hb0
  have hpre := hc9k_goodOpen_component_isPreconnected X r q y hc j
  have hu : IsOpen {c : ComplexPoint X |
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) c w = 0} := by
    rw [isOpen_iff_forall_mem_open]
    intro c hc0
    have hc0' := (ccm5_supportGerm_restriction X
      (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) ⊤ (2 * q) c trivial w).trans hc0
    obtain ⟨W, hcW, hWV, hW⟩ := hc9k_supportGerm_eq_zero_exists_restrict
      (TopCat.of (ComplexPoint X)) _ (2 * q) (V := ⊤) c trivial _ hc0'
    refine ⟨W, fun c' hc' => ?_, W.isOpen, hcW⟩
    have h4 := ccm5_supportGerm_restriction X
      (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) ⊤ (2 * q) c' trivial w
    rw [← supportRelativeCohomologyGerm_restrict _ _ _ hWV c' hc', hW] at h4
    show _ = 0
    rw [← h4]
    simp only [supportRelativeCohomologyGerm, map_zero]
  have hv : IsOpen {c : ComplexPoint X | ∃ W : Opens (ComplexPoint X), c ∈ W ∧ ∀ c' ∈ W,
      c' ∈ (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) →
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) c' w ≠ 0} := by
    rw [isOpen_iff_forall_mem_open]
    rintro c ⟨W, hcW, hW⟩
    exact ⟨W, fun c' hc' => ⟨W, hc', hW⟩, W.isOpen, hcW⟩
  have hnear : ∀ c, c ∈ (ccm5_componentBoundary X r y).compl →
      c ∈ cycleComponentAnalyticClosedSupport X (y j) →
      ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) c w ≠ 0 →
      ∃ W : Opens (ComplexPoint X), c ∈ W ∧ ∀ c' ∈ W,
        c' ∈ (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) →
        ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i)) (2 * q) c' w ≠
          0 := by
    intro c hcB hcS hc0
    obtain ⟨W, hcW, hW⟩ := hc9k_componentUnion_germ_zero_near X r q y hc w j c hcB hcS
    exact ⟨W, hcW, fun c' hc' hc'S h => hc0 (hW c' hc' hc'S h)⟩
  obtain ⟨c, hcs, hcu, W, hcW, hW⟩ := hpre _ _ hu hv
    (fun c hcs => by
      by_cases h : ccm5_supportGerm X (⨆ i, cycleComponentAnalyticClosedSupport X (y i))
          (2 * q) c w = 0
      · exact Or.inl h
      · exact Or.inr (hnear c hcs.1 hcs.2 h))
    ⟨a, ⟨haB, haS⟩, ha0⟩ ⟨b, ⟨hbB, hbS⟩, hnear b hbB hbS hb0⟩
  exact hW c hcW
    ((le_iSup (fun i => cycleComponentAnalyticClosedSupport X (y i)) j) hcs.2) hcu

end HodgeLean.Adapters
