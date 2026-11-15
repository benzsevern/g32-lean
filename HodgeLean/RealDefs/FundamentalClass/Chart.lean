import HodgeLean.RealDefs.DegreeZero
import HodgeLean.RealDefs.Port.OpenTransport

/-! # `[X] = 1`, layer 5: the chart coclass in normal dimension `0`

In normal dimension `c = 0` the normalized chart coclass needs no computation: every map of pairs
into `(ℂ⁰, ℂ⁰ \ {0})` is the same (`puncturedPair_hom_subsingleton`), so every chart coclass is the
restriction of one class, the full-support coclass (`fullSupportCoclass`, the pullback of the
normalized class along the collapse to the point). When the closed immersion is onto, the glued
coclass section is that class, sheafified
(`smoothClosedSupportCoclassSection_eq_fullSupportCoclass`). For a point of coheight `0` the lift
is onto, and transport to `X(ℂ)` gives
`cycleComponentSmoothSupportCoclassSection_eq_fullSupportCoclass`. -/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

section PointPair

/-- Every map of pairs into `(ℂ^c, ℂ^c \ {0})` is the same when `c = 0`. -/
lemma puncturedPair_hom_subsingleton (P : TopPair) (c : ℕ) (hc : c = 0) :
    Subsingleton (P ⟶ puncturedPair ℂ c) := by
  subst hc
  refine ⟨fun φ ψ => ?_⟩
  have h0 : ∀ v : Fin 0 → ℂ, v = 0 := fun v => funext (fun k => k.elim0)
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro a
    exact ((φ.left a).2 (h0 _)).elim
  · apply ConcreteCategory.hom_ext
    intro p
    exact (h0 _).trans (h0 _).symm

variable {M : Type} [TopologicalSpace M] (c : ℕ)

/-- The map of pairs `(W, W \ S) → (ℂ^c, ℂ^c \ {0})` collapsing `W` to `0`, for `W ⊆ S`. -/
noncomputable def toPuncturedPairOfSubset (W S : Set M) (hWS : W ⊆ S) :
    neighborhoodSupportComplementPair W S ⟶ puncturedPair ℂ c :=
  TopPair.ofSubsetHom (TopCat.ofHom (ContinuousMap.const _ 0))
    (fun a ha => (ha (hWS a.2)).elim)

/-- The normalized class in `H^{2c}(ℂ^c, ℂ^c \ {0}; ℚ)` that every chart coclass pulls back. -/
noncomputable abbrev normalizedPointCoclass : RelativeCohomology ℚ (puncturedPair ℂ c) (2 * c) :=
  normalizedRelativeCoclass (standardComplexLocalClass ℚ c)
    (standardComplexLocalClass_ne_zero_for_chart c)

/-- The pullback of the normalized class to `(W, W \ S)`, for `W ⊆ S`. -/
noncomputable def fullSupportCoclass (W S : Set M) (hWS : W ⊆ S) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W S) (2 * c) :=
  relativeCohomologyMap ℚ (2 * c) (toPuncturedPairOfSubset c W S hWS) (normalizedPointCoclass c)

/-- The restriction of the full-support coclass to a smaller neighbourhood is its full-support
coclass. -/
lemma relativeCohomologyMap_fullSupportCoclass (W W' S : Set M) (hWS : W ⊆ S) (h : W' ⊆ W) :
    relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap h S)
        (fullSupportCoclass c W S hWS) =
      fullSupportCoclass c W' S (h.trans hWS) := by
  rw [fullSupportCoclass, fullSupportCoclass, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 2

end PointPair

section SmoothPair

variable (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- A chart coclass of normal dimension `0` is the full-support coclass of its chart. -/
lemma smoothClosedSupportChartCoclass_eq_fullSupportCoclass (hmd : d - m = 0)
    (z : ComplexPoint Y) (W : Set (ComplexPoint X))
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hWS : W ⊆ Set.range (Point.map i)) :
    smoothClosedSupportChartCoclass X Y i m d z W hW =
      fullSupportCoclass (d - m) W (Set.range (Point.map i)) hWS := by
  have := puncturedPair_hom_subsingleton (neighborhoodSupportComplementPair W
    (Set.range (Point.map i))) (d - m) hmd
  rw [smoothClosedSupportChartCoclass, chartNormalProjectionCoclass, fullSupportCoclass,
    Subsingleton.elim (chartNormalProjectionPair _ _ _ _ _ W hW)
      (toPuncturedPairOfSubset (d - m) W _ hWS)]

/-- When the closed immersion is onto and the normal dimension is `0`, the glued coclass section is
the sheafified full-support coclass of `X(ℂ)`. -/
theorem smoothClosedSupportCoclassSection_eq_fullSupportCoclass (hmd : d - m = 0)
    (hS : Set.range (Point.map i) = Set.univ) :
    smoothClosedSupportCoclassSection X Y i m d =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
        (2 * (d - m))).app (op ⊤)
        (fullSupportCoclass (d - m) ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
          (Set.range (Point.map i)) (by rw [hS]; exact Set.subset_univ _)) := by
  apply TopCat.Presheaf.section_ext
  intro w _
  obtain ⟨z, rfl⟩ : w ∈ Set.range (Point.map i) := hS ▸ Set.mem_univ w
  have hz := mem_smoothClosedSupportChartOpen X Y i m d z
  change (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm _ _ = _
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z _ hz,
    smoothClosedSupportChartCoclassGerm, supportRelativeCohomologyGerm,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) _ hz]
  congr 1
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) (Set.range (Point.map i))
      (2 * (d - m))).naturality (homOfLE (le_top :
        smoothClosedSupportChartOpen X Y i m d z ≤ ⊤)).op)
    (fullSupportCoclass (d - m) ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
          (Set.range (Point.map i)) (by rw [hS]; exact Set.subset_univ _))
  refine Eq.trans ?_ (h.trans rfl)
  refine (congrArg (ConcreteCategory.hom ((supportRelativeCohomologyToSheaf
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app
      (op (smoothClosedSupportChartOpen X Y i m d z)))) ?_).trans rfl
  exact (smoothClosedSupportChartCoclass_eq_fullSupportCoclass X Y i m d hmd z
    (smoothClosedSupportChartOpen X Y i m d z : Set (ComplexPoint X)) (le_refl _)
    (by rw [hS]; exact Set.subset_univ _)).trans
    (relativeCohomologyMap_fullSupportCoclass _ _ _ _ _ (le_top : smoothClosedSupportChartOpen X Y i m d z ≤ ⊤)).symm

end SmoothPair


/-- Restricting a sheafified relative class is sheafifying its restriction. -/
lemma supportRelativeCohomologyToSheaf_map_apply {T : TopCat.{0}} (S : Set T) (n : ℕ)
    {V W : Opens T} (h : W ≤ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set T) S) n) :
    (𝓗_[S]^n(T; ℚ)).presheaf.map (homOfLE h).op
        ((supportRelativeCohomologyToSheaf T S n).app (op V) a) =
      (supportRelativeCohomologyToSheaf T S n).app (op W)
        (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap h S) a) :=
  (ConcreteCategory.congr_hom ((supportRelativeCohomologyToSheaf T S n).naturality
    (homOfLE h).op) a).symm

section Component

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (x : X.left) (hx : Order.coheight x = 0)

include hx in
/-- A point of coheight `0` is supported on all of `X(ℂ)`. -/
lemma cycleComponentSupport_eq_univ_of_coheight_zero : cycleComponentSupport X x = Set.univ := by
  obtain rfl := eq_genericPoint_of_coheight_zero x hx
  exact congrArg (fun Z : Closeds (ComplexPoint X) => (Z : Set (ComplexPoint X)))
    (cycleComponentAnalyticClosedSupport_genericPoint X)

include hx in
/-- For a point of coheight `0`, the closed lift of the smooth locus is onto its ambient open. -/
lemma range_cycleComponentSmoothLocusClosedLift_eq_univ :
    Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) = Set.univ := by
  rw [← cycleComponentSmoothClosedLiftAmbientMap_support,
    cycleComponentSupport_eq_univ_of_coheight_zero X x hx, Set.preimage_univ]

/-- For a point of coheight `0`, the coclass section on the smooth locus is the sheafified
full-support coclass. -/
theorem cycleComponentSmoothClosedLiftCoclassSection_eq_fullSupportCoclass :
    cycleComponentSmoothClosedLiftCoclassSection X x hx =
      (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))) (2 * 0)).app (op ⊤)
        (fullSupportCoclass 0 ((⊤ : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))) :
          Set (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
          (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
          (by rw [range_cycleComponentSmoothLocusClosedLift_eq_univ X x hx]
              exact Set.subset_univ _)) := by
  have hsub : ((⊤ : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))) :
      Set (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x))) ⊆
      Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    rw [range_cycleComponentSmoothLocusClosedLift_eq_univ X x hx]
    exact Set.subset_univ _
  have key : ∀ (c : ℕ) (hc : c = 0)
      (t : (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * c)
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
          (op ⊤)),
      t = (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))) (2 * c)).app (op ⊤)
          (fullSupportCoclass c _ _ hsub) →
      (hc ▸ t : (𝓗_[Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))]^(2 * 0)
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)); ℚ)).presheaf.obj
          (op ⊤)) =
      (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x))) (2 * 0)).app (op ⊤)
          (fullSupportCoclass 0 _ _ hsub) := by
    intro c hc t ht
    subst hc
    exact ht
  let := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  exact key _ (cycleComponentSmoothClosedLift_codimension X x hx) _
    (smoothClosedSupportCoclassSection_eq_fullSupportCoclass _ _ _ _ _
      (cycleComponentSmoothClosedLift_codimension X x hx)
      (range_cycleComponentSmoothLocusClosedLift_eq_univ X x hx))

include hx in
lemma cycleComponentSmoothSupportAmbientOpen_subset_support :
    ((cycleComponentSmoothSupportAmbientOpen X x : Opens (ComplexPoint X)) : Set (ComplexPoint X)) ⊆
      cycleComponentSupport X x := by
  rw [cycleComponentSupport_eq_univ_of_coheight_zero X x hx]
  exact Set.subset_univ _

/-- Layer 5: for a point of coheight `0`, upstream's normalized coclass section is the sheafified
full-support coclass on the smooth ambient open. -/
theorem cycleComponentSmoothSupportCoclassSection_eq_fullSupportCoclass :
    cycleComponentSmoothSupportCoclassSection X x hx =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * 0)).app (op (cycleComponentSmoothSupportAmbientOpen X x))
        (fullSupportCoclass 0 _ _ (cycleComponentSmoothSupportAmbientOpen_subset_support X x hx)) := by
  dsimp only [cycleComponentSmoothSupportCoclassSection, supportRelativeCohomologySectionOnOpen,
    supportRelativeCohomologySectionOpenImage]
  rw [cycleComponentSmoothClosedLiftCoclassSection_eq_fullSupportCoclass X x hx,
    supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]
  have he : eqToHom (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm =
      homOfLE (le_of_eq (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x).symm) :=
    Subsingleton.elim _ _
  rw [he]
  refine (supportRelativeCohomologyToSheaf_map_apply _ _ _ _).trans ?_
  congr 1
  rw [fullSupportCoclass, fullSupportCoclass, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  refine (LinearMap.congr_fun (relativeCohomologyMap_comp ℚ (2 * 0) _ _) _).symm.trans ?_
  have := puncturedPair_hom_subsingleton (neighborhoodSupportComplementPair
    ((cycleComponentSmoothSupportAmbientOpen X x : Opens (ComplexPoint X)) : Set (ComplexPoint X))
    (cycleComponentSupport X x)) 0 rfl
  exact congrArg (fun φ => relativeCohomologyMap ℚ (2 * 0) φ (normalizedPointCoclass 0))
    (Subsingleton.elim _ _)

end Component

end HodgeLean.RealDefs
