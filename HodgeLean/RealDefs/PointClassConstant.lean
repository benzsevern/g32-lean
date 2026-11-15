import HodgeLean.RealDefs.SupportEnlargement
import HodgeLean.RealDefs.OrientationConstant
import HodgeLean.RealDefs.Port.AlgebraicGeometry.Cycle.Component.PointClassNormalization

/-! # All closed points of a connected smooth projective variety have the same class

Let `X` be smooth projective of dimension `d` over `ℂ` with `X(ℂ)` preconnected. For a point `x`
of coheight `d`, forgetting the support of upstream's supported class factors through the full
support (`forgetSupport_restrict`), where forgetting is injective. Through upstream's
sheaf-to-singular identification (`supportedSingularClass_restrict`) and upstream's exact point
normalization (`cycleComponentSupportedInjectiveClass_point_normalization`), the class becomes
`pointCoclassPullback y`: the pullback to `(X(ℂ), ∅)` of the normalized coclass at the complex
point `y` of `x`. Paired with a global top homology class `w`, it gives the coefficient `q` of
`w` against the orientation at `y`, which does not depend on `y`
(`exists_relativeHomologyMap_eq_smul_complexLocalOrientation`). So the classes agree
(`cycleComponentSheafClass_eq_of_coheight_eq`). -/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexPoint
open AlgebraicTopology.Singular

noncomputable section

namespace HodgeLean.RealDefs

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

omit [SmoothOfRelativeDimension d X.hom] in
/-- Pulling back twice is pulling back along the composite. -/
lemma relativeCohomologyMap_apply_apply {P Q R : TopPair} (n : ℕ) (f : P ⟶ Q) (g : Q ⟶ R)
    (α : RelativeCohomology ℚ R n) :
    relativeCohomologyMap ℚ n f (relativeCohomologyMap ℚ n g α) =
      relativeCohomologyMap ℚ n (f ≫ g) α := by
  rw [relativeCohomologyMap_comp]
  rfl

omit [SmoothOfRelativeDimension d X.hom] in
/-- Pushing forward twice is pushing forward along the composite. -/
lemma relativeHomologyMap_apply_apply {P Q R : TopPair} (n : ℕ) (f : P ⟶ Q) (g : Q ⟶ R)
    (z : RelativeHomology ℚ P n) :
    relativeHomologyMap ℚ n g (relativeHomologyMap ℚ n f z) = relativeHomologyMap ℚ n (f ≫ g) z := by
  rw [relativeHomologyMap_comp]
  rfl

/-- The pair `(X(ℂ), ∅)`, written as `(⊤, ⊤ \ ⊤)`, maps to the pointed pair at `y`. -/
abbrev fullToPointPairMap (y : ComplexPoint X) :=
  neighborhoodSupportToPointPairMap ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
    ((⊤ : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) y trivial

/-- The normalized coclass at `y`, pulled back to `(X(ℂ), ∅)`. -/
def pointCoclassPullback [IsProjective X.hom] (y : ComplexPoint X) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
      ((⊤ : Closeds (ComplexPoint X)) : Set (ComplexPoint X))) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d) (fullToPointPairMap X y) (analyticPointLocalCoclass X d y)

/-- `(X(ℂ), ∅)` as a subspace pair of `X(ℂ)`. -/
abbrev fullToAmbientPairMap :
    neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        ((⊤ : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) ⟶
      TopPair.ofSubset (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X))) :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun _ ha => ha)

lemma fullToPointPairMap_eq (y : ComplexPoint X) :
    fullToPointPairMap X y = fullToAmbientPairMap X ≫
      supportInclusionPairMap (TopCat.of (ComplexPoint X))
        (Set.singleton_subset_iff.mpr (Opens.mem_top y)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable [IsProjective X.hom]

/-- On a preconnected variety, the pulled-back point coclass does not depend on the point. -/
theorem pointCoclassPullback_eq [PreconnectedSpace (ComplexPoint X)] (y y' : ComplexPoint X) :
    pointCoclassPullback X d y = pointCoclassPullback X d y' := by
  apply (relativeCohomologyEquivDualHomology ℚ _ (2 * d)).injective
  ext w
  obtain ⟨q, hq⟩ := exists_relativeHomologyMap_eq_smul_complexLocalOrientation X d
    (relativeHomologyMap ℚ (2 * d) (fullToAmbientPairMap X) w)
  have key (y : ComplexPoint X) :
      relativeCohomologyEquivDualHomology ℚ _ (2 * d) (pointCoclassPullback X d y) w = q := by
    rw [pointCoclassPullback, relativeCohomologyEquivDualHomology_relativeCohomologyMap,
      fullToPointPairMap_eq, relativeHomologyMap_comp]
    erw [hq y]
    rw [map_smul]
    have h1 := analyticPointLocalCoclass_apply_localClass X d y
    unfold analyticPointLocalCoclassDual at h1
    erw [h1]
    simp
  rw [key, key]

/-- `X(ℂ)` with empty subspace, back to the pair `(⊤, ⊤ \ ⊤)`. -/
abbrev ambientToFullPairMap :
    TopPair.ofSubset (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X))) ⟶
      neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        ((⊤ : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun m => ⟨m, trivial⟩, by fun_prop⟩) (fun _ ha => ha)

omit [IsProjective X.hom] in
lemma ambientToFullPairMap_comp : ambientToFullPairMap X ≫ fullToAmbientPairMap X = 𝟙 _ := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Given a fundamental class of `X(ℂ)`, every pulled-back point coclass is nonzero. -/
theorem pointCoclassPullback_ne_zero
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d))
    (hw : ∀ y : ComplexPoint X,
      relativeHomologyMap ℚ (2 * d)
          (supportInclusionPairMap (TopCat.of (ComplexPoint X))
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
        complexLocalOrientation X d y)
    (y : ComplexPoint X) : pointCoclassPullback X d y ≠ 0 := by
  intro h0
  have h := congrArg (fun α => relativeCohomologyEquivDualHomology ℚ _ (2 * d) α
    (relativeHomologyMap ℚ (2 * d) (ambientToFullPairMap X) w)) h0
  simp only [map_zero, LinearMap.zero_apply] at h
  rw [pointCoclassPullback, relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    fullToPointPairMap_eq, relativeHomologyMap_apply_apply, ← Category.assoc,
    ambientToFullPairMap_comp, Category.id_comp] at h
  erw [hw y] at h
  have h1 := analyticPointLocalCoclass_apply_localClass X d y
  unfold analyticPointLocalCoclassDual at h1
  erw [h1] at h
  exact one_ne_zero h

section Sheaf

variable [IsIntegral X.left] [Smooth X.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a point `x` of coheight `d` with complex point `y`, upstream's supported class, with its
support enlarged to `X(ℂ)` and read in singular cohomology, is the pulled-back coclass at `y`. -/
theorem exists_supportedSingularClass_supportEnlarge_eq (x : X.left)
    (hx : Order.coheight x = d) :
    ∃ y : ComplexPoint X,
      supportedSingularClass X ⊤ (2 * d) (supportEnlarge X le_top (2 * d)
        (cycleComponentSupportedInjectiveClass X x hx)) = pointCoclassPullback X d y := by
  obtain ⟨z, -⟩ := exists_cycleComponent_smooth_complexPoint X x
  refine ⟨cycleComponentMap X x z, ?_⟩
  rw [supportedSingularClass_restrict, cycleComponentSupportedInjectiveClass_point_normalization
    X x d z hx]
  change relativeCohomologyMap ℚ (2 * d) _ (complexSupportInjectiveSectionCohomologyEquiv X _ ⊤
    (2 * d) (rationalSupportAddEquivSupportedInjectiveHomology X _ (2 * d)
      ((rationalSupportAddEquivSupportedInjectiveHomology X _ (2 * d)).symm _))) = _
  rw [AddEquiv.apply_symm_apply, analyticComponentPointSupportedInjectiveCoclass_relative,
    analyticComponentPointRelativeCoclass, pointCoclassPullback]
  erw [relativeCohomologyMap_apply_apply]
  congr 2

/-- On a preconnected smooth projective variety of dimension `d`, all points of coheight `d`
have the same cycle class. -/
theorem cycleComponentSheafClass_eq_of_coheight_eq [PreconnectedSpace (ComplexPoint X)]
    (x x' : X.left) (hx : Order.coheight x = d) (hx' : Order.coheight x' = d) :
    cycleComponentSheafClass X x hx = cycleComponentSheafClass X x' hx' := by
  change ComplexPoint.forgetSupport ℚ X _ (2 * d) _ = ComplexPoint.forgetSupport ℚ X _ (2 * d) _
  rw [forgetSupport_restrict X (le_top : cycleComponentAnalyticClosedSupport X x ≤ ⊤),
    forgetSupport_restrict X (le_top : cycleComponentAnalyticClosedSupport X x' ≤ ⊤)]
  congr 1
  apply (supportedSingularClass X ⊤ (2 * d)).injective
  obtain ⟨y, hy⟩ := exists_supportedSingularClass_supportEnlarge_eq X d x hx
  obtain ⟨y', hy'⟩ := exists_supportedSingularClass_supportEnlarge_eq X d x' hx'
  rw [hy, hy', pointCoclassPullback_eq]

/-- Given a fundamental class of `X(ℂ)`, the class of a point of coheight `d` is nonzero. -/
theorem cycleComponentSheafClass_ne_zero_of_fundamentalClass (x : X.left)
    (hx : Order.coheight x = d)
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d))
    (hw : ∀ y : ComplexPoint X,
      relativeHomologyMap ℚ (2 * d)
          (supportInclusionPairMap (TopCat.of (ComplexPoint X))
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
        complexLocalOrientation X d y) :
    cycleComponentSheafClass X x hx ≠ 0 := by
  change ComplexPoint.forgetSupport ℚ X _ (2 * d) _ ≠ 0
  rw [forgetSupport_restrict X (le_top : cycleComponentAnalyticClosedSupport X x ≤ ⊤)]
  intro h0
  rw [← map_zero (ComplexPoint.forgetSupport ℚ X ⊤ (2 * d))] at h0
  have h1 := forgetSupport_injective_of_eq_top ℚ X ⊤ rfl (2 * d) h0
  obtain ⟨y, hy⟩ := exists_supportedSingularClass_supportEnlarge_eq X d x hx
  apply pointCoclassPullback_ne_zero X d w hw y
  rw [← hy, h1, map_zero]

end Sheaf

end HodgeLean.RealDefs

end
