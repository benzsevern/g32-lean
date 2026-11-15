import HodgeLean.Foundations.Program.CompensationAssemblyComponentPoint
import HodgeLean.Foundations.Program.CompensationAssemblyProjectionLift
import HodgeLean.Adapters.IntersectionProductCCNormal

/-! # Span-preservation amendment: rank one of the support germ at a regular point

At a regular point of a component support, a flattening chart gives a rational normal
evaluation that determines supported germs. The normalized component class has nonzero
evaluation, so every supported class has the germ of a rational multiple of it, and single-germ
injectivity identifies the supported classes.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A point of the smooth support open lying on the support comes from the smooth locus.
Source: `cycleComponentSmoothClosedLiftAmbientMap_imageOpen` and
`cycleComponentSmoothClosedLiftAmbientMap_support`. -/
theorem cq_span_smoothLocus_nonempty
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    Nonempty (ComplexPoint (cycleComponentSmoothLocusOver X x)) := by
  have hrange : a ∈ Set.range (cycleComponentSmoothClosedLiftAmbientMap X x) := by
    rw [← Set.image_univ]
    change a ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤
    rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact ha
  obtain ⟨b, rfl⟩ := hrange
  have hb : b ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
    exact haS
  obtain ⟨z, -⟩ := hb
  exact ⟨z⟩

/-- Normal evaluation is rational-linear.
Source: additivity of `supportedSingularClass`, linearity of restriction and of the relative
universal coefficient pairing. -/
theorem cq_span_normalEvaluation_smul (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (r : ℚ) (u : H_[S]^(2 * c)(X; ℚ)) :
    a3cc2_normalEvaluation X S c e hS a ha ha0 (r • u) =
      r * a3cc2_normalEvaluation X S c e hS a ha ha0 u := by
  have h : supportedSingularClass X S (2 * c) (r • u) =
      r • supportedSingularClass X S (2 * c) u :=
    map_rat_smul (supportedSingularClass X S (2 * c)).toAddMonoidHom r u
  unfold a3cc2_normalEvaluation
  rw [h, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- A supported class on a codimension-`p` component support whose germ is detected at a
regular point is a rational multiple of the normalized component class.
Source: `a3cc2_supportGerm_eq_of_normalEvaluation`, `hc9k_component_flatteningChart`,
`cycleComponentSupportedInjectiveClass_ne_zero`, `cq_component_relative_germ_injective`. -/
theorem cq_span_relative_multiple
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p)
    (d : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      ((cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X)))ᶜ) (2 * p)) :
    ∃ r : ℚ, d = r • ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X x)
      (2 * p) (cycleComponentSupportedInjectiveClass X x hx) := by
  obtain ⟨z, -, haS, haB⟩ := cq_component_regular_complex_point_on_open X x ⊤
    (by
      obtain ⟨t⟩ := (inferInstance : Nonempty (a2r_component X x).left)
      exact ⟨t, trivial⟩)
  generalize Point.map (Over.homMk (cycleComponentι X.left x) rfl) z = a at haS haB
  have hinj := cq_component_relative_germ_injective X x p hx a haS haB
  have hsmooth : a ∈ cycleComponentSmoothSupportAmbientOpen X x := by
    intro hs
    apply haB
    rw [cq_componentBoundary_singleton]
    exact hs
  obtain ⟨e, he, hae⟩ := hc9k_component_flatteningChart X p x hx a hsmooth haS
  have ha0 : (e a).2 = 0 := (he a hae).mp haS
  have hgerm (v w : H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ))
      (h : a3cc2_normalEvaluation X _ p e he a hae ha0 v =
        a3cc2_normalEvaluation X _ p e he a hae ha0 w) :
      ccm16_supportedComparison X _ (2 * p) v = ccm16_supportedComparison X _ (2 * p) w := by
    apply hinj
    dsimp only
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact a3cc2_supportGerm_eq_of_normalEvaluation X _ p e he a hae ha0 v w h
  have hev0 : a3cc2_normalEvaluation X _ p e he a hae ha0
      (cycleComponentSupportedInjectiveClass X x hx) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := cq_span_smoothLocus_nonempty X x a hsmooth haS
    apply cycleComponentSupportedInjectiveClass_ne_zero X x hx w
    apply (ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X x)
      (2 * p)).injective
    rw [map_zero]
    have h := hgerm (cycleComponentSupportedInjectiveClass X x hx) ((0 : ℚ) • cycleComponentSupportedInjectiveClass X x hx) (by
      rw [cq_span_normalEvaluation_smul, zero_mul]
      exact h0)
    rw [h, zero_smul, map_zero]
  refine ⟨a3cc2_normalEvaluation X _ p e he a hae ha0
      ((ccm16_supportedComparison X _ (2 * p)).symm d) /
    a3cc2_normalEvaluation X _ p e he a hae ha0
      (cycleComponentSupportedInjectiveClass X x hx), ?_⟩
  rw [← map_smul]
  have h := hgerm ((ccm16_supportedComparison X _ (2 * p)).symm d) (_ • _) (by
    rw [cq_span_normalEvaluation_smul, div_mul_cancel₀ _ hev0])
  rw [← h, LinearEquiv.apply_symm_apply]

end HodgeLean.Foundations.Program
