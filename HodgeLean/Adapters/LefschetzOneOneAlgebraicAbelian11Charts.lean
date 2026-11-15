import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11ChartsProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Witnesses

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
theorem bh11_component_normal_chart
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
          (cycleComponentSupport X x) he W hWe :=
  bh11_component_normal_chart_aux X q x hx a ha haS

open HodgeLean.Foundations.Curves

example := by
  let x := bh8_cubicWitness.x
  let w := Classical.choice
    (HodgeLean.RealDefs.nonempty_complexPoint_cycleComponentSmoothLocusOver E x)
  let y := Point.map (cycleComponentSmoothLocusClosedLiftOver E x) w
  let a := Point.map (openInclusion E (cycleComponentSmoothLocusAmbientOpen E x)) y
  have ha : a ∈ cycleComponentSmoothSupportAmbientOpen E x :=
    (cycleComponentSmoothLocusAmbientOpen_analytic_image E x).subset ⟨y, rfl⟩
  have haS : a ∈ cycleComponentSupport E x :=
    (cycleComponentSmoothLocusClosedLift_complexPoints_range E x).subset ⟨w, rfl⟩
  exact bh11_component_normal_chart E 1 x bh8_cubicWitness.codim a ha haS

end HodgeLean.Adapters
