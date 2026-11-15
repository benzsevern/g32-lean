import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian13Proofs

/-! # Exponential transport of smooth component normalization

Implication from an actual smooth component anchor to a normalized complex chart
on the exponential cover. Smooth-locus identification and regular-domain gluing
remain separate obligations. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

/-- Transport the actual supported component class to a complex normal chart at a smooth anchor.
Both chart directions are complex analytic at the corresponding anchor.
Source: `bh11_component_normal_chart`, `spec_complexExponential_localBiholomorph`,
and naturality of relative singular cohomology under maps of pairs. -/
theorem bh13_exponential_normal_chart
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (p : Fin (dim X.left) → ℂ) (hp : f p = 0)
    (ha : abelianExp X p ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    ∃ (e : OpenPartialHomeomorph (Fin (dim X.left) → ℂ)
        ((Fin (dim X.left - 1) → ℂ) × (Fin 1 → ℂ)))
      (he : ∀ y ∈ e.source, f y = 0 ↔ (e y).2 = 0),
      p ∈ e.source ∧ AnalyticAt ℂ e p ∧ AnalyticAt ℂ e.symm (e p) ∧
      ∃ (W : Opens (Fin (dim X.left) → ℂ)) (_hpW : p ∈ W)
        (hWe : (W : Set (Fin (dim X.left) → ℂ)) ⊆ e.source),
        relativeCohomologyMap ℚ 2
          (neighborhoodSupportInclusionPairMap
            (show (W : Set (Fin (dim X.left) → ℂ)) ⊆ Set.univ from Set.subset_univ _)
            {z | f z = 0})
          (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx))))) =
        chartNormalProjectionCoclass (Fin (dim X.left - 1) → ℂ) 1 e
          {z | f z = 0} he W hWe :=
  bh13_exponential_normal_chart_aux X x hx f hf hs p hp ha

open HodgeLean.Foundations.Curves

example : ∃ p : Fin (dim E.left) → ℂ,
    ∃ (e : OpenPartialHomeomorph (Fin (dim E.left) → ℂ)
        ((Fin (dim E.left - 1) → ℂ) × (Fin 1 → ℂ)))
      (he : ∀ y ∈ e.source, bh8_cubicWitness.f y = 0 ↔ (e y).2 = 0),
      p ∈ e.source ∧ AnalyticAt ℂ e p ∧ AnalyticAt ℂ e.symm (e p) ∧
      ∃ (W : Opens (Fin (dim E.left) → ℂ)) (_hpW : p ∈ W)
        (hWe : (W : Set (Fin (dim E.left) → ℂ)) ⊆ e.source),
        relativeCohomologyMap ℚ 2
          (neighborhoodSupportInclusionPairMap
            (show (W : Set (Fin (dim E.left) → ℂ)) ⊆ Set.univ from Set.subset_univ _)
            {z | bh8_cubicWitness.f z = 0})
          (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim E.left) → ℂ))
          {z | bh8_cubicWitness.f z = 0} ⟶ bh8_equationPair (dim E.left) bh8_cubicWitness.f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim E.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_coverMap E bh8_cubicWitness.x bh8_cubicWitness.f bh8_cubicWitness.support)
        (complexSupportInjectiveSectionCohomologyEquiv E
          (cycleComponentAnalyticClosedSupport E bh8_cubicWitness.x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology E
            (cycleComponentAnalyticClosedSupport E bh8_cubicWitness.x) 2)
            (cycleComponentSupportedInjectiveClass E bh8_cubicWitness.x bh8_cubicWitness.codim))))) =
        chartNormalProjectionCoclass (Fin (dim E.left - 1) → ℂ) 1 e
          {z | bh8_cubicWitness.f z = 0} he W hWe := by
  let x := bh8_cubicWitness.x
  let w := Classical.choice
    (HodgeLean.RealDefs.nonempty_complexPoint_cycleComponentSmoothLocusOver E x)
  let y := Point.map (cycleComponentSmoothLocusClosedLiftOver E x) w
  let a := Point.map (openInclusion E (cycleComponentSmoothLocusAmbientOpen E x)) y
  have ha : a ∈ cycleComponentSmoothSupportAmbientOpen E x :=
    (cycleComponentSmoothLocusAmbientOpen_analytic_image E x).subset ⟨y, rfl⟩
  have haS : a ∈ cycleComponentSupport E x :=
    (cycleComponentSmoothLocusClosedLift_complexPoints_range E x).subset ⟨w, rfl⟩
  obtain ⟨p, hp⟩ := surjective_abelianExp E a
  have hpS : abelianExp E p ∈ bh4_componentSupport E x := hp.symm ▸ haS
  have hpA : abelianExp E p ∈ cycleComponentSmoothSupportAmbientOpen E x := hp.symm ▸ ha
  refine ⟨p, ?_⟩
  exact bh13_exponential_normal_chart E x bh8_cubicWitness.codim
    bh8_cubicWitness.f bh8_cubicWitness.analytic bh8_cubicWitness.support p
    ((bh8_cubicWitness.support p).mpr hpS) hpA

end HodgeLean.Adapters
