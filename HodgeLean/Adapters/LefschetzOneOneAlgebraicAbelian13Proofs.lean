import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Charts
import HodgeLean.Adapters.UniformizationBiholomorphic

/-! # Exponential transport of smooth component normalization

Implication from an actual smooth component anchor to a normalized complex chart
on the exponential cover. Smooth-locus identification and regular-domain gluing
remain separate obligations. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

private theorem bh13_chartNormalProjectionCoclass_pullback
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

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
/-- Transport the actual supported component class to a complex normal chart at a smooth anchor.
Both chart directions are complex analytic at the corresponding anchor.
Source: `bh11_component_normal_chart`, `spec_complexExponential_localBiholomorph`,
and naturality of relative singular cohomology under maps of pairs. -/
theorem bh13_exponential_normal_chart_aux
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
          {z | f z = 0} he W hWe := by
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  let aX := abelianExp X p
  have haS : aX ∈ cycleComponentSupport X x := (hs p).mp hp
  obtain ⟨a, hpa, haeq, hai⟩ :=
    spec_complexExponential_localBiholomorph X (dim X.left) p
  obtain ⟨d, hd, had, hdA, hdI, V, haV, hVd, hclass⟩ :=
    bh11_component_normal_chart X 1 x hx aX ha haS
  have hap : a p = aX := by
    exact (haeq hpa).symm
  have had' : a p ∈ d.source := hap.symm ▸ had
  let e := a.trans d
  have hpe : p ∈ e.source := ⟨hpa, had'⟩
  have hea (y : Fin (dim X.left) → ℂ) (hy : y ∈ a.source) : a y = abelianExp X y := by
    exact (haeq hy).symm
  have he : ∀ y ∈ e.source, f y = 0 ↔ (e y).2 = 0 := by
    intro y hy
    change f y = 0 ↔ (d (a y)).2 = 0
    rw [← hd (a y) hy.2, hea y hy.1]
    exact hs y
  have hexp : AnalyticAt ℂ (fun y ↦ localChart X (dim X.left) aX (abelianExp X y)) p := by
    have h := (spec_contMDiff_complexExponential X (dim X.left)).contMDiffAt (x := p)
    rw [contMDiffAt_iff] at h
    have h2 := h.2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_id, ModelWithCorners.range_eq_univ,
      contDiffWithinAt_univ, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp, chartAt_eq_localChart X (dim X.left), Set.range_id, id_eq] at h2
    change AnalyticAt ℂ
      (localChart X (dim X.left) aX ∘ fun y ↦ abelianExp X y) p
    simpa [aX, abelianExp] using (contDiffWithinAt_univ.mp h2).analyticAt
  have heA : AnalyticAt ℂ e p := by
    have hdA' : AnalyticAt ℂ
        (fun z ↦ d ((localChart X (dim X.left) aX).symm z))
        (localChart X (dim X.left) aX aX) := by
      exact hdA
    have hcpt := AnalyticAt.comp
      (g := fun z ↦ d ((localChart X (dim X.left) aX).symm z))
      (f := fun y ↦ localChart X (dim X.left) aX (abelianExp X y)) hdA' hexp
    apply hcpt.congr
    have hc : ContinuousAt a p := a.continuousAt hpa
    have hce : ContinuousAt (abelianExp X) p := (continuous_abelianExp X).continuousAt
    filter_upwards [a.open_source.mem_nhds hpa,
      hc (d.open_source.mem_nhds had'),
      hce ((localChart X (dim X.left) aX).open_source.mem_nhds
        (mem_localChart_source X (dim X.left) aX))] with y hya hy hyC
    change d ((localChart X (dim X.left) aX).symm
      (localChart X (dim X.left) aX (abelianExp X y))) = d (a y)
    rw [(localChart X (dim X.left) aX).left_inv]
    · rw [hea y hya]
    · exact hyC
  have haI : AnalyticAt ℂ
      (fun z ↦ a.symm ((localChart X (dim X.left) aX).symm z))
      (localChart X (dim X.left) aX aX) := by
    have hat : aX ∈ a.target := hap ▸ a.map_source hpa
    have h := hai.contMDiffAt (a.open_target.mem_nhds hat)
    rw [contMDiffAt_iff] at h
    have h2 := h.2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_id, ModelWithCorners.range_eq_univ,
      contDiffWithinAt_univ, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp,
      chartAt_eq_localChart X (dim X.left), Set.range_id, id_eq] at h2
    change AnalyticAt ℂ
      (a.symm ∘ (localChart X (dim X.left) aX).symm)
      (localChart X (dim X.left) aX aX)
    simpa only [aX, chartAt_eq_localChart X (dim X.left)] using
      (contDiffWithinAt_univ.mp h2).analyticAt
  have heI : AnalyticAt ℂ e.symm (e p) := by
    have hdI' : AnalyticAt ℂ
        (fun z ↦ localChart X (dim X.left) aX (d.symm z)) (d aX) := by
      exact hdI
    have haI' : AnalyticAt ℂ
        (fun z ↦ a.symm ((localChart X (dim X.left) aX).symm z))
        (localChart X (dim X.left) aX (d.symm (d aX))) := by
      rwa [d.left_inv had]
    have hcomp := AnalyticAt.comp
      (g := fun z ↦ a.symm ((localChart X (dim X.left) aX).symm z))
      (f := fun z ↦ localChart X (dim X.left) aX (d.symm z)) haI' hdI'
    rw [show e p = d aX by change d (a p) = _; rw [hap]]
    apply hcomp.congr
    have hc : ContinuousAt d.symm (d aX) := d.continuousAt_symm (d.map_source had)
    have hmem : d.symm (d aX) ∈ (localChart X (dim X.left) aX).source := by
      rw [d.left_inv had]
      exact mem_localChart_source X (dim X.left) aX
    filter_upwards [hc ((localChart X (dim X.left) aX).open_source.mem_nhds hmem)] with z hz
    change a.symm ((localChart X (dim X.left) aX).symm
      (localChart X (dim X.left) aX (d.symm z))) = a.symm (d.symm z)
    rw [(localChart X (dim X.left) aX).left_inv hz]
  let W : Opens (Fin (dim X.left) → ℂ) :=
    ⟨a.source ∩ a ⁻¹' (V : Set (ComplexPoint X)),
      a.isOpen_inter_preimage V.isOpen⟩
  have hpW : p ∈ W := ⟨hpa, by simpa [hap] using haV⟩
  have hWe : (W : Set (Fin (dim X.left) → ℂ)) ⊆ e.source := by
    intro y hy
    exact ⟨hy.1, hVd hy.2⟩
  have hexpV (y : W) : abelianExp X y.1 ∈ V := by
    rw [← hea y.1 y.2.1]
    exact y.2.2
  have hcontV : Continuous (fun y : W ↦ (⟨abelianExp X y.1, hexpV y⟩ : V)) :=
    ((continuous_abelianExp X).comp continuous_subtype_val).subtype_mk _
  let φ : neighborhoodSupportComplementPair (W : Set (Fin (dim X.left) → ℂ))
      {z | f z = 0} ⟶ neighborhoodSupportComplementPair (V : Set (ComplexPoint X))
        (cycleComponentSupport X x) :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun y ↦ ⟨abelianExp X y.1, hexpV y⟩, hcontV⟩)
      (by
        intro y hy h
        exact hy ((hs y.1).mpr h))
  let iW := neighborhoodSupportInclusionPairMap
    (show (W : Set (Fin (dim X.left) → ℂ)) ⊆ Set.univ from Set.subset_univ _)
    {z | f z = 0}
  let q : neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
      {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
        continuous_subtype_val⟩) (fun _ h ↦ h)
  let cover := bh8_coverMap X x f hs
  let iV := neighborhoodSupportInclusionPairMap
    (show (V : Set (ComplexPoint X)) ⊆ Set.univ from Set.subset_univ _)
    (cycleComponentSupport X x)
  have hclass' : relativeCohomologyMap ℚ 2 iV
      (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) 2
        (cycleComponentSupportedInjectiveClass X x hx)) =
      chartNormalProjectionCoclass (Fin (dim X.left - 1) → ℂ) 1 d
        (cycleComponentSupport X x) hd V hVd := by
    simpa only [iV, Nat.mul_one] using hclass
  have hcomm : iW ≫ q ≫ cover = φ ≫ iV := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  refine ⟨e, he, hpe, heA, heI, W, hpW, hWe, ?_⟩
  change relativeCohomologyMap ℚ 2 iW
      (relativeCohomologyMap ℚ 2 q (relativeCohomologyMap ℚ 2 cover
        (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) 2
          (cycleComponentSupportedInjectiveClass X x hx)))) = _
  calc
    _ = relativeCohomologyMap ℚ 2 (iW ≫ q ≫ cover)
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) 2
            (cycleComponentSupportedInjectiveClass X x hx)) := by
              rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp]
              rfl
    _ = relativeCohomologyMap ℚ 2 (φ ≫ iV)
        (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) 2
          (cycleComponentSupportedInjectiveClass X x hx)) := by rw [hcomm]
    _ = relativeCohomologyMap ℚ 2 φ
        (chartNormalProjectionCoclass (Fin (dim X.left - 1) → ℂ) 1 d
          (cycleComponentSupport X x) hd V hVd) := by
            rw [relativeCohomologyMap_comp]
            exact congrArg (relativeCohomologyMap ℚ 2 φ) hclass'
    _ = chartNormalProjectionCoclass (Fin (dim X.left - 1) → ℂ) 1 e
          {z | f z = 0} he W hWe := by
            refine bh13_chartNormalProjectionCoclass_pullback
              (Fin (dim X.left - 1) → ℂ) (Fin (dim X.left - 1) → ℂ) 1
              e d {z | f z = 0} (cycleComponentSupport X x) he hd W V hWe hVd φ ?_
            intro y
            change (d (abelianExp X y.1)).2 = (d (a y.1)).2
            rw [hea y.1 y.2.1]

end HodgeLean.Adapters
