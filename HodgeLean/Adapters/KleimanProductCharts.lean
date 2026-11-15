import HodgeLean.Adapters.CycleClassSmoothCharts
import HodgeLean.Adapters.KleimanProductDefs

/-! # Holomorphic normal charts for the Kleiman chart bridges

Holomorphic flattening charts on the open subscheme `X \ Z_sing` are read in the complex-manifold
charts of `X(ℂ)` through evaluation of regular functions. Their normal coordinates are holomorphic
submersions cutting out a component support near each of its smooth points. Two such maps, on an
open that avoids the other intersection components, give the charts of the stage-4 chart bridges.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Filter Topology Set
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- Inverse of the inclusion of an open subscheme on complex points, extended by a default point.
Source: `AlgebraicGeometry.ComplexPoint.openEquiv`. -/
def hc9k_openPointInv (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (z₀ : ComplexPoint (openScheme X A))
    (y : ComplexPoint X) : ComplexPoint (openScheme X A) := by
  classical
  exact if h : y ∈ Point.overOpen A then (openEquiv X A).symm ⟨y, h⟩ else z₀

/-- The inverse of an open inclusion undoes the inclusion.
Source: `Equiv.symm_apply_apply`. -/
theorem hc9k_openPointInv_map (X : Over (Spec ↧ℂ)) (A : X.left.Opens)
    (z₀ q : ComplexPoint (openScheme X A)) :
    hc9k_openPointInv X A z₀ (Point.map (openInclusion X A) q) = q := by
  have h : Point.map (openInclusion X A) q ∈ Point.overOpen A := ((openEquiv X A) q).2
  simp only [hc9k_openPointInv, h, ↓reduceDIte]
  exact (openEquiv X A).symm_apply_apply q

example (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (q : ComplexPoint (openScheme X A)) :
    hc9k_openPointInv X A q (Point.map (openInclusion X A) q) = q :=
  hc9k_openPointInv_map X A q q

/-- An open-subscheme chart read through an ambient chart is complex analytic. -/
theorem hc9k_analyticAt_openChart_symm (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d (openScheme X A).hom]
    (z : ComplexPoint (openScheme X A)) (b : ComplexPoint X) {w : Fin d → ℂ}
    (hw : w ∈ (localChart X d b).target) (q : ComplexPoint (openScheme X A))
    (hq : q ∈ (localChart (openScheme X A) d z).source)
    (hqw : Point.map (openInclusion X A) q = (localChart X d b).symm w) :
    AnalyticAt ℂ (fun v => localChart (openScheme X A) d z
      (hc9k_openPointInv X A z ((localChart X d b).symm v))) w := by
  let j := Point.map (openInclusion X A)
  let W := localChart (openScheme X A) d z
  have hopen : IsOpen (j '' W.source) := (isOpenEmbedding_map_open X A).isOpenMap _ W.open_source
  have hev : ∀ᶠ v in 𝓝 w, (localChart X d b).symm v ∈ j '' W.source :=
    ((localChart X d b).continuousAt_symm hw) (hopen.mem_nhds ⟨q, hq, hqw⟩)
  refine AnalyticAt.pi fun i => ?_
  let D := localEtaleCoordinates (openScheme X A) d z
  let V := D.ambientCoordinateOpen
  let t := D.ambientCoordinateSection i
  have hqV : q ∈ Point.overOpen V := by
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source (openScheme X A) d z q hq
    simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have hV : (localChart X d b).symm w ∈ Point.overOpen (A.ι ''ᵁ V) := by
    rw [← hqw, Point.mem_overOpen_map_iff]
    change q.underlying ∈ A.ι ⁻¹ᵁ A.ι ''ᵁ V
    rw [A.ι.preimage_image_eq V]
    exact hqV
  apply (analyticAt_localChart_symm_evaluate X d b hw (A.ι ''ᵁ V)
    ((A.ι.appIso V).inv t) hV).congr
  filter_upwards [hev] with v hv
  obtain ⟨r, hr, hrv⟩ := hv
  rw [← hrv, hc9k_openPointInv_map, evaluate_openEquiv]
  exact (localChart_apply_component_eq_evaluate (openScheme X A) d z r hr i).symm

/-- An ambient chart read through an open-subscheme chart is complex analytic. -/
theorem hc9k_analyticAt_openChart (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d (openScheme X A).hom]
    (z : ComplexPoint (openScheme X A)) (b : ComplexPoint X) {w : Fin d → ℂ}
    (hw : w ∈ (localChart (openScheme X A) d z).target)
    (hb : Point.map (openInclusion X A) ((localChart (openScheme X A) d z).symm w) ∈
      (localChart X d b).source) :
    AnalyticAt ℂ (fun v => localChart X d b
      (Point.map (openInclusion X A) ((localChart (openScheme X A) d z).symm v))) w := by
  let j := Point.map (openInclusion X A)
  have hev : ∀ᶠ v in 𝓝 w, j ((localChart (openScheme X A) d z).symm v) ∈
      (localChart X d b).source :=
    ((Point.continuous_map (openInclusion X A)).continuousAt.comp
      ((localChart (openScheme X A) d z).continuousAt_symm hw))
      ((localChart X d b).open_source.mem_nhds hb)
  refine AnalyticAt.pi fun i => ?_
  let D := localEtaleCoordinates X d b
  let V := D.ambientCoordinateOpen
  let t := D.ambientCoordinateSection i
  have hV : (localChart (openScheme X A) d z).symm w ∈
      Point.overOpen ((openInclusion X A).left ⁻¹ᵁ V) := by
    rw [← Point.mem_overOpen_map_iff]
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source X d b _ hb
    simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  apply (analyticAt_localChart_symm_evaluate (openScheme X A) d z hw _
    ((openInclusion X A).left.app V t) hV).congr
  filter_upwards [hev] with v hv
  rw [← Point.evaluate_map]
  exact (localChart_apply_component_eq_evaluate X d b _ hv i).symm


/-- On an open subset, the manifold derivative of a restricted map is the ambient one. -/
theorem hc9k_mfderiv_opens {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ω M]
    (U : Opens M) (g : M → F) (u : U) (hg : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) g u) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (fun x : U => g x) u = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g u := by
  have hval : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → M) u :=
    (contMDiff_subtype_val (n := ω) u).mdifferentiableAt (by simp)
  have hgu : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) (fun x : U => g x) u := hg.comp u hval
  rw [hgu.mfderiv, hg.mfderiv]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  apply Filter.EventuallyEq.fderiv_eq
  have hmem : ((chartAt E u.1).subtypeRestr ⟨u⟩).target ∈ 𝓝 ((extChartAt 𝓘(ℂ, E) u) u) := by
    apply ((chartAt E u.1).subtypeRestr ⟨u⟩).open_target.mem_nhds
    simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl]
    exact ((chartAt E u.1).subtypeRestr ⟨u⟩).map_source (mem_chart_source E u)
  filter_upwards [hmem] with v hv
  have h := (chartAt E u.1).subtypeRestr_symm_eqOn ⟨u⟩ hv
  change chartAt F (g u) (g (((chartAt E u.1).subtypeRestr ⟨u⟩).symm v)) =
    chartAt F (g u) (g ((chartAt E u.1).symm v))
  rw [h]
  rfl

/-- A map with a differentiable right inverse near a point has surjective derivative there. -/
theorem hc9k_fderiv_surjective_of_rightInverse {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (G : E → F) (H : F → E) (b : F)
    (hG : DifferentiableAt ℂ G (H b)) (hH : DifferentiableAt ℂ H b)
    (hGH : G ∘ H =ᶠ[𝓝 b] id) : Function.Surjective (fderiv ℂ G (H b)) := by
  intro v
  refine ⟨fderiv ℂ H b v, ?_⟩
  have h := fderiv_comp b hG hH
  rw [hGH.fderiv_eq, fderiv_id] at h
  exact (congrArg (fun L => L v) h).symm


/-- The normal coordinate of a holomorphic flattening chart on an open subscheme, read on the
ambient complex points.
Source: `closedImmersionHolomorphicFlatteningChart`; Griffiths--Harris, *Principles of Algebraic
Geometry*, chapter 0 §2, local defining functions of submanifolds. -/
def hc9k_ambientNormalCoordinate (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (Y : Over (Spec ↧ℂ))
    (i : Y ⟶ openScheme X A) (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d (openScheme X A).hom] [IsClosedImmersion i.left]
    (z : ComplexPoint Y) (y : ComplexPoint X) : Fin (d - m) → ℂ :=
  (closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i m d z
    (hc9k_openPointInv X A (Point.map i z) y)).2

example (X : Over (Spec ↧ℂ)) (A : X.left.Opens) (Y : Over (Spec ↧ℂ))
    (i : Y ⟶ openScheme X A) (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d (openScheme X A).hom] [IsClosedImmersion i.left]
    (z : ComplexPoint Y) (q : ComplexPoint (openScheme X A)) :
    hc9k_ambientNormalCoordinate X A Y i m d z (Point.map (openInclusion X A) q) =
      (closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i m d z q).2 := by
  rw [hc9k_ambientNormalCoordinate, hc9k_openPointInv_map]

/-- In an ambient chart, the normal coordinate is analytic with surjective derivative.
Source: chain rule for the analytic chart transitions. -/
theorem hc9k_ambientNormalCoordinate_analytic (X : Over (Spec ↧ℂ)) (A : X.left.Opens)
    (Y : Over (Spec ↧ℂ)) (i : Y ⟶ openScheme X A) (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension d (openScheme X A).hom] [IsClosedImmersion i.left]
    (z : ComplexPoint Y) (q : ComplexPoint (openScheme X A))
    (hq : q ∈ (closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i m d z).source) :
    AnalyticAt ℂ (hc9k_ambientNormalCoordinate X A Y i m d z ∘
        (localChart X d (Point.map (openInclusion X A) q)).symm)
      (localChart X d (Point.map (openInclusion X A) q) (Point.map (openInclusion X A) q)) ∧
    Function.Surjective (fderiv ℂ (hc9k_ambientNormalCoordinate X A Y i m d z ∘
        (localChart X d (Point.map (openInclusion X A) q)).symm)
      (localChart X d (Point.map (openInclusion X A) q) (Point.map (openInclusion X A) q))) := by
  let j := Point.map (openInclusion X A)
  let y := j q
  let CX := localChart X d y
  let CΩ := localChart (openScheme X A) d (Point.map i z)
  let φ := closedImmersionNormalCoordinateChange (openScheme X A) Y i m d z
  let w₀ := CX y
  have hy : y ∈ CX.source := mem_localChart_source X d y
  have hqΩ : q ∈ CΩ.source := hq.1.1
  have hφ := (OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hq.1.2
  have hyw : j q = CX.symm w₀ := (CX.left_inv hy).symm
  let ψ : (Fin d → ℂ) → (Fin d → ℂ) := fun v => CΩ (hc9k_openPointInv X A (Point.map i z) (CX.symm v))
  have hψ : AnalyticAt ℂ ψ w₀ :=
    hc9k_analyticAt_openChart_symm X A d (Point.map i z) y (CX.map_source hy) q hqΩ hyw
  have hψw : ψ w₀ = CΩ q := by
    change CΩ (hc9k_openPointInv X A (Point.map i z) (CX.symm w₀)) = CΩ q
    rw [← hyw, hc9k_openPointInv_map]
  have hG : hc9k_ambientNormalCoordinate X A Y i m d z ∘ CX.symm = fun v => (φ (ψ v)).2 := rfl
  have hφa : AnalyticAt ℂ φ (ψ w₀) := hψw ▸ hφ.2.1
  have hGa : AnalyticAt ℂ (fun v => (φ (ψ v)).2) w₀ := analyticAt_snd.comp (hφa.comp hψ)
  refine ⟨hG ▸ hGa, ?_⟩
  change Function.Surjective (fderiv ℂ (hc9k_ambientNormalCoordinate X A Y i m d z ∘ CX.symm) w₀)
  rw [hG]
  let a := (φ (ψ w₀)).1
  let c₀ := (φ (ψ w₀)).2
  let T : (Fin d → ℂ) → (Fin d → ℂ) := fun u => CX (j (CΩ.symm u))
  let H : (Fin (d - m) → ℂ) → (Fin d → ℂ) := fun c => T (φ.symm (a, c))
  have hφs : ψ w₀ ∈ φ.source := hψw ▸ hφ.1
  have hac : (a, c₀) = φ (ψ w₀) := rfl
  have hφsy : φ.symm (a, c₀) = CΩ q := by rw [hac, φ.left_inv hφs, hψw]
  have hHc : H c₀ = w₀ := by
    change CX (j (CΩ.symm (φ.symm (a, c₀)))) = w₀
    rw [hφsy, CΩ.left_inv hqΩ]
  have hT : AnalyticAt ℂ T (CΩ q) := by
    refine hc9k_analyticAt_openChart X A d (Point.map i z) y (CΩ.map_source hqΩ) ?_
    rw [CΩ.left_inv hqΩ]
    exact hy
  have hφi : AnalyticAt ℂ φ.symm (a, c₀) := by
    rw [hac, hψw]
    exact hφ.2.2
  have hHa : AnalyticAt ℂ H c₀ := by
    have hT' : AnalyticAt ℂ T (φ.symm (a, c₀)) := hφsy ▸ hT
    exact hT'.comp_of_eq (hφi.comp (AnalyticAt.prod analyticAt_const analyticAt_id)) rfl
  rw [← hHc]
  apply hc9k_fderiv_surjective_of_rightInverse _ H c₀
    ((hHc ▸ hGa).differentiableAt) hHa.differentiableAt
  have htar : (a, c₀) ∈ φ.target := by rw [hac]; exact φ.map_source hφs
  have h1 : ∀ᶠ c in 𝓝 c₀, (a, c) ∈ φ.target :=
    (continuous_const.prodMk continuous_id).continuousAt (φ.open_target.mem_nhds htar)
  have hCΩt : φ.symm (a, c₀) ∈ CΩ.target := by rw [hφsy]; exact CΩ.map_source hqΩ
  have hcont : ContinuousAt (fun c : Fin (d - m) → ℂ => φ.symm (a, c)) c₀ :=
    (φ.continuousAt_symm htar).comp (continuous_const.prodMk continuous_id).continuousAt
  have h2 : ∀ᶠ c in 𝓝 c₀, φ.symm (a, c) ∈ CΩ.target :=
    hcont (CΩ.open_target.mem_nhds hCΩt)
  have hcont2 : ContinuousAt (fun c : Fin (d - m) → ℂ => j (CΩ.symm (φ.symm (a, c)))) c₀ :=
    (Point.continuous_map (openInclusion X A)).continuousAt.comp
      ((CΩ.continuousAt_symm hCΩt).comp_of_eq hcont rfl)
  have hjy : j (CΩ.symm (φ.symm (a, c₀))) ∈ CX.source := by
    rw [hφsy, CΩ.left_inv hqΩ]
    exact hy
  have h3 : ∀ᶠ c in 𝓝 c₀, j (CΩ.symm (φ.symm (a, c))) ∈ CX.source :=
    hcont2 (CX.open_source.mem_nhds hjy)
  filter_upwards [h1, h2, h3] with c hc1 hc2 hc3
  change (φ (CΩ (hc9k_openPointInv X A (Point.map i z)
    (CX.symm (CX (j (CΩ.symm (φ.symm (a, c))))))))).2 = c
  rw [CX.left_inv hc3, hc9k_openPointInv_map, CΩ.right_inv hc2, φ.right_inv hc1]

/-- The ambient normal coordinate is holomorphic with surjective derivative on the chart image. -/
theorem hc9k_ambientNormalCoordinate_contMDiffAt (X : Over (Spec ↧ℂ)) (A : X.left.Opens)
    (Y : Over (Spec ↧ℂ)) (i : Y ⟶ openScheme X A) (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension d (openScheme X A).hom] [IsClosedImmersion i.left]
    (z : ComplexPoint Y) (q : ComplexPoint (openScheme X A))
    (hq : q ∈ (closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i m d z).source) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (d - m) → ℂ) ω
        (hc9k_ambientNormalCoordinate X A Y i m d z) (Point.map (openInclusion X A) q) ∧
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (d - m) → ℂ)
        (hc9k_ambientNormalCoordinate X A Y i m d z) (Point.map (openInclusion X A) q)) := by
  obtain ⟨ha, hs⟩ := hc9k_ambientNormalCoordinate_analytic X A Y i m d z q hq
  let g := hc9k_ambientNormalCoordinate X A Y i m d z
  let j := Point.map (openInclusion X A)
  have hcont : ContinuousAt g (j q) := by
    have h1 : ContinuousAt (g ∘ j) q := by
      have he : g ∘ j = fun r => (closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i
          m d z r).2 := by
        funext r
        simp only [Function.comp_apply, g, j, hc9k_ambientNormalCoordinate, hc9k_openPointInv_map]
      rw [he]
      exact continuous_snd.continuousAt.comp
        ((closedImmersionHolomorphicFlatteningChart (openScheme X A) Y i m d z).continuousAt hq)
    exact ((isOpenEmbedding_map_open X A).continuousAt_iff).mp h1
  have hc : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin (d - m) → ℂ) ω g (j q) := by
    rw [contMDiffAt_iff]
    refine ⟨hcont, ?_⟩
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
      modelWithCornersSelf_coe, range_id]
    exact ha.contDiffAt.contDiffWithinAt
  refine ⟨hc, ?_⟩
  rw [(hc.mdifferentiableAt (by simp)).mfderiv]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  intro v
  obtain ⟨u, hu⟩ := hs ((tangentSpaceCastModel 𝓘(ℂ, Fin (d - m) → ℂ) (g (j q))) v)
  refine ⟨(tangentSpaceCastModel 𝓘(ℂ, Fin d → ℂ) (j q)).symm u, ?_⟩
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change (tangentSpaceCastModel 𝓘(ℂ, Fin (d - m) → ℂ) (g (j q))).symm
    (fderiv ℂ (g ∘ (localChart X d (j q)).symm) (localChart X d (j q) (j q)) u) = v
  rw [hu, ContinuousLinearEquiv.symm_apply_apply]

/-- At a point of a component support off its singular locus there is a holomorphic map to
`ℂ^q`, a submersion on an open neighborhood, whose zeros there are exactly the support. -/
theorem hc9k_exists_component_normalMap
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q) (a : ComplexPoint X)
    (ha : a ∈ cycleComponentAnalyticClosedSupport X x)
    (has : a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0) :
    ∃ (V : Opens (ComplexPoint X)) (_ : a ∈ V) (g : ComplexPoint X → Fin q → ℂ),
      (∀ y ∈ V, g y = 0 ↔ y ∈ cycleComponentAnalyticClosedSupport X x) ∧
      (∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω g y ∧
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) g y)) := by
  obtain rfl : dim X.left = d := SmoothOfRelativeDimension.dim_eq X.hom d
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  let A := cycleComponentSmoothLocusAmbientOpen X x
  let i := cycleComponentSmoothLocusClosedLiftOver X x
  let j := Point.map (openInclusion X A)
  have hrange : a ∈ Set.range (cycleComponentSmoothClosedLiftAmbientMap X x) := by
    rw [← Set.image_univ]
    change a ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤
    rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact has
  obtain ⟨b, rfl⟩ := hrange
  have hb : b ∈ Set.range (Point.map i) := by
    rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
    exact ha
  obtain ⟨z, rfl⟩ := hb
  let e₀ := closedImmersionHolomorphicFlatteningChart (openScheme X A)
    (cycleComponentSmoothLocusOver X x) i (dim X.left - q) (dim X.left) z
  let V : Opens (ComplexPoint X) :=
    ⟨j '' e₀.source, (isOpenEmbedding_map_open X A).isOpenMap _ e₀.open_source⟩
  have haV : cycleComponentSmoothClosedLiftAmbientMap X x (Point.map i z) ∈ V :=
    ⟨_, closedImmersionHolomorphicFlatteningChart_mem_source _ _ _ _ _ z, rfl⟩
  let g := hc9k_ambientNormalCoordinate X A (cycleComponentSmoothLocusOver X x) i
    (dim X.left - q) (dim X.left) z
  have hzero : ∀ y ∈ V, g y = 0 ↔ y ∈ cycleComponentAnalyticClosedSupport X x := by
    rintro _ ⟨r, hr, rfl⟩
    change (e₀ (hc9k_openPointInv X A (Point.map i z) (j r))).2 = 0 ↔ _
    rw [hc9k_openPointInv_map]
    change _ ↔ r ∈ cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' cycleComponentSupport X x
    rw [cycleComponentSmoothClosedLiftAmbientMap_support]
    exact (closedImmersionHolomorphicFlatteningChart_mem_range_iff _ _ _ _ _ z r hr).symm
  have hdiff : ∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ)
      𝓘(ℂ, Fin (dim X.left - (dim X.left - q)) → ℂ) ω g y ∧
      Function.Surjective (mfderiv 𝓘(ℂ, Fin (dim X.left) → ℂ)
        𝓘(ℂ, Fin (dim X.left - (dim X.left - q)) → ℂ) g y) := by
    rintro _ ⟨r, hr, rfl⟩
    exact hc9k_ambientNormalCoordinate_contMDiffAt X A _ i _ _ z r hr
  have hcod := cycleComponentSmoothClosedLift_codimension X x hx
  have key : ∀ (c : ℕ), c = q → ∀ g : ComplexPoint X → Fin c → ℂ,
      (∀ y ∈ V, g y = 0 ↔ y ∈ cycleComponentAnalyticClosedSupport X x) →
      (∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin c → ℂ) ω g y ∧
        Function.Surjective (mfderiv 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin c → ℂ) g y)) →
      ∃ g : ComplexPoint X → Fin q → ℂ,
        (∀ y ∈ V, g y = 0 ↔ y ∈ cycleComponentAnalyticClosedSupport X x) ∧
        (∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin q → ℂ) ω g y ∧
          Function.Surjective (mfderiv 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin q → ℂ) g y)) := by
    rintro c rfl g h1 h2
    exact ⟨g, h1, h2⟩
  obtain ⟨g', h1, h2⟩ := key _ hcod g hzero hdiff
  exact ⟨V, haV, g', h1, h2⟩

/-- Two coordinate blocks side by side vanish exactly when both blocks vanish. -/
theorem hc9k_append_eq_zero_iff {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) :
    Fin.append a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa only [Fin.append_left, Pi.zero_apply] using congrFun h (Fin.castAdd q i)
    · simpa only [Fin.append_right, Pi.zero_apply] using congrFun h (Fin.natAdd p i)
  · rintro ⟨rfl, rfl⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, Pi.zero_apply]
    · simp only [Fin.append_right, Pi.zero_apply]

/-- Every point of the intersection subscheme lies on both analytic supports. -/
theorem hc9k_charts_intersection_support_le
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left) (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) :
    cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y := by
  have hmem : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∈
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).support : Set X.left) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [Scheme.IdealSheafData.support_sup] at hmem
  obtain ⟨hx, hy⟩ := hmem
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left) at hx
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({y} : Set X.left), isClosed_closure⟩).support : Set X.left) at hy
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx hy
  intro a ha
  change Point.underlying a ∈ closure ({_} : Set X.left) at ha
  constructor
  · change Point.underlying a ∈ closure ({x} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure ha
  · change Point.underlying a ∈ closure ({y} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure ha

/-- A common point of two analytic supports lies on the support of some irreducible component of
the scheme-theoretic intersection. -/
theorem hc9k_mem_some_component_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left) (c : ComplexPoint X) (hcx : c ∈ cycleComponentAnalyticClosedSupport X x)
    (hcy : c ∈ cycleComponentAnalyticClosedSupport X y) :
    ∃ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme ∧
      c ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') := by
  let I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  have hmem : Point.underlying c ∈ (I.support : Set X.left) := by
    rw [Scheme.IdealSheafData.support_sup]
    refine ⟨?_, ?_⟩
    · change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hcx
    · change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({y} : Set X.left), isClosed_closure⟩).support : Set X.left)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hcy
  rw [← Scheme.IdealSheafData.range_subschemeι] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hC := irreducibleComponent_mem_irreducibleComponents v
  obtain ⟨g, hg⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := v))
    isClosed_irreducibleComponent
  refine ⟨g, ?_, ?_⟩
  · rw [hg.def]
    exact hC
  · have hvg : v ∈ closure ({g} : Set I.subscheme) := by
      rw [hg.def]
      exact mem_irreducibleComponent
    change Point.underlying c ∈ closure ({I.subschemeι g} : Set X.left)
    rw [← hv]
    have hsp : g ⤳ v := specializes_iff_mem_closure.mpr hvg
    exact specializes_iff_mem_closure.mp (hsp.map I.subschemeι.continuous)

/-- Restriction of an ambient normal map to an open inside its domain, as a chart of the
form required by the chart bridges. -/
theorem hc9k_restrict_normalMap
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (q : ℕ) (x : X.left)
    (V U : Opens (ComplexPoint X)) (hUV : U ≤ V) (g : ComplexPoint X → Fin q → ℂ)
    (hg0 : ∀ y ∈ V, g y = 0 ↔ y ∈ cycleComponentAnalyticClosedSupport X x)
    (hg : ∀ y ∈ V, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω g y ∧
      Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) g y)) :
    ∃ f : C(U, Fin q → ℂ), (∀ u : U, f u = g u.1) ∧
      (∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω f ∧
      (∀ u : U, f u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) f u)) := by
  let f : C(U, Fin q → ℂ) := ⟨fun u => g u.1, continuous_iff_continuousAt.mpr fun u =>
    (hg u.1 (hUV u.2)).1.continuousAt.comp continuous_subtype_val.continuousAt⟩
  refine ⟨f, fun _ => rfl, fun u => hg0 u.1 (hUV u.2), fun u =>
    contMDiffAt_subtype_iff.mpr (hg u.1 (hUV u.2)).1, fun u _ => ?_⟩
  change Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) (fun x : U => g x) u)
  rw [hc9k_mfderiv_opens U g u ((hg u.1 (hUV u.2)).1.mdifferentiableAt (by simp))]
  exact (hg u.1 (hUV u.2)).2

/-- Chart existence at a point of one intersection component off both singular loci and off the
other components.
Source: SGA 1, Exposé XII, 3.1; the holomorphic implicit function theorem; Hartshorne,
*Algebraic Geometry*, I, 1.5. -/
theorem hc9k_exists_transverse_chart_of_charts
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (_hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme)
    (a : ComplexPoint X)
    (ha : a ∈ cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
    (hax : a ∉ cycleComponentSingularAnalyticClosedFiltration X x 0)
    (hay : a ∉ cycleComponentSingularAnalyticClosedFiltration X y 0)
    (hunique : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') → w' = w) :
    ∃ (U : Opens (ComplexPoint X)) (_ : a ∈ U) (f : C(U, Fin p → ℂ)) (h : C(U, Fin q → ℂ)),
      (∀ u : U, f u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X x) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) ω f ∧
      (∀ u : U, f u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin p → ℂ) f u)) ∧
      (∀ u : U, h u = 0 ↔ u.1 ∈ cycleComponentAnalyticClosedSupport X y) ∧
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) ω h ∧
      (∀ u : U, h u = 0 →
        Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin q → ℂ) h u)) ∧
      (∀ u : U, hc9k_appendCoordinates f h u = 0 ↔
        u.1 ∈ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)) := by
  classical
  let I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  have haxy := hc9k_charts_intersection_support_le X x y w ha
  obtain ⟨Vx, haVx, gx, hgx0, hgx⟩ :=
    hc9k_exists_component_normalMap X d p x hx a haxy.1 hax
  obtain ⟨Vy, haVy, gy, hgy0, hgy⟩ :=
    hc9k_exists_component_normalMap X d q y hy a haxy.2 hay
  let := ccm12_isNoetherian X
  have hfin := ccm11_intersection_components_finite X.left (ccm3_primeIdeal X.left x)
    (ccm3_primeIdeal X.left y)
  let T : Set I.subscheme := {w' | closure ({w'} : Set I.subscheme) ∈
    irreducibleComponents I.subscheme ∧ w' ≠ w}
  have hT : T.Finite := hfin.subset fun w' hw' => hw'.1
  let C : Set (ComplexPoint X) := ⋃ w' ∈ T,
    (cycleComponentAnalyticClosedSupport X (I.subschemeι w') : Set (ComplexPoint X))
  have hC : IsClosed C := hT.isClosed_biUnion fun w' _ =>
    (cycleComponentAnalyticClosedSupport X (I.subschemeι w')).isClosed
  let O : Opens (ComplexPoint X) := ⟨Cᶜ, hC.isOpen_compl⟩
  let U := Vx ⊓ Vy ⊓ O
  have haO : a ∈ O := by
    intro haC
    obtain ⟨w', hw'T, haw'⟩ := Set.mem_iUnion₂.mp haC
    exact hw'T.2 (hunique w' hw'T.1 haw')
  have haU : a ∈ U := ⟨⟨haVx, haVy⟩, haO⟩
  obtain ⟨f, hfg, hf0, hfhol, hfsub⟩ :=
    hc9k_restrict_normalMap X d p x Vx U (inf_le_left.trans inf_le_left) gx hgx0 hgx
  obtain ⟨h, hhg, hh0, hhhol, hhsub⟩ :=
    hc9k_restrict_normalMap X d q y Vy U (inf_le_left.trans inf_le_right) gy hgy0 hgy
  refine ⟨U, haU, f, h, hf0, hfhol, hfsub, hh0, hhhol, hhsub, fun u => ?_⟩
  change Fin.append (f u) (h u) = 0 ↔ _
  rw [hc9k_append_eq_zero_iff, hf0, hh0]
  constructor
  · rintro ⟨hux, huy⟩
    obtain ⟨w', hw', huw'⟩ := hc9k_mem_some_component_support X x y u.1 hux huy
    by_cases hww : w' = w
    · exact hww ▸ huw'
    · exact absurd (Set.mem_iUnion₂.mpr ⟨w', ⟨hw', hww⟩, huw'⟩) u.2.2
  · intro huw
    exact hc9k_charts_intersection_support_le X x y w huw

end HodgeLean.Adapters
