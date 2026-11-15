import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothChartOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenSheetChartOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenHolomorphicChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicSheetCharts

/-! # Original complex orientations on actual smooth algebraic open subsets -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The original canonical complex local orientation on an actual smooth algebraic open, transported by its literal point-complement map to the original ambient space.
Source: complexLocalOrientation; ComplexPoint.isOpenEmbedding_map_open; imagePointPairMap.
HC no distance; AV milestone no distance. -/
def properCycle_open_smooth_orientation (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (x : ComplexPoint (openScheme X U)) :
    orientationGroup (a3b4_an X.hom) (2*d) (Point.map (openInclusion X U) x) :=
  relativeHomologyMap ℚ (2*d)
    (imagePointPairMap (TopCat.ofHom (Point.continuousMap (openInclusion X U)))
      (ComplexPoint.isOpenEmbedding_map_open X U).injective x)
    (complexLocalOrientation (openScheme X U) d x)

/-- The actual smooth-open complex local orientation generates the original ambient local homology at that point.
Source: properCycle_open_embedding_local_homology_bijective; span_complexLocalOrientation_eq_top.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_smooth_orientation_generates
    (X : Over (Spec ↧ℂ)) [T1Space (ComplexPoint X)] (U : X.left.Opens) (d : ℕ)
    [SmoothOfRelativeDimension d (openScheme X U).hom]
    (x : ComplexPoint (openScheme X U)) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ _ (properCycle_open_smooth_orientation X U d x)) := by
  let Y := openScheme X U
  letI : T1Space (ComplexPoint Y) := (ComplexPoint.isOpenEmbedding_map_open X U).isEmbedding.t1Space
  let f := TopCat.ofHom (Point.continuousMap (openInclusion X U))
  let P := relativeHomologyMap ℚ (2*d)
    (imagePointPairMap f (ComplexPoint.isOpenEmbedding_map_open X U).injective x)
  have hP : Function.Bijective P := properCycle_open_embedding_local_homology_bijective
    f (ComplexPoint.isOpenEmbedding_map_open X U) x (2*d)
  have hμ : complexLocalOrientation Y d x ≠ 0 :=
    localClassOfChart_ne_zero d (localChart Y d x) x (mem_localChart_source Y d x)
  have hμX : properCycle_open_smooth_orientation X U d x ≠ 0 := by
    intro hz
    apply hμ
    apply hP.injective
    exact hz.trans (map_zero P).symm
  constructor
  · intro q r hqr
    exact smul_left_injective ℚ hμX hqr
  · intro b
    obtain ⟨a, ha⟩ := hP.surjective b
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp
      (show a ∈ Submodule.span ℚ {complexLocalOrientation Y d x} by
        rw [span_complexLocalOrientation_eq_top]; trivial)
    refine ⟨q, ?_⟩
    change q • P (complexLocalOrientation Y d x) = b
    rw [← map_smul, hq, ha]

/-- On an original holomorphic chart contained in the actual smooth algebraic open, its canonical transported orientation is exactly the original ambient chart class.
Source: properCycle_holomorphic_sheet_chart_coordinates; properCycle_smooth_holomorphic_chart_orientation; properCycle_open_sheet_chart_orientation.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_smooth_orientation_chart
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) [LocallyOfFiniteType (openScheme X U).hom]
    [QuasiCompact (openScheme X U).hom] [IsSeparated (openScheme X U).hom]
    (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (he : ∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i))
    (heU : e.source ⊆ Set.range (Point.map (openInclusion X U)))
    (y : ComplexPoint (openScheme X U)) (hy : Point.map (openInclusion X U) y ∈ e.source) :
    properCycle_open_smooth_orientation X U d y =
      localClassOfChart d e (Point.map (openInclusion X U) y) hy := by
  let Y := openScheme X U
  letI : Nonempty (ComplexPoint Y) := ⟨y⟩
  let f := TopCat.ofHom (Point.continuousMap (openInclusion X U))
  have hf : Topology.IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open X U
  let H := hf.toOpenPartialHomeomorph f
  have hH : ∀ z, f z = H z := fun _ => rfl
  have hyH : y ∈ H.source := by rw [hf.toOpenPartialHomeomorph_source f]; trivial
  have heH : e.source ⊆ H.target := by
    rw [hf.toOpenPartialHomeomorph_target f]
    exact heU
  have hhol := properCycle_holomorphic_sheet_chart_coordinates
    (f4_analytification Y) (f4_analytification X) f (f4_map_isHom (openInclusion X U)) H hH d e he
  have hyE : H y ∈ e.source := hy
  change relativeHomologyMap ℚ (2*d) (imagePointPairMap f hf.injective y)
    (complexLocalOrientation Y d y) = _
  rw [properCycle_smooth_holomorphic_chart_orientation Y d (H.trans e) hhol y ⟨hyH, hyE⟩]
  exact properCycle_open_sheet_chart_orientation f hf.injective H hH d e heH y hyH hyE

/-- The canonical orientations of the actual smooth algebraic open have concrete chart-coherent representatives in the original ambient complex point space.
Source: properCycle_holomorphic_vector_chart_open_transport; properCycle_open_smooth_orientation_chart.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_smooth_orientation_chart_coherence
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) [LocallyOfFiniteType (openScheme X U).hom]
    [QuasiCompact (openScheme X U).hom] [IsSeparated (openScheme X U).hom]
    (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (y : ComplexPoint (openScheme X U)) :
    ∃ V : TopologicalSpace.Opens (ComplexPoint (openScheme X U)), y ∈ V ∧
      ∃ e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ),
        ∃ hV : (V : Set (ComplexPoint (openScheme X U))) ⊆
          (Point.map (openInclusion X U)) ⁻¹' e.source,
          ∀ (z : ComplexPoint (openScheme X U)) (hz : z ∈ V),
            properCycle_open_smooth_orientation X U d z =
              localClassOfChart d e (Point.map (openInclusion X U) z) (hV hz) := by
  let Y := openScheme X U
  letI : Nonempty (ComplexPoint Y) := ⟨y⟩
  let f := Point.map (openInclusion X U)
  obtain ⟨e, he, hsource, _⟩ := properCycle_holomorphic_vector_chart_open_transport X U d
    (localChart Y d y) (properCycle_smooth_local_chart_holomorphic Y d y)
  let V : TopologicalSpace.Opens (ComplexPoint Y) :=
    ⟨f ⁻¹' e.source, e.open_source.preimage (Point.continuous_map _)⟩
  have hyV : y ∈ V := by
    change f y ∈ e.source
    rw [hsource]
    exact ⟨y, mem_localChart_source Y d y, rfl⟩
  have heU : e.source ⊆ Set.range f := by
    rw [hsource]
    rintro z ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩
  refine ⟨V, hyV, e, fun _ hz => hz, ?_⟩
  intro z hz
  exact properCycle_open_smooth_orientation_chart X U d e he heU z hz

end HodgeLean.Foundations.QuotientDuality
