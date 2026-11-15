import HodgeLean.Foundations.Program.SchoenTowerL1bActionScalarClass
import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartMultiplicity
import HodgeLean.Foundations.Program.SchoenTowerL1bActionDiskMap

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A punctured scalar disk map whose translated values lie in a chart
has an actual map to that chart's target neighbourhood pair. -/
def s2v_l1b_action_chart_disk_coordinates
    {M : Type} [TopologicalSpace M] (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (x : M) (h : ℂ → ℂ) (r : ℝ)
    (hc : ContinuousOn h (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0)
    (ht : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv (h z) + e x ∈ e.target) :
    neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0 ⟶
      neighborhoodPointComplementPair e.target (e x) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun z : Metric.ball (0 : ℂ) r =>
      ⟨b6m_surfaceCoordinateEquiv (h z) + e x, ht z z.property⟩,
      ((b6m_surfaceCoordinateEquiv.continuous.comp
        (continuousOn_iff_continuous_domRestrict.mp hc)).add continuous_const).subtype_mk _⟩)
    (fun z hz he => hn z z.property hz (b6m_surfaceCoordinateEquiv.injective (by
      have he0 : b6m_surfaceCoordinateEquiv (h z) = 0 :=
        add_right_cancel (he.trans (zero_add _).symm)
      simpa only [map_zero] using he0)))

/-- Forgetting the chart target restriction gives scalar coordinate
conversion followed by translation to the chart center. -/
theorem s2v_l1b_action_chart_disk_coordinates_factorization
    {M : Type} [TopologicalSpace M] (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (x : M) (h : ℂ → ℂ) (r : ℝ)
    (hc : ContinuousOn h (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0)
    (ht : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv (h z) + e x ∈ e.target) :
    s2v_l1b_action_chart_disk_coordinates e x h r hc hn ht ≫
      neighborhoodPointComplementPairMap e.target (e x) =
        s2v_l1b_action_disk_pair_map h r hc hn ≫ s2v_l1b_action_scalar_pair_iso.hom ≫
          translationPointComplementPairMap (Fin 1 → ℂ) (e x) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

end HodgeLean.Foundations.Program
