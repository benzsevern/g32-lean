import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalChartTransport
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingSupportHomology

/-! # Literal complex orientation transport along an actual open sheet -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual point map of an original open sheet preserves the original normalized chart class for the literal pulled chart.
Source: properCycle_chart_model_local_transport; imagePointPairMap; localClassOfChart.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_sheet_chart_orientation
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Function.Injective f)
    (H : OpenPartialHomeomorph X Y) (hH : ∀ z : X, f z = H z)
    (d : ℕ) (e : OpenPartialHomeomorph Y (Fin d → ℂ)) (he : e.source ⊆ H.target)
    (x : X) (hx : x ∈ H.source) (hxe : H x ∈ e.source) :
    relativeHomologyMap ℚ (2*d) (imagePointPairMap f hf x)
      (localClassOfChart d (H.trans e) x ⟨hx, hxe⟩) =
      localClassOfChart d e (f x) (by rw [hH]; exact hxe) := by
  have ht (t : Fin d → ℂ) : f (chartModelEmbedding d (H.trans e) x ⟨hx, hxe⟩ t) =
      chartModelEmbedding d e (f x) (by rw [hH]; exact hxe) t := by
    simpa only [hH] using properCycle_chart_model_local_transport d H e he x hx hxe t
  have hp : chartModelEmbeddingPair d (H.trans e) x ⟨hx, hxe⟩ ≫ imagePointPairMap f hf x =
      chartModelEmbeddingPair d e (f x) (by rw [hH]; exact hxe) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z : 1
      apply Subtype.ext
      exact ht z.val
    · ext z : 1
      exact ht z
  change relativeHomologyMap ℚ (2*d) (imagePointPairMap f hf x)
    (relativeHomologyMap ℚ (2*d) (chartModelEmbeddingPair d (H.trans e) x ⟨hx, hxe⟩)
      (standardComplexLocalClass ℚ d)) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hp]
  rfl

end HodgeLean.Foundations.QuotientDuality
