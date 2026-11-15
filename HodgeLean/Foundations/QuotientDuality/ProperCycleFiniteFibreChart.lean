import HodgeLean.Foundations.QuotientDuality.ProperCycleChartNeighborhood

/-! # Original complex chart normalization of actual finite fibre point maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual finite-fibre point map preserves the original complex chart class when the literal compressed models intertwine the original continuous map.
Source: Hatcher, Algebraic Topology, section 3.3, chart orientations and local degree.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_fibre_point_pushforward_chart
    {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) [DecidableEq (f ⁻¹' {y})]
    (x : f ⁻¹' {y}) (d : ℕ)
    (eX : OpenPartialHomeomorph X (Fin d → ℂ)) (hx : x.val ∈ eX.source)
    (eY : OpenPartialHomeomorph Y (Fin d → ℂ)) (hy : y ∈ eY.source)
    (hisolate : ∀ z ∈ eX.source, f z = y → z = x.val)
    (hmodel : ∀ t : Fin d → ℂ,
      f (chartModelEmbedding d eX x.val hx t) = chartModelEmbedding d eY y hy t) :
    properCycle_finite_fibre_point_pushforward f y hfinite (2 * d) x
      (localClassOfChart d eX x.val hx) = localClassOfChart d eY y hy := by
  let a := relativeHomologyMap ℚ (2 * d)
    (properCycle_chart_neighborhood_pair_map X d eX x.val hx) (standardComplexLocalClass ℚ d)
  have ha : relativeHomologyMap ℚ (2 * d)
      (b6m_subspacePairMap X eX.source ({x.val} : Set X)ᶜ) a =
      localClassOfChart d eX x.val hx := properCycle_chart_neighborhood_class_image X d eX x.val hx
  have h := properCycle_finite_fibre_point_pushforward_on_neighborhood
    f y hfinite x eX.source hisolate (2 * d) a
  rw [ha] at h
  refine h.trans ?_
  change relativeHomologyMap ℚ (2 * d) _
    (relativeHomologyMap ℚ (2 * d)
      (properCycle_chart_neighborhood_pair_map X d eX x.val hx) (standardComplexLocalClass ℚ d)) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  have hp : properCycle_chart_neighborhood_pair_map X d eX x.val hx ≫
      (properCycle_isolated_support_pair_map X (f ⁻¹' {y}) eX.source x.val hisolate ≫
        properCycle_fibre_complement_pair_map f y) = chartModelEmbeddingPair d eY y hy := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext t
      exact Subtype.ext (hmodel t.val)
    · ext t
      exact hmodel t
  rw [hp]
  rfl

end HodgeLean.Foundations.QuotientDuality
