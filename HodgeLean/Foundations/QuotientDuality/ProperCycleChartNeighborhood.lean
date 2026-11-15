import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteFibreExcision
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClass

/-! # Original compressed chart classes inside their actual neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original compressed chart model has its entire image in the actual chart source.
Source: Hatcher, Algebraic Topology, section 3.3, local chart orientation classes.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_model_mem_source
    {X : Type} [TopologicalSpace X] (d : ℕ)
    (e : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X) (hx : x ∈ e.source)
    (t : Fin d → ℂ) : chartModelEmbedding d e x hx t ∈ e.source := by
  have ht := (chartModelEmbedding d e x hx).map_source
    (show t ∈ (chartModelEmbedding d e x hx).source by
      rw [chartModelEmbedding_source]; trivial)
  change chartModelEmbedding d e x hx t ∈
    e.symm.target ∩ e ⁻¹' (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).target at ht
  exact ht.1

/-- The original compressed chart model maps into the actual chart-source point-complement pair.
Source: Hatcher, Algebraic Topology, section 3.3, local chart orientation classes.
HC no distance; AV milestone no distance. -/
def properCycle_chart_neighborhood_pair_map
    (X : TopCat.{0}) (d : ℕ) (e : OpenPartialHomeomorph X (Fin d → ℂ))
    (x : X) (hx : x ∈ e.source) :
    puncturedPair ℂ d ⟶ neighborhoodSupportComplementPair e.source ({x} : Set X) :=
  let g : TopCat.of (Fin d → ℂ) ⟶ TopCat.of e.source := TopCat.ofHom
    ⟨fun t => ⟨chartModelEmbedding d e x hx t, properCycle_chart_model_mem_source d e x hx t⟩,
      ((chartModelEmbedding d e x hx).isOpenEmbedding
        (chartModelEmbedding_source d e x hx)).continuous.subtype_mk _⟩
  TopPair.ofSubsetHom g (fun t ht he => ht (by
    apply chartModelEmbedding_injective d e x hx
    rw [chartModelEmbedding_zero]
    exact he))

/-- The actual neighborhood class of the standard complex model has the original chart-local orientation as its singleton excision image.
Source: Hatcher, Algebraic Topology, section 3.3, normalization of complex chart orientations.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_neighborhood_class_image
    (X : TopCat.{0}) (d : ℕ) (e : OpenPartialHomeomorph X (Fin d → ℂ))
    (x : X) (hx : x ∈ e.source) :
    relativeHomologyMap ℚ (2 * d) (b6m_subspacePairMap X e.source ({x} : Set X)ᶜ)
      (relativeHomologyMap ℚ (2 * d) (properCycle_chart_neighborhood_pair_map X d e x hx)
        (standardComplexLocalClass ℚ d)) = localClassOfChart d e x hx := by
  have hc : properCycle_chart_neighborhood_pair_map X d e x hx ≫
      b6m_subspacePairMap X e.source ({x} : Set X)ᶜ = chartModelEmbeddingPair d e x hx := by
    ext t : 2 <;> rfl
  have hm := relativeHomologyMap_comp ℚ (2 * d)
    (properCycle_chart_neighborhood_pair_map X d e x hx)
    (b6m_subspacePairMap X e.source ({x} : Set X)ᶜ)
  rw [hc] at hm
  exact (LinearMap.congr_fun hm (standardComplexLocalClass ℚ d)).symm

end HodgeLean.Foundations.QuotientDuality
