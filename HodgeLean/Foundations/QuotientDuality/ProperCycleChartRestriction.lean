import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization

/-! # The literal normal coclass under restriction of its ambient chart -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Restricting the ambient chart retains its actual normal projection and its exact complex normal coclass.
Source: Bott and Tu, Differential Forms in Algebraic Topology, sections 5 and 6, restriction of normal orientations.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_coclass_restrOpen {M E : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin k → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (O : Opens M)
    (W : Set M) (hW : W ⊆ (e.restrOpen (O : Set M) O.isOpen).source) :
    chartNormalProjectionCoclass E k (e.restrOpen (O : Set M) O.isOpen) S
      (fun y hy => hS y hy.1) W hW =
    chartNormalProjectionCoclass E k e S hS W (fun y hy => (hW hy).1) := rfl

end HodgeLean.Foundations.QuotientDuality
