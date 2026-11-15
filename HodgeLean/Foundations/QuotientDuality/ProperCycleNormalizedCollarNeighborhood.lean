import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Adapters.NormalConeB4aClassRestriction

/-! # Original local cycle normalization on actual collar neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cycle normalization can be restricted to an actual chart neighborhood inside the retained collar whose retraction values stay in the original chart.
Source: a3b4_IsCycleClass; a3b4a_classLocal_normalization_mono; ProperCycleSupportCollar.chart_neighborhood.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_collar_neighborhood
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ) (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a)
    (C : ProperCycleSupportCollar (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ))
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hflat : ∀ u ∈ e.source, u ∈ a3b4_cycleSupport X.hom γ ↔ (e u).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport X.hom γ) :
    ∃ (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source),
      x ∈ W ∧ ∃ hWN : (W : Set (ComplexPoint X)) ⊆ C.neighborhood,
      (∀ (u : ComplexPoint X) (hu : u ∈ W), (C.retraction ⟨u, hWN hu⟩).val ∈ e.source) ∧
      relativeCohomologyMap ℚ (2*k)
        (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)) a =
      a3b4_multiplicity X.hom γ x •
        chartNormalProjectionCoclass (Fin r → ℂ) k e (a3b4_cycleSupport X.hom γ) hflat (W : Set _) hWe := by
  obtain ⟨W0, hW0e, hW0, hxW0, hWa0⟩ := ha r e hflat x hx hxS he
  obtain ⟨W1, hxW1, hW1e, hWN1, hR1⟩ := C.chart_neighborhood e ⟨x, hxS⟩ hx
  let W : Opens (ComplexPoint X) := ⟨W0 ∩ W1.carrier, hW0.inter W1.isOpen⟩
  have hWe : (W : Set (ComplexPoint X)) ⊆ e.source := fun u hu => hW0e hu.1
  have hWN : (W : Set (ComplexPoint X)) ⊆ C.neighborhood := fun u hu => hWN1 hu.2
  refine ⟨W, hWe, ⟨hxW0, hxW1⟩, hWN, ?_, ?_⟩
  · intro u hu
    exact hR1 u hu.2
  · exact a3b4a_classLocal_normalization_mono e (a3b4_cycleSupport X.hom γ) hflat
      (show (W : Set (ComplexPoint X)) ⊆ W0 from Set.inter_subset_left) hW0e a
      (a3b4_multiplicity X.hom γ x) hWa0

end HodgeLean.Foundations.QuotientDuality
