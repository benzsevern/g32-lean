import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentFlatHolomorphicChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatChartHomologyImage
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentOnSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClassProperties

/-! # The specified intrinsic component in the original flattened chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

local instance properCycle_intrinsicFlatChartPoint_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (ComplexPoint X) := f4_t2Space X

local instance properCycle_intrinsicFlatChartPoint_an_t2
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : T2Space (a3b4_an X.hom) := f4_t2Space X

/-- On an actual open component piece, the specified intrinsic component class has standard complex point value in the literal tangential coordinates of the original holomorphic flattened support chart.
Source: properCycle_component_flat_holomorphic_chart; properCycle_flat_chart_homology_image; properCycle_intrinsic_class_chart.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_flat_chart_point
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (r d : ℕ) (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (r : ℕ))
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)))
    (hOr : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
      Set.range (properCycle_component_support_map X γ ξ hξ))
    (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (y : ComplexPoint (properCycle_component_over X ξ))
    (hy : properCycle_component_support_map X γ ξ hξ y ∈ O)
    (hcenter : e (properCycle_component_support_map X γ ξ hξ y).val = (0, 0)) :
    let z := properCycle_component_support_map X γ ξ hξ y
    let V : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)) :=
      ⟨{s | s.val ∈ e.source}, e.open_source.preimage continuous_subtype_val⟩
    relativeHomologyMap ℚ (2*r)
      (properCycle_flat_support_point_pair (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)
        e 0 hflat z (hOe z hy) (congrArg Prod.fst hcenter))
      ((properCycle_open_local_homology_iso (TopCat.of (a3b4_cycleSupport X.hom γ))
        V ⟨z, hOe z hy⟩ (2*r)).inv.hom
        (localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*r)
          (properCycle_intrinsic_component_on_support X γ ξ hξ r hdim) z)) =
      standardComplexLocalClass ℚ r := by
  dsimp only
  let Z := properCycle_component_over X ξ
  let f := properCycle_component_support_map X γ ξ hξ
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (ComplexPoint Z) := f4_t2Space Z
  obtain ⟨c, hsrc, hhol, hval⟩ := properCycle_component_flat_holomorphic_chart
    X γ ξ hξ r d e hflat he O hOr hOe y hy
  have hyc : y ∈ c.source := by rw [hsrc]; exact hy
  have hsub : ∀ u ∈ c.source, (f u).val ∈ e.source := by
    intro u hu
    have huO : f u ∈ O := by
      change u ∈ f ⁻¹' (O : Set _)
      rw [← hsrc]
      exact hu
    exact hOe (f u) huO
  have hμ := properCycle_intrinsic_class_chart Z r hdim c hhol y hyc
  exact properCycle_flat_chart_homology_image (a3b4_an X.hom) (TopCat.of (ComplexPoint Z))
    (a3b4_cycleSupport X.hom γ) r (TopCat.of (Fin d → ℂ)) e 0 hflat f
    (properCycle_component_support_map_embedding X γ ξ hξ).injective c hsub hval y hyc hcenter
    (properCycle_intrinsic_class Z r hdim) hμ

end HodgeLean.Foundations.QuotientDuality
