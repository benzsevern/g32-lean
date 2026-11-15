import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedFlatChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentSupportMap

/-! # Intrinsic holomorphic charts inherited from original flattened cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual reduced component containing an open piece of the original flattened support inherits its literal tangential coordinates as an intrinsic holomorphic chart.
Source: properCycle_embedded_flat_chart; f4_map_isHom; anb_isHolFun_restrict.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_flat_holomorphic_chart
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support)
    (r d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ)))
    (hOr : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆
      Set.range (properCycle_component_support_map X γ ξ hξ))
    (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (y : ComplexPoint (properCycle_component_over X ξ))
    (hy : properCycle_component_support_map X γ ξ hξ y ∈ O) :
    ∃ c : OpenPartialHomeomorph (ComplexPoint (properCycle_component_over X ξ)) (Fin r → ℂ),
      c.source = (properCycle_component_support_map X γ ξ hξ) ⁻¹' (O : Set _) ∧
      (∀ j, (f4_analytification (properCycle_component_over X ξ)).IsHolFun
        (fun u : c.source => c u j)) ∧
      ∀ u ∈ c.source, c u = (e (properCycle_component_support_map X γ ξ hξ u).val).1 := by
  let V := properCycle_component_over X ξ
  let f := properCycle_component_support_map X γ ξ hξ
  let i := properCycle_component_over_inclusion X ξ
  obtain ⟨c, hsrc, hval⟩ := properCycle_embedded_flat_chart (a3b4_an X.hom)
    (TopCat.of (ComplexPoint V)) (a3b4_cycleSupport X.hom γ) e 0 hflat f
    (properCycle_component_support_map_embedding X γ ξ hξ) O hOr hOe y hy
  refine ⟨c, hsrc, ?_, hval⟩
  intro j
  have hsub : c.source ⊆ Point.map i ⁻¹' e.source := by
    intro u hu
    have huO : f u ∈ O := by
      change u ∈ f ⁻¹' (O : Set _)
      rw [← hsrc]
      exact hu
    exact hOe (f u) huO
  have hcomp := (f4_map_isHom i).2 e.source e.open_source
    (fun u : e.source => (e u).1 j) (he.1 j)
  have hh := anb_isHolFun_restrict (f4_analytification V).atlas hsub hcomp
  convert hh using 1
  funext u
  exact congrArg (fun v : Fin r → ℂ => v j) (hval u.val u.property)

end HodgeLean.Foundations.QuotientDuality
