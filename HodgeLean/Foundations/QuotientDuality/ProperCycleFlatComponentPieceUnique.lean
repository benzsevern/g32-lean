import HodgeLean.Foundations.QuotientDuality.ProperCyclePurePrimeNoSpecialization
import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedFlatChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicChartComplement
import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteDimensionPredecessor
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! # Uniqueness of actual components containing an original flattened support piece
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace Topology HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Two original pure middle components containing the same nonempty open piece of an original flattened support chart are the same prime.
Source: properCycle_pure_prime_not_mem_closure; properCycle_chart_open_meets_algebraic_complement; properCycle_embedded_flat_chart.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_component_piece_unique
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (ξ η : γ.support) (d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin d → ℂ)))
    (hflat : ∀ x ∈ e.source, x ∈ a3b4_cycleSupport X.hom γ ↔ (e x).2 = 0)
    (O : Opens (TopCat.of (a3b4_cycleSupport X.hom γ))) (hO : (O : Set (a3b4_cycleSupport X.hom γ)).Nonempty)
    (hOe : ∀ s ∈ O, s.val ∈ e.source)
    (hOξ : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆ Set.range (properCycle_component_support_map X γ ξ.val ξ.property))
    (hOη : (O : Set (a3b4_cycleSupport X.hom γ)) ⊆ Set.range (properCycle_component_support_map X γ η.val η.property)) : ξ = η := by
  by_contra hneq
  have hξη : ξ.val ≠ η.val := fun h => hneq (Subtype.ext h)
  let Z := properCycle_component_over X ξ.val
  let f := properCycle_component_support_map X γ ξ.val ξ.property
  let i := cycleComponentι X.left ξ.val
  letI : CompactSpace Z.left := a3b4_compactSpace Z.hom
  letI : IsNoetherian Z.left := { __ := LocallyOfFiniteType.isLocallyNoetherian Z.hom }
  letI : T2Space (ComplexPoint Z) := f4_t2Space Z
  let B : Closeds Z.left := ⟨i ⁻¹' closure ({η.val} : Set X.left), isClosed_closure.preimage i.continuous⟩
  have hBproper : (B : Set Z.left) ≠ Set.univ := by
    intro hB
    have hz : genericPoint Z.left ∈ (B : Set Z.left) := by rw [hB]; trivial
    change cycleComponentι X.left ξ.val (genericPoint (cycleComponent X.left ξ.val)) ∈
      closure ({η.val} : Set X.left) at hz
    rw [properCycle_component_generic_point X.left ξ.val] at hz
    exact properCycle_pure_prime_not_mem_closure X.left k ξ.val η.val hξη
      (hc ξ.val ξ.property) (hc η.val η.property) hz
  have hZdim := properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property)
  have hBdim : topologicalKrullDim B ≤ (k-1 : ℕ) :=
    properCycle_dimension_le_pred_of_lt _ k
      (topologicalKrullDim_lt_of_isClosed_of_ne_univ B.isClosed hBproper hZdim.le)
  obtain ⟨z, hzO⟩ := hO
  obtain ⟨y, hy⟩ := hOξ hzO
  have hyO : f y ∈ O := by rw [hy]; exact hzO
  obtain ⟨c, hsrc, hval⟩ := properCycle_embedded_flat_chart (a3b4_an X.hom)
    (TopCat.of (ComplexPoint Z)) (a3b4_cycleSupport X.hom γ) e 0 hflat f
    (properCycle_component_support_map_embedding X γ ξ.val ξ.property) O hOξ hOe y hyO
  have hyc : y ∈ c.source := by rw [hsrc]; exact hyO
  obtain ⟨w, hw, hwB⟩ := properCycle_chart_open_meets_algebraic_complement Z B (k-1) hBdim
    k (by omega) c ⟨c.source, c.open_source⟩ ⟨y, hyc⟩ Set.Subset.rfl
  have hwO : f w ∈ O := by change w ∈ f ⁻¹' (O : Set (a3b4_cycleSupport X.hom γ)); rw [← hsrc]; exact hw
  have hwη := hOη hwO
  rw [properCycle_component_support_map_range] at hwη
  exact hwB hwη

end HodgeLean.Foundations.QuotientDuality
