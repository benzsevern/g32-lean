import HodgeLean.Foundations.QuotientDuality.RetainedCycleWeightedCarrier
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothCollectedDescent
import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroCollectedDescent

/-! Exact finite collection with the full family carrier in smooth ambient schemes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
namespace HodgeLean.Foundations.QuotientDuality

/-- In dimension zero the unique point chart supplies the component-chart data for every cycle. -/
lemma retained_zero_dimension_cycle_charts
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (γ : AlgebraicCycle X.left ℚ) (ξ : X.left) (hξ : ξ ∈ γ.support) :
    ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin 0 → ℂ)))
      (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0),
      a3b4_IsHolChart X.hom e ∧ ∃ z : ComplexPoint X,
        z ∈ e.source ∧ z ∈ a3b4_cycleSupport X.hom γ ∧
        Point.underlying z ∈ closure {ξ} ∧
        ∀ ζ ∈ γ.support, Point.underlying z ∈ closure {ζ} → ζ = ξ := by
  letI : Subsingleton (ComplexPoint X) := properCycle_zero_dimension_complex_subsingleton X hdim
  letI : Unique (ComplexPoint X) :=
    { default := Classical.choice (properCycle_zero_dimension_complex_nonempty X hdim)
      uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  let e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
    (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
  have hγ : γ ≠ 0 := by
    intro h
    exact hξ (by rw [h]; rfl)
  have hwhole := properCycle_zero_dimension_nonzero_support X hdim γ hγ
  refine ⟨0, e, ?_, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
    default, Set.mem_univ _, ?_, ?_, ?_⟩
  · intro z _
    exact iff_of_true (by rw [hwhole]; trivial) (Subsingleton.elim _ _)
  · rw [hwhole]
    trivial
  · rw [properCycle_zero_dimension_point_eq_generic X hdim ξ]
    exact specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp le_top)
  · intro ζ _ _
    exact (properCycle_zero_dimension_point_eq_generic X hdim ζ).trans
      (properCycle_zero_dimension_point_eq_generic X hdim ξ).symm

end HodgeLean.Foundations.QuotientDuality
