import HodgeLean.Foundations.QuotientDuality.ProperCycleChartCycleNormalization
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Actual tangential dimension in the frozen flattened chart hypotheses -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original local homology vanishing hypothesis forces every actual codimension-k flattened chart in ambient complex dimension twice k to have exactly k tangential complex coordinates.
Source: Hatcher, Algebraic Topology, section 2.2, local homology and invariance of dimension.
HC no distance; AV milestone no distance. -/
lemma properCycle_flattened_chart_tangent_dimension
    (X : TopCat.{0}) [T1Space X] (k r : ℕ)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : X, Subsingleton (orientationGroup X j x))
    (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin k → ℂ)))
    (x : X) (hx : x ∈ e.source) : r = k := by
  let L : ((Fin r → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (r + k) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hφ : x ∈ φ.source := by
    change x ∈ e.source ∩ e ⁻¹' Set.univ
    exact ⟨hx, Set.mem_univ _⟩
  let c := localClassOfChart (r + k) φ x hφ
  have hc : c ≠ 0 := localClassOfChart_ne_zero (r + k) φ x hφ
  by_contra h
  have hdeg : 2 * (r + k) ≠ 2 * (2 * k) := by omega
  exact hc ((hvan (2 * (r + k)) hdeg x).elim c 0)

end HodgeLean.Foundations.QuotientDuality
