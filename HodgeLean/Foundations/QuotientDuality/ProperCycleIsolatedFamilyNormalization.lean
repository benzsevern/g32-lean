import HodgeLean.Foundations.QuotientDuality.ProperCycleAbsentChartTerms
import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyComponentNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartRestriction
import HodgeLean.Adapters.NormalConeB4aGysinBridge2PrescribedChart

/-! # Actual local collected coefficients for arbitrary finite supported representatives -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Near an isolated common component, the actual weighted supported class has the collected component coefficient, including arbitrary family terms absent from that component.
Source: Fulton, Intersection Theory, sections 1.4, 1.5 and 19.1, finite collection and local cycle normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_weighted_isolated_component_chart_normalization
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (q : I → ℚ) (T : Set (ComplexPoint X))
    (hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hT : ∀ y ∈ e.source, y ∈ T ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (ξ : X.left) (hxξ : x.underlying ∈ closure ({ξ} : Set X.left))
    (hprime : ∀ y ∈ e.source, y.underlying ∈ closure ({ξ} : Set X.left) ↔ (e y).2 = 0)
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ →
      x.underlying ∉ closure ({η} : Set X.left)) :
    ∃ (W : Opens (ComplexPoint X)) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source), x ∈ W ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
        (SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hST a) =
      (∑ i, q i * γ i ξ) • chartNormalProjectionCoclass (Fin r → ℂ) k e T hT W hWe := by
  classical
  obtain ⟨O, hOe, hxO, hO⟩ := properCycle_family_component_neighborhood X γ ξ x hother
    (⟨e.source, e.open_source⟩ : Opens (ComplexPoint X)) hx
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have hx' : x ∈ e'.source := ⟨hx, hxO⟩
  have hT' : ∀ y ∈ e'.source, y ∈ T ↔ (e' y).2 = 0 := fun y hy => hT y hy.1
  have he' : a3b4_IsHolChart X.hom e' := a3b4g_isHolChart_restrOpen e he (O : Set (ComplexPoint X)) O.isOpen
  have hpresent (i : I) (_ : q i ≠ 0) (hxi : x ∈ a3b4_cycleSupport X.hom (γ i)) :
      (∀ y ∈ e'.source, y ∈ a3b4_cycleSupport X.hom (γ i) ↔ (e' y).2 = 0) ∧
        γ i ξ = a3b4_multiplicity X.hom (γ i) x := by
    have hξ := ((hO i x hxO).mp hxi).1
    refine ⟨?_, (a3b4a_classMultiplicity_eq_component X.hom (γ i) ξ hξ x hxξ (hother i)).symm⟩
    intro y hy
    exact (hO i y hy.2).trans ((and_iff_right hξ).trans (hprime y hy.1))
  have hmissing (i : I) (_ : q i ≠ 0) (hxi : x ∉ a3b4_cycleSupport X.hom (γ i)) :
      (∀ y ∈ e'.source, y ∉ a3b4_cycleSupport X.hom (γ i)) ∧ γ i ξ = 0 := by
    have hξ : ξ ∉ (γ i).support := fun h => hxi ((hO i x hxO).mpr ⟨h, hxξ⟩)
    refine ⟨fun y hy hyS => hξ ((hO i y hy.2).mp hyS).1, ?_⟩
    by_contra hn
    exact hξ hn
  obtain ⟨W, hWe', hxW, hW⟩ := properCycle_weighted_chart_normalization_with_absent_terms
    X k γ a ha q T hST r e' hT' he' x hx' (fun i => γ i ξ) hpresent hmissing
  refine ⟨W, fun y hy => (hWe' hy).1, hxW, hW.trans ?_⟩
  exact congrArg (fun c => (∑ i, q i * γ i ξ) • c)
    (properCycle_chart_normal_coclass_restrOpen k e T hT O W hWe')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A zero coefficient of the literal collected cycle forces the actual finite weighted supported restriction to vanish near an isolated component, including all absent family terms.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, rational coefficient collection and local cycle classes.
HC no distance; AV milestone no distance. -/
lemma properCycle_weighted_isolated_component_cancellation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (q : I → ℚ) (T : Set (ComplexPoint X))
    (hST : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hT : ∀ y ∈ e.source, y ∈ T ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (ξ : X.left) (hxξ : x.underlying ∈ closure ({ξ} : Set X.left))
    (hprime : ∀ y ∈ e.source, y.underlying ∈ closure ({ξ} : Set X.left) ↔ (e y).2 = 0)
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ →
      x.underlying ∉ closure ({η} : Set X.left))
    (hcancel : (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ξ = 0) :
    ∃ W : Opens (ComplexPoint X), x ∈ W ∧ (W : Set (ComplexPoint X)) ⊆ e.source ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) T)
        (SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hST a) = 0 := by
  classical
  obtain ⟨W, hWe, hxW, hW⟩ := properCycle_weighted_isolated_component_chart_normalization
    X k γ a ha q T hST r e hT he x hx ξ hxξ hprime hother
  have hsum : (∑ i, q i * γ i ξ) = 0 := by
    simpa only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply] using hcancel
  exact ⟨W, hxW, hWe, hW.trans (by rw [hsum, zero_smul])⟩

end HodgeLean.Foundations.QuotientDuality
