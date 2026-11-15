import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyRegularBoundary

/-! # Actual surviving collected components at family-isolated points -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Every nonzero collected component occurs in an actual active representative.
Source: Fulton, Intersection Theory, section 1.5, collection of rational cycle coefficients.
HC no distance; AV milestone no distance. -/
lemma properCycle_collected_component_occurs
    {X : Scheme.{0}} {I : Type} [Fintype I]
    (γ : I → AlgebraicCycle X ℚ) (q : I → ℚ) (ξ : X)
    (hξ : ξ ∈ (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support) :
    ∃ i, q i ≠ 0 ∧ ξ ∈ (γ i).support := by
  classical
  have hs : (∑ i, q i * γ i ξ) ≠ 0 := by
    change (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ξ ≠ 0 at hξ
    simpa only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.mapRange_apply] using hξ
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨i, left_ne_zero_of_mul hi, right_ne_zero_of_mul hi⟩

/-- At a family-isolated point in the collected support, the selected component survives collection and every other collected component misses the point.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1, component supports and collection.
HC no distance; AV milestone no distance. -/
lemma properCycle_collected_component_isolation
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (ξ : X.left) (x : ComplexPoint X)
    (hx : x ∈ a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)))
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ → x.underlying ∉ closure ({η} : Set X.left)) :
    ξ ∈ (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support ∧
      ∀ η ∈ (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support,
        η ≠ ξ → x.underlying ∉ closure ({η} : Set X.left) := by
  have hcol (η : X.left)
      (hη : η ∈ (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support)
      (hne : η ≠ ξ) : x.underlying ∉ closure ({η} : Set X.left) := by
    obtain ⟨i, _, hi⟩ := properCycle_collected_component_occurs γ q η hη
    exact hother i η hi hne
  refine ⟨?_, hcol⟩
  obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hx
  have he : η = ξ := by
    by_contra hn
    exact hcol η hη hn hxη
  exact he ▸ hη

end HodgeLean.Foundations.QuotientDuality
