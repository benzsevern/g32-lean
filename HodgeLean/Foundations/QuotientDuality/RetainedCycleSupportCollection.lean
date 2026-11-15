import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_weighted_support_subset (X : Over (Spec ↧ℂ))
    {I : Type*} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ) :
    a3b4_cycleSupport X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) ⊆
      ⋃ i, a3b4_cycleSupport X.hom (γ i) := by
  intro z hz
  change z.underlying ∈ ⋃ x ∈
    (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)).support, closure {x} at hz
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hx, hzx⟩ := Set.mem_iUnion.mp hx
  have hne : (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) x ≠ 0 := hx
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.mapRange_apply] at hne
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hγ : x ∈ (γ i).support := by
    intro hx0
    exact hi (by rw [hx0, mul_zero])
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change z.underlying ∈ ⋃ y ∈ (γ i).support, closure {y}
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hγ, hzx⟩⟩

theorem retained_prime_collection_support (X : Over (Spec ↧ℂ))
    {I : Type*} [Fintype I] (ξ : I → X.left) (q : I → ℚ) :
    a3b4_cycleSupport X.hom
        (∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)) ⊆
      ⋃ i, a3b4_cycleSupport X.hom (properPrime (ξ i)) :=
  retained_weighted_support_subset X (fun i => properPrime (ξ i)) q

end HodgeLean.Foundations.QuotientDuality
