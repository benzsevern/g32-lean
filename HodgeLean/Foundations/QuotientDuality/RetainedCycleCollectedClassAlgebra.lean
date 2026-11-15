import HodgeLean.Foundations.QuotientDuality.RetainedCycleSupportCollection

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators Classical
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual coefficient of a weighted prime collection is the sum over precisely its repeated occurrences. -/
theorem retained_prime_collection_coefficient (X : Over (Spec ↧ℂ))
    {I : Type*} [Fintype I] (ξ : I → X.left) (q : I → ℚ) (x : X.left) :
    (∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)) x =
      ∑ i with ξ i = x, q i := by
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.mapRange_apply, properPrime,
    Function.locallyFinsuppWithin.single_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ξ i = x
  · subst x
    simp only [ite_true, mul_one]
  · simp only [h, Ne.symm h, ite_false, mul_zero]

/-- A weighted family constant on repeated prime indices cancels whenever every collected coefficient vanishes. -/
theorem retained_weighted_family_zero_of_coefficients
    {I P M : Type*} [Fintype I] [AddCommGroup M] [Module ℚ M]
    (ξ : I → P) (q : I → ℚ) (v : I → M)
    (hv : ∀ i j, ξ i = ξ j → v i = v j)
    (hq : ∀ x, (∑ i with ξ i = x, q i) = 0) :
    ∑ i, q i • v i = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image ξ)
    (fun i hi => Finset.mem_image_of_mem ξ hi) (fun i => q i • v i)]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  calc
    ∑ j with ξ j = ξ i, q j • v j = ∑ j with ξ j = ξ i, q j • v i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hv j i (Finset.mem_filter.mp hj).2]
    _ = (∑ j with ξ j = ξ i, q j) • v i := Finset.sum_smul.symm
    _ = 0 := by rw [hq, zero_smul]

/-- Weighted values constant on repeated primes depend only on the literal collected algebraic cycle. -/
theorem retained_weighted_family_eq_of_prime_collection
    (X : Over (Spec ↧ℂ)) {I M : Type*} [Fintype I]
    [AddCommGroup M] [Module ℚ M]
    (ξ : I → X.left) (q r : I → ℚ) (v : I → M)
    (hv : ∀ i j, ξ i = ξ j → v i = v j)
    (hγ : (∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)) =
      ∑ i, (properPrime (ξ i)).mapRange (r i * ·) (mul_zero _)) :
    ∑ i, q i • v i = ∑ i, r i • v i := by
  have hq (x : X.left) : (∑ i with ξ i = x, (q i - r i)) = 0 := by
    have hx := congrArg (fun γ : AlgebraicCycle X.left ℚ => γ x) hγ
    rw [retained_prime_collection_coefficient, retained_prime_collection_coefficient] at hx
    rw [Finset.sum_sub_distrib, hx, sub_self]
  have hz := retained_weighted_family_zero_of_coefficients ξ (fun i => q i - r i) v hv hq
  simpa only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using hz

/-- A zero actual collected prime cycle annihilates every weighted family constant on its repeated primes. -/
theorem retained_weighted_family_zero_of_prime_collection
    (X : Over (Spec ↧ℂ)) {I M : Type*} [Fintype I]
    [AddCommGroup M] [Module ℚ M]
    (ξ : I → X.left) (q : I → ℚ) (v : I → M)
    (hv : ∀ i j, ξ i = ξ j → v i = v j)
    (hγ : (∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)) = 0) :
    ∑ i, q i • v i = 0 := by
  apply retained_weighted_family_zero_of_coefficients ξ q v hv
  intro x
  have hx := congrArg (fun γ : AlgebraicCycle X.left ℚ => γ x) hγ
  rw [retained_prime_collection_coefficient] at hx
  exact hx

end HodgeLean.Foundations.QuotientDuality
