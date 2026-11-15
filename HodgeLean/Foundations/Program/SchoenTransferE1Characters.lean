import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

/-! Sum-zero character algebra over an arbitrary commutative ring. -/

open scoped BigOperators

namespace HodgeLean.Foundations.Program

/-- A coefficient tuple annihilates the sum-zero tuples exactly when it is constant.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism,
Lemma 1.2, pp. 5–6; the test tuples have entries one and minus one. -/
theorem s4_e1_sum_zero_character_algebra
    {ι R : Type*} [Fintype ι] [Nonempty ι] [CommRing R] (c : ι → R) :
    (∀ v : ι → R, (∑ i, v i) = 0 → (∑ i, c i * v i) = 0) ↔
      ∃ a : R, ∀ i, c i = a := by
  classical
  constructor
  · intro hc
    let j : ι := Classical.choice inferInstance
    refine ⟨c j, fun i => ?_⟩
    have hi := hc (fun k => (if k = i then 1 else 0) -
      (if k = j then 1 else 0)) (by simp [Finset.sum_sub_distrib])
    have he : c i - c j = 0 := by
      simpa only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hi
    exact sub_eq_zero.mp he
  · rintro ⟨a, ha⟩ v hv
    simp only [ha, ← Finset.mul_sum, hv, mul_zero]

/-- A zero coefficient forces every coefficient to vanish when the tuple
annihilates all sum-zero tuples.
Source: Schoen (1988), Lemma 1.2, pp. 5–6, the equal-character test. -/
theorem s4_e1_zero_coordinate_characters
    {ι R : Type*} [Fintype ι] [CommRing R] (c : ι → R) (j : ι)
    (hj : c j = 0)
    (hc : ∀ v : ι → R, (∑ i, v i) = 0 → (∑ i, c i * v i) = 0) :
    ∀ i, c i = 0 := by
  letI : Nonempty ι := ⟨j⟩
  obtain ⟨a, ha⟩ := (s4_e1_sum_zero_character_algebra c).mp hc
  intro i
  exact (ha i).trans ((ha j).symm.trans hj)

#print axioms s4_e1_sum_zero_character_algebra
#print axioms s4_e1_zero_coordinate_characters

end HodgeLean.Foundations.Program
