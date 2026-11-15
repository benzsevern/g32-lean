import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Coordinate divisibility under flat parameter maps

Implication from flatness to preservation of the coordinate divisibility
calculation used for the insertion ideal.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Under a flat algebra map, simultaneous divisibility by the images of
relatively prime source elements implies divisibility by their product.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2, flatness and finite relations. -/
theorem s2v_l1a_flat_coprime_divisibility
    {R B : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    (p q : R) (hpq : IsRelPrime p q) (x : B)
    (hp : algebraMap R B p ∣ x) (hq : algebraMap R B q ∣ x) :
    algebraMap R B (p * q) ∣ x := by
  obtain ⟨b, hb⟩ := hp
  obtain ⟨c, hc⟩ := hq
  let f : Fin 2 → R := ![p, -q]
  let y : Fin 2 → B := ![b, c]
  have hrel : ∑ i, f i • y i = 0 := by
    simp only [Fin.sum_univ_two, f, y, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, map_neg, neg_mul]
    rw [← sub_eq_add_neg, ← hb, ← hc, sub_self]
  obtain ⟨k, a, t, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hqa (j : Fin k) : q ∣ a 0 j := by
    have H : p * a 0 j - q * a 1 j = 0 := by
      simpa only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one,
        neg_mul, sub_eq_add_neg] using ha j
    apply hpq.symm.dvd_of_dvd_mul_left
    exact ⟨a 1 j, sub_eq_zero.mp H⟩
  have hqb : algebraMap R B q ∣ b := by
    rw [show b = ∑ j, a 0 j • t j from hy 0]
    apply Finset.dvd_sum
    intro j _
    rw [Algebra.smul_def]
    exact dvd_mul_of_dvd_left (map_dvd (algebraMap R B) (hqa j)) _
  obtain ⟨r, hr⟩ := hqb
  refine ⟨r, ?_⟩
  rw [hb, hr, map_mul, mul_assoc]

/-- Flat parameter extension preserves simultaneous divisibility by a finite
family of pairwise relatively prime source coordinates.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2, flatness and finite relations. -/
theorem s2v_l1a_flat_pairwise_product_divisibility
    {R B ι : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [DecidableEq ι]
    (f : ι → R) (hrel : Pairwise (fun i j => IsRelPrime (f i) (f j)))
    (s : Finset ι) (x : B) (hdiv : ∀ i ∈ s, algebraMap R B (f i) ∣ x) :
    algebraMap R B (∏ i ∈ s, f i) ∣ x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, map_one, one_dvd]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      apply s2v_l1a_flat_coprime_divisibility
      · apply IsRelPrime.prod_right
        intro j hj
        exact hrel (by intro h; subst j; exact hi hj)
      · exact hdiv i (Finset.mem_insert_self i s)
      · exact ih (fun j hj => hdiv j (Finset.mem_insert_of_mem hj))

end HodgeLean.Foundations.Program
