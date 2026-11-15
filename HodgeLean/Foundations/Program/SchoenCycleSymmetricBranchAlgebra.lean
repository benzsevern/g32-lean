import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps

/-! # Branch equations in polynomial symmetric quotients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program
open MvPolynomial

/-- Distinct coordinate factors divide simultaneously with multiplicity one.
Source: Mathlib, MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero. -/
theorem s2e_coordinate_product_dvd
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (s : Finset σ) (p : MvPolynomial σ R)
    (h : ∀ i ∈ s, X i ∣ p) : (∏ i ∈ s, X i) ∣ p := by
  classical
  let a : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1
  have ha (i : σ) : a i = if i ∈ s then 1 else 0 := by
    simp [a, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have he : (∏ i ∈ s, (X i : MvPolynomial σ R)) = monomial a 1 := by
    exact (monomial_sum_one s (fun i => Finsupp.single i 1)).symm
  rw [he, monomial_one_dvd_iff_modMonomial_eq_zero]
  ext m
  change (modMonomial p a).coeff m = 0
  by_cases hle : a ≤ m
  · simp only [coeff_modMonomial_of_le p hle]
  · rw [coeff_modMonomial_of_not_le p hle]
    by_contra hm
    apply hle
    intro i
    rw [ha]
    by_cases hi : i ∈ s
    · rw [if_pos hi]
      obtain ⟨q, hq⟩ := h i hi
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      apply hm
      rw [hq, coeff_X_mul']
      simp only [Finsupp.mem_support_iff, hz, ne_eq, not_true_eq_false, if_false]
    · rw [if_neg hi]
      exact Nat.zero_le _

/-- Over any coefficient ring, an invariant equation vanishing on a root
hyperplane is divisible in the invariant ring by the top elementary coefficient.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_symmetric_root_divisible_over_ring
    (R σ : Type*) [CommRing R] [Fintype σ]
    (p : symmetricSubalgebra σ R) (i : σ)
    (hi : (X i : MvPolynomial σ R) ∣ (p : MvPolynomial σ R)) :
    (⟨esymm σ R (Fintype.card σ), esymm_isSymmetric σ R _⟩ :
      symmetricSubalgebra σ R) ∣ p := by
  classical
  have he : esymm σ R (Fintype.card σ) = ∏ j : σ, (X j : MvPolynomial σ R) := by
    unfold esymm
    rw [← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]
  have hall (j : σ) : (X j : MvPolynomial σ R) ∣ (p : MvPolynomial σ R) := by
    have hj := map_dvd (rename (Equiv.swap i j)).toRingHom hi
    change rename (Equiv.swap i j) (X i) ∣ rename (Equiv.swap i j) (p : MvPolynomial σ R) at hj
    simpa only [rename_X, Equiv.swap_apply_left, p.property (Equiv.swap i j)] using hj
  obtain ⟨q, hq⟩ := s2e_coordinate_product_dvd Finset.univ (p : MvPolynomial σ R)
    (fun j _ => hall j)
  have hs : IsSymmetric (∏ j : σ, (X j : MvPolynomial σ R)) := by
    rw [← he]
    exact esymm_isSymmetric σ R _
  have hqn : IsSymmetric q := by
    intro e
    apply (isRegular_prod_X (R := R) (Finset.univ : Finset σ)).left
    calc
      (∏ j : σ, (X j : MvPolynomial σ R)) * rename e q =
          rename e ((∏ j : σ, (X j : MvPolynomial σ R)) * q) := by rw [map_mul, hs e]
      _ = rename e (p : MvPolynomial σ R) := by rw [← hq]
      _ = (p : MvPolynomial σ R) := p.property e
      _ = (∏ j : σ, (X j : MvPolynomial σ R)) * q := hq
  refine ⟨⟨q, hqn⟩, ?_⟩
  apply Subtype.ext
  change (p : MvPolynomial σ R) = esymm σ R (Fintype.card σ) * q
  rw [he]
  exact hq

/-- The root hyperplane contracts to the top coefficient ideal over every base ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_symmetric_root_ideal_over_ring
    (R σ : Type*) [CommRing R] [Fintype σ] (i : σ) :
    (Ideal.span {(X i : MvPolynomial σ R)}).comap
      (symmetricSubalgebra σ R).val.toRingHom =
    Ideal.span {(⟨esymm σ R (Fintype.card σ), esymm_isSymmetric σ R _⟩ :
      symmetricSubalgebra σ R)} := by
  classical
  ext p
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · exact s2e_symmetric_root_divisible_over_ring R σ p i
  · intro h
    have hm := map_dvd (symmetricSubalgebra σ R).val.toRingHom h
    change esymm σ R (Fintype.card σ) ∣ (p : MvPolynomial σ R) at hm
    have hx : (X i : MvPolynomial σ R) ∣ esymm σ R (Fintype.card σ) := by
      have he : esymm σ R (Fintype.card σ) = ∏ j : σ, (X j : MvPolynomial σ R) := by
        unfold esymm
        rw [← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]
      rw [he]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact hx.trans hm

end HodgeLean.Foundations.Program
