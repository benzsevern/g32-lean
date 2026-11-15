import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps

/-! # Marked root divisibility in formal power series -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPowerSeries
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A monic formal monomial divides a series precisely when all coefficients
outside its upper exponent set vanish.
Source: Bourbaki, Commutative Algebra, Chapter III, §2;
Mathlib, MvPowerSeries.coeff_monomial_mul. -/
theorem s2e_powerSeries_monomial_dvd_iff
    {R σ : Type*} [CommRing R] (a : σ →₀ ℕ) (p : MvPowerSeries σ R) :
    monomial a (1 : R) ∣ p ↔ ∀ d, ¬ a ≤ d → coeff d p = 0 := by
  classical
  constructor
  · rintro ⟨q, rfl⟩ d hd
    rw [coeff_monomial_mul, if_neg hd]
  · intro h
    refine ⟨fun d => coeff (d + a) p, ?_⟩
    ext d
    rw [coeff_monomial_mul]
    split_ifs with hd
    · change coeff d p = 1 * coeff (d - a + a) p
      rw [tsub_add_cancel_of_le hd, one_mul]
    · exact h d hd

#print axioms s2e_powerSeries_monomial_dvd_iff
/-- Simultaneous divisibility by distinct formal coordinates implies
divisibility by their product, retaining multiplicity one.
Source: Bourbaki, Commutative Algebra, Chapter III, §2;
Mathlib, MvPowerSeries.X_dvd_iff. -/
theorem s2e_powerSeries_coordinate_product_dvd
    {R σ : Type*} [CommRing R] (s : Finset σ) (p : MvPowerSeries σ R)
    (h : ∀ i ∈ s, (X i : MvPowerSeries σ R) ∣ p) :
    (∏ i ∈ s, (X i : MvPowerSeries σ R)) ∣ p := by
  classical
  let a : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1
  have ha (i : σ) : a i = if i ∈ s then 1 else 0 := by
    simp [a, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have he : (∏ i ∈ s, (X i : MvPowerSeries σ R)) = monomial a 1 := by
    simpa only [X, Finset.prod_const_one] using prod_monomial (fun i => Finsupp.single i 1)
      (fun _ => (1 : R)) s
  rw [he, s2e_powerSeries_monomial_dvd_iff]
  intro d hd
  by_contra hm
  apply hd
  intro i
  rw [ha]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    exact hm ((X_dvd_iff.mp (h i hi)) d hz)
  · rw [if_neg hi]
    exact Nat.zero_le _

#print axioms s2e_powerSeries_coordinate_product_dvd
/-- Multiplication by a monic formal monomial is injective over any coefficient ring.
Source: Bourbaki, Commutative Algebra, Chapter III, §2;
Mathlib, MvPowerSeries.coeff_monomial_mul. -/
theorem s2e_powerSeries_monomial_mul_injective
    {R σ : Type*} [CommRing R] (a : σ →₀ ℕ) :
    Function.Injective (fun p : MvPowerSeries σ R => monomial a (1 : R) * p) := by
  intro p q h
  ext d
  have hc := congrArg (coeff (d + a)) h
  simpa only [coeff_monomial_mul, le_add_self, ite_true, add_tsub_cancel_right,
    one_mul] using hc

#print axioms s2e_powerSeries_monomial_mul_injective
/-- An invariant formal series divisible by one coordinate is the product of all
coordinates and an invariant formal series.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_powerSeries_symmetric_root_divisible
    {R σ : Type*} [CommRing R] [Fintype σ]
    (p : MvPowerSeries σ R) (hp : ∀ e : Equiv.Perm σ, rename e p = p)
    (i : σ) (hi : (X i : MvPowerSeries σ R) ∣ p) :
    ∃ q : MvPowerSeries σ R,
      (∀ e : Equiv.Perm σ, rename e q = q) ∧ p = (∏ j : σ, X j) * q := by
  classical
  have hall (j : σ) : (X j : MvPowerSeries σ R) ∣ p := by
    have hj := map_dvd (rename (Equiv.swap i j)).toRingHom hi
    change rename (Equiv.swap i j) (X i) ∣ rename (Equiv.swap i j) p at hj
    simpa only [rename_X, Equiv.swap_apply_left, hp] using hj
  obtain ⟨q, hq⟩ := s2e_powerSeries_coordinate_product_dvd Finset.univ p
    (fun j _ => hall j)
  have hs (e : Equiv.Perm σ) :
      rename e (∏ j : σ, (X j : MvPowerSeries σ R)) = ∏ j : σ, X j := by
    simp only [map_prod, rename_X]
    exact Equiv.prod_comp e (fun j => (X j : MvPowerSeries σ R))
  have he : (∏ j : σ, (X j : MvPowerSeries σ R)) =
      monomial (∑ j : σ, Finsupp.single j 1) 1 := by
    simpa only [X, Finset.prod_const_one] using prod_monomial
      (fun j : σ => Finsupp.single j 1) (fun _ => (1 : R)) Finset.univ
  refine ⟨q, ?_, hq⟩
  intro e
  apply s2e_powerSeries_monomial_mul_injective (∑ j : σ, Finsupp.single j 1)
  change monomial _ (1 : R) * rename e q = monomial _ (1 : R) * q
  rw [← he]
  calc
    (∏ j : σ, X j) * rename e q = rename e ((∏ j : σ, X j) * q) := by
      rw [map_mul, hs]
    _ = rename e p := by rw [← hq]
    _ = p := hp e
    _ = (∏ j : σ, X j) * q := hq

#print axioms s2e_powerSeries_symmetric_root_divisible
/-- A ring identified with formal permutation invariants contracts a marked
coordinate ideal to the principal ideal of the product of all coordinates.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_powerSeries_invariant_root_ideal
    {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ]
    (f : S →+* MvPowerSeries σ R) (hf : Function.Injective f)
    (hfix : ∀ (s : S) (e : Equiv.Perm σ), rename e (f s) = f s)
    (hdesc : ∀ p : MvPowerSeries σ R,
      (∀ e : Equiv.Perm σ, rename e p = p) → ∃ s, f s = p)
    (c : S) (hc : f c = ∏ j : σ, X j) (i : σ) :
    (Ideal.span {(X i : MvPowerSeries σ R)}).comap f = Ideal.span {c} := by
  classical
  ext s
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · intro hs
    obtain ⟨q, hq, he⟩ := s2e_powerSeries_symmetric_root_divisible
      (f s) (hfix s) i hs
    obtain ⟨b, hb⟩ := hdesc q hq
    refine ⟨b, hf ?_⟩
    rw [map_mul, hc, hb, he]
  · rintro ⟨b, rfl⟩
    rw [map_mul, hc]
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _

#print axioms s2e_powerSeries_invariant_root_ideal
end HodgeLean.Foundations.Program
