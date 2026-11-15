import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
open UniqueFactorizationMonoid
namespace HodgeLean.Foundations.Program

/-- Divisibility of all prime orders gives a power up to a unit in a factorial domain. -/
theorem s2v_l1b_divisor_power_of_orders
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a : R) (ha : a ≠ 0) (m : ℕ)
    (hm : ∀ p : R, Prime p → m ∣ (emultiplicity p a).toNat) :
    ∃ (ε : Rˣ) (c : R), c ≠ 0 ∧ a = (ε : R) * c ^ m := by
  classical
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  let f := normalizedFactors a
  let c : R := ∏ p ∈ f.toFinset, p ^ (f.count p / m)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors
      (Multiset.mem_toFinset.mp hp))
  have hd (p : R) (hp : p ∈ f.toFinset) : m ∣ f.count p := by
    have hmem : p ∈ normalizedFactors a := Multiset.mem_toFinset.mp hp
    have hh := hm p (UniqueFactorizationMonoid.prime_of_normalized_factor p hmem)
    rwa [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (UniqueFactorizationMonoid.prime_of_normalized_factor p hmem).irreducible ha,
      UniqueFactorizationMonoid.normalize_normalized_factor p hmem, ENat.toNat_natCast] at hh
  have hpow : c ^ m = f.prod := by
    change (∏ p ∈ f.toFinset, p ^ (f.count p / m)) ^ m = f.prod
    rw [← Finset.prod_pow]
    conv_rhs => rw [← f.map_id, Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← pow_mul, Nat.div_mul_cancel (hd p hp)]
    rfl
  obtain ⟨ε, hε⟩ := UniqueFactorizationMonoid.prod_normalizedFactors ha
  exact ⟨ε, c, hc, by rw [← hε, ← hpow]; ring⟩

end HodgeLean.Foundations.Program
