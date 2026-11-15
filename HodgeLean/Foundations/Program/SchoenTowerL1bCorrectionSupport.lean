import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRescaling
import Mathlib.Data.Int.ModEq

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid

/-- A product over distinct normalized primes has the prescribed orders. -/
theorem s2v_l1b_orders_prime_product
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R] (s : Finset R)
    (hs : ∀ q ∈ s, Prime q ∧ normalize q = q) (f : R → ℕ)
    (p : R) (hp : Prime p) :
    emultiplicity p (∏ q ∈ s, q ^ f q) =
      if normalize p ∈ s then (f (normalize p) : ℕ∞) else 0 := by
  classical
  rw [Finset.emultiplicity_prod hp]
  have he (q : R) (hq : q ∈ s) :
      emultiplicity p q = if normalize p = q then 1 else 0 := by
    rw [emultiplicity_eq_count_normalizedFactors hp.irreducible (hs q hq).1.ne_zero,
      normalizedFactors_irreducible (hs q hq).1.irreducible, (hs q hq).2]
    simp only [Multiset.count_singleton]
    split_ifs <;> simp_all
  simp_rw [emultiplicity_pow hp]
  trans ∑ q ∈ s, if normalize p = q then (f q : ℕ∞) else 0
  · apply Finset.sum_congr rfl
    intro q hq
    rw [he q hq]
    split_ifs <;> simp
  · simp

/-- Congruent natural orders are balanced by nonnegative quotient corrections. -/
theorem s2v_l1b_balance_orders (A B m : ℕ) (h : Nat.ModEq m A B) :
    A + m * ((B - A) / m) = B + m * ((A - B) / m) := by
  rcases le_total A B with hab | hba
  · have hd := Nat.mul_div_cancel' h.dvd'
    rw [Nat.sub_eq_zero_of_le hab, Nat.zero_div, mul_zero, add_zero, hd]
    omega
  · have hd := Nat.mul_div_cancel' h.symm.dvd'
    rw [Nat.sub_eq_zero_of_le hba, Nat.zero_div, mul_zero, add_zero, hd]
    omega

/-- Finite prime support realizes the rational corrections prescribed by residue agreement. -/
theorem s2v_l1b_construct_corrections
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {J : Type*} [Fintype J] (g : J → R) (n : J → ℕ)
    (a b : R) (m : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hg : ∀ j, g j ≠ 0)
    (hv : ∀ p : R, Prime p →
      Int.ModEq (m : ℤ) ((emultiplicity p a).toNat : ℤ)
        (((emultiplicity p b).toNat : ℤ) +
          ∑ j, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ))) :
    ∃ c d : R, c ≠ 0 ∧ d ≠ 0 ∧
      ∀ p : R, Prime p →
        emultiplicity p a + (m : ℕ∞) * emultiplicity p d =
          emultiplicity p b + (m : ℕ∞) * emultiplicity p c +
            ∑ j, (n j : ℕ∞) * emultiplicity p (g j) := by
  classical
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s : Finset R := (normalizedFactors a).toFinset ∪ (normalizedFactors b).toFinset ∪
    Finset.univ.biUnion (fun j => (normalizedFactors (g j)).toFinset)
  let A : R → ℕ := fun p => (normalizedFactors a).count p
  let B : R → ℕ := fun p => (normalizedFactors b).count p +
    ∑ j, n j * (normalizedFactors (g j)).count p
  let c := ∏ q ∈ s, q ^ ((A q - B q) / m)
  let d := ∏ q ∈ s, q ^ ((B q - A q) / m)
  have hs (q : R) (hq : q ∈ s) : Prime q ∧ normalize q = q := by
    have hfactor {x : R} (hx : q ∈ (normalizedFactors x).toFinset) :
        Prime q ∧ normalize q = q :=
      ⟨prime_of_normalized_factor q (Multiset.mem_toFinset.mp hx),
        normalize_normalized_factor q (Multiset.mem_toFinset.mp hx)⟩
    simp only [s, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hq
    rcases hq with (hq | hq) | ⟨j, hq⟩
    · exact hfactor hq
    · exact hfactor hq
    · exact hfactor hq
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq =>
    pow_ne_zero _ (hs q hq).1.ne_zero
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq =>
    pow_ne_zero _ (hs q hq).1.ne_zero
  refine ⟨c, d, hc, hd, ?_⟩
  intro p hp
  have he {x : R} (hx : x ≠ 0) :
      emultiplicity p x = ((normalizedFactors x).count (normalize p) : ℕ∞) :=
    emultiplicity_eq_count_normalizedFactors hp.irreducible hx
  have hC := s2v_l1b_orders_prime_product s hs (fun q => (A q - B q) / m) p hp
  have hD := s2v_l1b_orders_prime_product s hs (fun q => (B q - A q) / m) p hp
  change emultiplicity p c = _ at hC
  change emultiplicity p d = _ at hD
  rw [hC, hD, he ha, he hb]
  simp_rw [he (hg _)]
  have hcong : Nat.ModEq m (A (normalize p)) (B (normalize p)) := by
    apply Int.natCast_modEq_iff.mp
    simpa [A, B, he ha, he hb, he (hg _)] using hv p hp
  have hbalance := s2v_l1b_balance_orders _ _ _ hcong
  by_cases hmem : normalize p ∈ s
  · simp only [if_pos hmem]
    norm_cast
    dsimp only [A, B] at hbalance ⊢
    omega
  · have hz {x : R} (hx : (normalizedFactors x).toFinset ⊆ s) :
        (normalizedFactors x).count (normalize p) = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hh
      exact hmem (hx (Multiset.mem_toFinset.mpr hh))
    have ha0 : A (normalize p) = 0 := hz (by intro q hq; simp [s, hq])
    have hb0 : (normalizedFactors b).count (normalize p) = 0 :=
      hz (by intro q hq; simp [s, hq])
    have hg0 (j : J) : (normalizedFactors (g j)).count (normalize p) = 0 :=
      hz (by intro q hq; simp only [s, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_univ, true_and]; exact Or.inr ⟨j, hq⟩)
    simp only [if_neg hmem, mul_zero, add_zero]
    simp [A] at ha0
    simp [ha0, hb0, hg0]

end HodgeLean.Foundations.Program
