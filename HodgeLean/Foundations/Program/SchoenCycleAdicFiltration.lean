import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Comparing cofinal ideal filtrations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A monotone reindexing of ideal powers induces a map of adic rings.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, AdicCompletion.liftRingHom. -/
def s2e_adic_filtration_map
    {R : Type*} [CommRing R] (I J : Ideal R)
    (a : ℕ → ℕ) (ha : Monotone a) (h : ∀ n, I ^ a n ≤ J ^ n) :
    AdicCompletion I R →+* AdicCompletion J R :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.Quotient.factor (h n)).comp (AdicCompletion.evalₐ I (a n)).toRingHom)
    (by
      intro m n hmn
      apply RingHom.ext
      intro x
      change Ideal.Quotient.factorPow J hmn
        (Ideal.Quotient.factor (h n) (AdicCompletion.evalₐ I (a n) x)) =
          Ideal.Quotient.factor (h m) (AdicCompletion.evalₐ I (a m) x)
      induction x using AdicCompletion.induction_on I R with
      | h x =>
        simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
          Ideal.Quotient.factorPow] using
          congrArg (Ideal.Quotient.factor (h m))
            (AdicCompletion.Ideal.mk_eq_mk I (ha hmn) x))

#print axioms s2e_adic_filtration_map

/-- Evaluation of a reindexed adic map is its specified quotient factor.
Source: Mathlib, AdicCompletion.evalₐ_liftRingHom. -/
theorem s2e_adic_filtration_map_eval
    {R : Type*} [CommRing R] (I J : Ideal R)
    (a : ℕ → ℕ) (ha : Monotone a) (h : ∀ n, I ^ a n ≤ J ^ n)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (s2e_adic_filtration_map I J a ha h x) =
      Ideal.Quotient.factor (h n) (AdicCompletion.evalₐ I (a n) x) := by
  unfold s2e_adic_filtration_map
  generalize_proofs
  apply AdicCompletion.evalₐ_liftRingHom
  assumption

#print axioms s2e_adic_filtration_map_eval

/-- Nested ideals containing a power of one another have equivalent adic rings,
with the equivalence preserving the image of the original ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_equiv_of_power_le
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (k : ℕ) (hk : 0 < k) (hJI : J ^ k ≤ I) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J R,
      ∀ r, E (AdicCompletion.of I R r) = AdicCompletion.of J R r := by
  have hI : ∀ n : ℕ, I ^ n ≤ J ^ n := fun n => pow_le_pow_left' hIJ n
  have hJ : ∀ n : ℕ, J ^ (k * n) ≤ I ^ n := by
    intro n
    rw [pow_mul]
    exact pow_le_pow_left' hJI n
  have hm : Monotone (fun n : ℕ => k * n) := fun _ _ h => Nat.mul_le_mul_left k h
  have hn : ∀ n : ℕ, n ≤ k * n := fun n => by
    simpa using Nat.mul_le_mul_right n hk
  let f := s2e_adic_filtration_map I J id monotone_id hI
  let g := s2e_adic_filtration_map J I (fun n => k * n) hm hJ
  have hgf : Function.LeftInverse g f := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    dsimp only [f, g]
    rw [s2e_adic_filtration_map_eval, s2e_adic_filtration_map_eval]
    induction x using AdicCompletion.induction_on I R with
    | h x =>
      simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, id_eq] using
        AdicCompletion.Ideal.mk_eq_mk I (hn n) x
  have hfg : Function.RightInverse g f := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    dsimp only [f, g]
    rw [s2e_adic_filtration_map_eval, s2e_adic_filtration_map_eval]
    induction x using AdicCompletion.induction_on J R with
    | h x =>
      simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, id_eq] using
        AdicCompletion.Ideal.mk_eq_mk J (hn n) x
  refine ⟨{ f with invFun := g, left_inv := hgf, right_inv := hfg }, ?_⟩
  intro r
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n (f (AdicCompletion.of I R r)) = _
  dsimp only [f]
  rw [s2e_adic_filtration_map_eval]
  simp only [AdicCompletion.evalₐ_of, Ideal.Quotient.factor_mk]

#print axioms s2e_adic_equiv_of_power_le

/-- An ideal and its finitely generated radical have equivalent adic rings.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, Ideal.exists_radical_pow_le_of_fg. -/
theorem s2e_adic_equiv_radical
    {R : Type*} [CommRing R] (I : Ideal R) (hfg : I.radical.FG) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion I.radical R,
      ∀ r, E (AdicCompletion.of I R r) = AdicCompletion.of I.radical R r := by
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg I hfg
  exact s2e_adic_equiv_of_power_le I I.radical Ideal.le_radical (k + 1)
    (Nat.zero_lt_succ k) ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)

#print axioms s2e_adic_equiv_radical
/-- The canonical map between nested cofinal ideal filtrations is bijective.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_ring_map_bijective_of_power_le
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (k : ℕ) (hk : 0 < k) (hJI : J ^ k ≤ I) :
    Function.Bijective (s2e_adic_ring_map I J (RingHom.id R)
      (by simpa using hIJ)) := by
  have hI : ∀ n : ℕ, I ^ n ≤ J ^ n := fun n => pow_le_pow_left' hIJ n
  have hJ : ∀ n : ℕ, J ^ (k * n) ≤ I ^ n := by
    intro n
    rw [pow_mul]
    exact pow_le_pow_left' hJI n
  have hm : Monotone (fun n : ℕ => k * n) := fun _ _ h => Nat.mul_le_mul_left k h
  have hn : ∀ n : ℕ, n ≤ k * n := fun n => by
    simpa using Nat.mul_le_mul_right n hk
  let f := s2e_adic_ring_map I J (RingHom.id R) (by simpa using hIJ)
  let g := s2e_adic_filtration_map J I (fun n => k * n) hm hJ
  have hgf : Function.LeftInverse g f := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    dsimp only [f, g]
    rw [s2e_adic_filtration_map_eval, s2e_adic_ring_map_eval]
    induction x using AdicCompletion.induction_on I R with
    | h x =>
      simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, s2e_adic_quotient_ring_map, Ideal.quotientMap_mk, RingHom.id_apply] using
        AdicCompletion.Ideal.mk_eq_mk I (hn n) x
  have hfg : Function.RightInverse g f := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    dsimp only [f, g]
    rw [s2e_adic_ring_map_eval, s2e_adic_filtration_map_eval]
    induction x using AdicCompletion.induction_on J R with
    | h x =>
      simpa only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, s2e_adic_quotient_ring_map, Ideal.quotientMap_mk, RingHom.id_apply] using
        AdicCompletion.Ideal.mk_eq_mk J (hn n) x
  exact ⟨hgf.injective, hfg.surjective⟩

#print axioms s2e_adic_ring_map_bijective_of_power_le
/-- The canonical map to the adic ring of a finitely generated radical is bijective.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, Ideal.exists_radical_pow_le_of_fg. -/
theorem s2e_adic_ring_map_radical_bijective
    {R : Type*} [CommRing R] (I : Ideal R) (hfg : I.radical.FG) :
    Function.Bijective (s2e_adic_ring_map I I.radical (RingHom.id R)
      (by simpa using (Ideal.le_radical : I ≤ I.radical))) := by
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg I hfg
  exact s2e_adic_ring_map_bijective_of_power_le I I.radical Ideal.le_radical
    (k + 1) (Nat.zero_lt_succ k)
    ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)

#print axioms s2e_adic_ring_map_radical_bijective
end HodgeLean.Foundations.Program
