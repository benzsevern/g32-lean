import HodgeLean.Foundations.MeyerRationalS2
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ChineseRemainder

/-! A rational selector with prescribed local square classes and real sign. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

instance prime_fact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

theorem square_quotient_of_residue (p : ℕ) [Fact p.Prime]
    (u v : ℤ_[p]) (hu : IsUnit u)
    (h : PadicInt.toZModPow 3 v = PadicInt.toZModPow 3 u) :
    IsSquare ((v : ℚ_[p]) / (u : ℚ_[p])) := by
  have hker : v - u ∈ Ideal.span {(p : ℤ_[p]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  have hn := (PadicInt.norm_le_pow_iff_mem_span_pow (v - u) 3).mpr hker
  have hu1 := PadicInt.isUnit_iff.mp hu
  have hu0 : (u : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  apply (square_of_near_one p _ ?_).2
  rw [div_sub_one hu0, norm_div, PadicInt.norm_coe, hu1, div_one,
    ← PadicInt.coe_sub, PadicInt.norm_coe]
  apply hn.trans_lt
  by_cases hp : p = 2
  · subst p
    rw [show ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ from PadicInt.norm_p]
    norm_num
  · have ht : ‖(2 : ℤ_[p])‖ = 1 :=
      PadicInt.norm_natCast_eq_one_iff.mpr
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
          hp ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
            (Fact.out : p.Prime).ne_one)))
    rw [ht, one_pow]
    exact zpow_lt_one_of_neg₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt) (by norm_num)

theorem prime_prescribed_residues (S : Finset Nat.Primes)
    (u : (p : Nat.Primes) → ℤ_[p.val]) (hu : ∀ p ∈ S, IsUnit (u p)) :
    ∃ ell : Nat.Primes, ell ∉ S ∧
      ∀ p ∈ S, PadicInt.toZModPow 3 (ell.val : ℤ_[p.val]) =
        PadicInt.toZModPow 3 (u p) := by
  classical
  let a : Nat.Primes → ℕ := fun p => (PadicInt.toZModPow 3 (u p)).val
  let m : Nat.Primes → ℕ := fun p => p.val ^ 3
  have hm : ∀ p ∈ S, m p ≠ 0 := fun p _ => pow_ne_zero _ p.property.ne_zero
  have hpair : Set.Pairwise (↑S : Set Nat.Primes) (fun p q => (m p).Coprime (m q)) := by
    intro p _ q _ hpq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h))
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset a m S hm hpair
  have hcop : r.Coprime (∏ p ∈ S, m p) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    apply (ZMod.isUnit_iff_coprime r (m p)).mp
    have heq : (r : ZMod (m p)) = (a p : ZMod (m p)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hr p hp)
    rw [heq]
    change IsUnit ((PadicInt.toZModPow 3 (u p)).val : ZMod (p.val ^ 3))
    simpa using (hu p hp).map (PadicInt.toZModPow 3)
  obtain ⟨ell, hlarge, hell, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (S.sup (fun p : Nat.Primes => p.val)) (Finset.prod_ne_zero_iff.mpr hm) hcop
  refine ⟨⟨ell, hell⟩, ?_, ?_⟩
  · intro hmem
    exact (not_le_of_gt hlarge) (Finset.le_sup (f := (fun p : Nat.Primes => p.val)) hmem)
  · intro p hp
    have hmod' := (hmod.of_dvd (Finset.dvd_prod_of_mem m hp)).trans (hr p hp)
    simpa [a, m] using (ZMod.natCast_eq_natCast_iff ell (a p) (m p)).mpr hmod'

theorem prime_valuation (p q : Nat.Primes) :
    padicValRat p.val (q.val : ℚ) = if p = q then 1 else 0 := by
  classical
  by_cases h : p = q
  · subst q
    simp [padicValRat.self p.property.one_lt]
  · rw [ite_eq_right h, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · rfl
    · intro hd
      exact h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hd))

theorem product_valuation (p : Nat.Primes) (S : Finset Nat.Primes)
    (f : Nat.Primes → ℚ) (hf : ∀ q ∈ S, f q ≠ 0) :
    padicValRat p.val (∏ q ∈ S, f q) = ∑ q ∈ S, padicValRat p.val (f q) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq, padicValRat.mul
      (hf q (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun r hr => hf r (Finset.mem_insert_of_mem hr))),
      ih (fun r hr => hf r (Finset.mem_insert_of_mem hr))]

/-- A positive rational with independently prescribed valuations on a finite prime set.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, proof of Theorem 8. -/
def primePowerProduct (S : Finset Nat.Primes) (e : Nat.Primes → ℤ) : ℚ :=
  ∏ p ∈ S, (p.val : ℚ) ^ e p

theorem primePowerProduct_pos (S : Finset Nat.Primes) (e : Nat.Primes → ℤ) :
    0 < primePowerProduct S e :=
  Finset.prod_pos (fun p _ => zpow_pos (by exact_mod_cast p.property.pos) _)

theorem primePowerProduct_valuation (S : Finset Nat.Primes) (e : Nat.Primes → ℤ)
    (p : Nat.Primes) : padicValRat p.val (primePowerProduct S e) =
      if p ∈ S then e p else 0 := by
  classical
  rw [primePowerProduct, product_valuation p S _ (fun q _ =>
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr q.property.ne_zero))]
  simp_rw [padicValRat.zpow, prime_valuation]
  simp [mul_ite]

theorem signed_multiplier (S : Finset Nat.Primes) (e : Nat.Primes → ℤ)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ∃ c : ℚ, c ≠ 0 ∧ 0 < sign * (c : ℝ) ∧
      ∀ p : Nat.Primes, padicValRat p.val c = if p ∈ S then e p else 0 := by
  have hd := primePowerProduct_pos S e
  rcases hsign with rfl | rfl
  · exact ⟨primePowerProduct S e, ne_of_gt hd, by exact_mod_cast (by simpa using hd),
      primePowerProduct_valuation S e⟩
  · refine ⟨-primePowerProduct S e, neg_ne_zero.mpr (ne_of_gt hd), ?_, ?_⟩
    · simpa using (show (0 : ℝ) < (primePowerProduct S e : ℚ) by exact_mod_cast hd)
    · intro p
      simpa using primePowerProduct_valuation S e p

theorem norm_div_of_valuation (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]) (hx : x ≠ 0) (c : ℚ) (hc : c ≠ 0)
    (hv : padicValRat p c = x.valuation) : ‖x / (c : ℚ_[p])‖ = 1 := by
  have hc' : (c : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hc
  rw [Padic.norm_eq_zpow_neg_valuation (div_ne_zero hx hc'), div_eq_mul_inv,
    Padic.valuation_mul hx (inv_ne_zero hc'), Padic.valuation_inv,
    Padic.valuation_ratCast, hv]
  simp

/-- Prescribe local square classes and a real sign with at most one new odd prime.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, proof of Theorem 8. -/
theorem prime_squareClass_selector
    (S : Finset Nat.Primes) (h2 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ S)
    (target : (p : Nat.Primes) → ℚ_[p.val])
    (htarget : ∀ p ∈ S, target p ≠ 0)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ∃ (t : ℚ) (ell : Nat.Primes), t ≠ 0 ∧ 0 < sign * (t : ℝ) ∧ ell ∉ S ∧
      ell.val ≠ 2 ∧ (∀ p ∈ S, IsSquare ((t : ℚ_[p.val]) / target p)) ∧
      ∀ p : Nat.Primes, p ∉ S → p ≠ ell → padicValRat p.val t = 0 := by
  classical
  obtain ⟨c, hc, hsignc, hval⟩ := signed_multiplier S
    (fun p => (target p).valuation) sign hsign
  have hn : ∀ p ∈ S, ‖target p / (c : ℚ_[p.val])‖ = 1 := by
    intro p hp
    exact norm_div_of_valuation p.val (target p) (htarget p hp) c hc
      (by simpa [hp] using hval p)
  have hex : ∀ p : Nat.Primes, ∃ u : ℤ_[p.val], IsUnit u ∧
      (p ∈ S → (u : ℚ_[p.val]) = target p / (c : ℚ_[p.val])) := by
    intro p
    by_cases hp : p ∈ S
    · exact ⟨⟨target p / (c : ℚ_[p.val]), (hn p hp).le⟩,
        PadicInt.isUnit_iff.mpr (hn p hp), fun _ => rfl⟩
    · exact ⟨1, isUnit_one, fun h => (hp h).elim⟩
  choose u hu hueq using hex
  obtain ⟨ell, hell, hres⟩ := prime_prescribed_residues S u (fun p _ => hu p)
  have hell0 : (ell.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ell.property.ne_zero
  refine ⟨c * ell.val, ell, mul_ne_zero hc hell0, ?_, hell, ?_, ?_, ?_⟩
  · push_cast
    rw [← mul_assoc]
    exact mul_pos hsignc (by exact_mod_cast ell.property.pos)
  · intro heq
    apply hell
    have : ell = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext heq
    rwa [this]
  · intro p hp
    have hs := square_quotient_of_residue p.val (u p) (ell.val : ℤ_[p.val])
      (hu p) (hres p hp)
    rw [hueq p hp, PadicInt.coe_natCast, div_div_eq_mul_div] at hs
    simpa only [Rat.cast_mul, Rat.cast_natCast, mul_comm] using hs
  · intro p hp hpell
    rw [padicValRat.mul hc hell0, hval p, ite_eq_right hp, prime_valuation, ite_eq_right hpell]
    rfl

example : ∃ t : ℚ, t < 0 ∧
    IsSquare ((t : ℚ_[2]) / (-1 / 2)) ∧ IsSquare ((t : ℚ_[3]) / (-1 / 2)) := by
  refine ⟨-2, by norm_num, ⟨2, ?_⟩, ⟨2, ?_⟩⟩ <;> norm_num

example : ∃ (t : ℚ) (ell : Nat.Primes), t ≠ 0 ∧ 0 < (-1 : ℝ) * (t : ℝ) ∧
    ell ∉ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes) ∧
    ell.val ≠ 2 ∧
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      IsSquare ((t : ℚ_[p.val]) / (-1 / 2))) ∧
    ∀ p : Nat.Primes, p ∉ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes) →
      p ≠ ell → padicValRat p.val t = 0 := by
  exact prime_squareClass_selector _ (Finset.mem_insert_self _ _) (fun _ => -1 / 2)
    (fun _ _ => by norm_num) (-1) (Or.inr rfl)

end HodgeLean.Foundations.MeyerRational
