import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-! Local square tests for the Meyer construction. -/

noncomputable section
open scoped Topology
namespace HodgeLean.Foundations.MeyerRational

/-- The valuation-zero factor of a nonzero local number.
Source: Serre, A Course in Arithmetic, Chapter II, §2. -/
def normalizedUnit (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) : ℤ_[p] :=
  ⟨x * (p : ℚ_[p]) ^ (-x.valuation), by
    apply (Padic.norm_le_one_iff_val_nonneg _).2
    rw [Padic.valuation_mul hx (zpow_ne_zero _ (Nat.cast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero)), Padic.valuation_zpow, Padic.valuation_p]
    simp⟩

theorem hensel_square (p : ℕ) [Fact p.Prime] (u a : ℤ_[p])
    (h : ‖a ^ 2 - u‖ < ‖2 * a‖ ^ 2) : IsSquare u := by
  obtain ⟨z, hz, _⟩ := hensels_lemma (F := Polynomial.X ^ 2 - Polynomial.C u)
    (a := a) (by simpa [show (1 : ℤ_[p]) + 1 = 2 by norm_num] using h)
  exact ⟨z, by simpa only [sq] using (sub_eq_zero.mp (show z ^ 2 - u = 0 by simpa using hz)).symm⟩

theorem unit_square_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (u : ℤ_[p]) (hu : IsUnit u) :
    IsSquare u ↔ IsSquare (PadicInt.toZMod u) := by
  constructor
  · exact fun h => h.map PadicInt.toZMod
  · rintro ⟨r, hr⟩
    let a : ℤ_[p] := r.val
    have ha : PadicInt.toZMod a = r := by simp [a]
    have hker : a ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      simp [ha, hr, sq]
    have hn : ‖a ^ 2 - u‖ < 1 := by
      exact PadicInt.mem_nonunits.mp hker
    have haunit : IsUnit a := by
      by_contra h
      have hn' := PadicInt.not_isUnit_iff.mp h
      have hsq : ‖a ^ 2‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hn' (by norm_num)
      have hu' := PadicInt.norm_lt_one_add hsq (show ‖-(a ^ 2 - u)‖ < 1 by simpa only [norm_neg] using hn)
      rw [show a ^ 2 + -(a ^ 2 - u) = u by ring, PadicInt.isUnit_iff.mp hu] at hu'
      exact lt_irrefl _ hu'
    have htwo : ‖(2 : ℤ_[p])‖ = 1 := by
      exact PadicInt.norm_natCast_eq_one_iff.mpr
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
          intro h
          exact hp ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
            (Fact.out : p.Prime).ne_one)))
    apply hensel_square p u a
    simpa only [norm_mul, htwo, PadicInt.isUnit_iff.mp haunit, one_mul, one_pow] using hn

theorem unit_square_two (u : ℤ_[2]) (hu : IsUnit u) :
    IsSquare u ↔ PadicInt.toZModPow 3 u = 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    have hz : IsUnit z := isUnit_of_mul_isUnit_left hu
    have hmod := hz.map (PadicInt.toZModPow 3)
    have hs : ∀ a : ZMod 8, IsUnit a → a * a = 1 := by decide
    simpa using hs _ hmod
  · intro h
    have hker : u - 1 ∈ Ideal.span {(2 : ℤ_[2]) ^ 3} := by
      change u - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3}
      rw [← PadicInt.ker_toZModPow (p := 2) 3, RingHom.mem_ker]
      simp [h]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow (u - 1) 3).mpr hker
    apply hensel_square 2 u 1
    have ht : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    simp only [one_pow, mul_one, ht]
    rw [norm_sub_rev]
    norm_num at hn ⊢
    linarith

theorem normalizedUnit_isUnit (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    IsUnit (normalizedUnit p x hx) := by
  apply PadicInt.isUnit_iff.mpr
  rw [← PadicInt.norm_coe]
  change ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hx (zpow_ne_zero _ hp)),
    Padic.valuation_mul hx (zpow_ne_zero _ hp), Padic.valuation_zpow, Padic.valuation_p]
  simp

theorem normalizedUnit_mul (p : ℕ) [Fact p.Prime]
    (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0) :
    normalizedUnit p (x * y) (mul_ne_zero hx hy) =
      normalizedUnit p x hx * normalizedUnit p y hy := by
  apply PadicInt.ext
  change x * y * (p : ℚ_[p]) ^ (-(x * y).valuation) =
    (x * (p : ℚ_[p]) ^ (-x.valuation)) * (y * (p : ℚ_[p]) ^ (-y.valuation))
  rw [Padic.valuation_mul hx hy, neg_add, zpow_add₀
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  ring

theorem square_iff_even_unit (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    IsSquare x ↔ Even x.valuation ∧ IsSquare (normalizedUnit p x hx) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := fun h => hx (by simp [h])
    constructor
    · exact ⟨y.valuation, Padic.valuation_mul hy hy⟩
    · exact ⟨normalizedUnit p y hy, normalizedUnit_mul p y y hy hy⟩
  · rintro ⟨⟨k, hk⟩, z, hz⟩
    refine ⟨(z : ℚ_[p]) * (p : ℚ_[p]) ^ k, ?_⟩
    have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hu := congrArg (fun u : ℤ_[p] => (u : ℚ_[p])) hz
    change x * (p : ℚ_[p]) ^ (-x.valuation) = (z : ℚ_[p]) * z at hu
    calc
      x = (x * (p : ℚ_[p]) ^ (-x.valuation)) * (p : ℚ_[p]) ^ x.valuation := by
        rw [mul_assoc, ← zpow_add₀ hp]; simp
      _ = ((z : ℚ_[p]) * z) * ((p : ℚ_[p]) ^ k * (p : ℚ_[p]) ^ k) := by
        rw [hu, hk, zpow_add₀ hp]
      _ = _ := by ring

/-- The local square criterion, including the dyadic residue modulo eight.
Source: Serre, A Course in Arithmetic, Chapter II, §2, Theorems 3 and 4. -/
theorem square_iff (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    IsSquare x ↔ Even x.valuation ∧
      (if p = 2 then PadicInt.toZModPow 3 (normalizedUnit p x hx) = 1
       else IsSquare (PadicInt.toZMod (normalizedUnit p x hx))) := by
  rw [square_iff_even_unit]
  apply and_congr_right
  intro _
  split_ifs with hp
  · subst p
    exact unit_square_two _ (normalizedUnit_isUnit _ _ _)
  · exact unit_square_odd p hp _ (normalizedUnit_isUnit _ _ _)

theorem square_of_near_one (p : ℕ) [Fact p.Prime] (y : ℚ_[p])
    (h : ‖y - 1‖ < ‖(2 : ℤ_[p])‖ ^ 2) : y ≠ 0 ∧ IsSquare y := by
  have hb : ‖(2 : ℤ_[p])‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)
  have hn : ‖y‖ = 1 := by
    have := Padic.norm_eq_of_norm_add_lt_right
      (z1 := y) (z2 := -1) (by simpa only [norm_neg, norm_one, ← sub_eq_add_neg] using h.trans_le hb)
    simpa using this
  have hy : y ≠ 0 := fun hz => by simp [hz] at hn
  let u : ℤ_[p] := ⟨y, hn.le⟩
  have hs : IsSquare u := hensel_square p u 1 (by
    rw [one_pow, mul_one, ← PadicInt.norm_coe, PadicInt.coe_sub, PadicInt.coe_one]
    change ‖1 - y‖ < _
    rwa [norm_sub_rev])
  obtain ⟨z, hz⟩ := hs
  exact ⟨hy, ⟨(z : ℚ_[p]), congrArg (fun v : ℤ_[p] => (v : ℚ_[p])) hz⟩⟩

/-- A nonzero local square class contains a neighborhood of each of its elements.
Source: Serre, A Course in Arithmetic, Chapter II, §2. -/
theorem squareClass_nhds (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    {y : ℚ_[p] | y ≠ 0 ∧ IsSquare (y / x)} ∈ 𝓝 x := by
  have ht : 0 < ‖(2 : ℤ_[p])‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (by norm_num))
  have hc : ContinuousAt (fun y : ℚ_[p] => ‖y / x - 1‖) x := by fun_prop
  have hn : {y : ℚ_[p] | ‖y / x - 1‖ < ‖(2 : ℤ_[p])‖ ^ 2} ∈ 𝓝 x :=
    hc.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa only [Set.mem_Iio, div_self hx, sub_self, norm_zero] using ht))
  filter_upwards [hn] with y hy
  obtain ⟨hne, hs⟩ := square_of_near_one p (y / x) hy
  exact ⟨fun hz => hne (by simp [hz]), hs⟩

example : ¬IsSquare (5 : ℤ_[2]) := by
  have hu : IsUnit (5 : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 2 5))
  rw [unit_square_two _ hu]
  change ¬ (PadicInt.toZModPow 3) ((5 : ℕ) : ℤ_[2]) = 1
  rw [map_natCast]
  decide

example : ¬IsSquare (2 : ℚ_[2]) := by
  intro h
  have he := ((square_iff 2 2 (by norm_num)).mp h).1
  have hv : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  rw [hv] at he
  norm_num at he

example : IsSquare (1 / 9 : ℚ_[2]) := by
  exact ⟨1 / 3, by norm_num⟩

end HodgeLean.Foundations.MeyerRational
