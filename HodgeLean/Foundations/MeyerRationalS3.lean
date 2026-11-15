import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-! Binary norm obstruction and reciprocity helpers for Meyer stage S3. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

/-- The sign of the obstruction to representing `b` by the binary norm form.
Source: Serre, A Course in Arithmetic, Chapter III, §1. -/
def binaryNormSymbol (K : Type*) [Field K] (a b : K) : ℤ := by
  classical
  exact if ∃ x y : K, x ^ 2 - a * y ^ 2 = b then 1 else -1

theorem binaryNormSymbol_eq_one {K : Type*} [Field K] (a b : K) :
    binaryNormSymbol K a b = 1 ↔ ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  simp only [binaryNormSymbol]
  split_ifs <;> simp_all

theorem binaryNormSymbol_sq {K : Type*} [Field K] (a b : K) :
    binaryNormSymbol K a b ^ 2 = 1 := by
  unfold binaryNormSymbol
  split_ifs <;> norm_num

theorem binary_norm_of_square {K : Type*} [Field K] [CharZero K]
    (a b r : K) (hr : r ^ 2 = a) (ha : a ≠ 0) :
    ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  have hr₀ : r ≠ 0 := by intro h; simp [h] at hr; exact ha hr.symm
  refine ⟨(b + 1) / 2, (b - 1) / (2 * r), ?_⟩
  rw [← hr]
  field_simp
  <;> ring

/-- The norm obstruction agrees with nonzero ternary isotropy.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Proposition 1. -/
theorem binaryNormSymbol_eq_one_iff_ternary {K : Type*} [Field K] [CharZero K]
    (a b : K) (ha : a ≠ 0) :
    binaryNormSymbol K a b = 1 ↔
      ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - a * y ^ 2 = b * z ^ 2 := by
  rw [binaryNormSymbol_eq_one]
  constructor
  · rintro ⟨x, y, he⟩
    exact ⟨x, y, 1, by simp, by simpa using he⟩
  · rintro ⟨x, y, z, hn, he⟩
    by_cases hz : z = 0
    · have hy : y ≠ 0 := by
        intro hy
        have hx : x = 0 := by simpa [hy, hz] using he
        tauto
      have hr : (x / y) ^ 2 = a := by
        rw [div_pow]
        apply (div_eq_iff (pow_ne_zero 2 hy)).mpr
        simpa [div_pow, hz] using (show x ^ 2 = a * y ^ 2 by simpa [hz, sub_eq_zero] using he)
      exact binary_norm_of_square a b (x / y) hr ha
    · refine ⟨x / z, y / z, ?_⟩
      field_simp
      linear_combination he

/-- The real-place sign formula for nonzero coefficients.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_real (a b : ℝ) (ha : a ≠ 0) (_hb : b ≠ 0) :
    binaryNormSymbol ℝ a b = if a < 0 ∧ b < 0 then -1 else 1 := by
  by_cases h : a < 0 ∧ b < 0
  · rw [ite_eq_left h]
    unfold binaryNormSymbol
    apply ite_eq_right
    rintro ⟨x, y, he⟩
    have hterm : a * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.1.le (sq_nonneg y)
    nlinarith [sq_nonneg x]
  · rw [ite_eq_right h, binaryNormSymbol_eq_one]
    by_cases ha' : 0 < a
    · exact binary_norm_of_square a b (Real.sqrt a) (Real.sq_sqrt ha'.le) ha
    · have hb' : 0 ≤ b := by
        have ha'' : a < 0 := lt_of_le_of_ne (le_of_not_gt ha') ha
        exact not_lt.mp (fun hb'' => h ⟨ha'', hb''⟩)
      exact ⟨Real.sqrt b, 0, by simp [Real.sq_sqrt hb']⟩

theorem norm_finite_field (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ZMod p) (ha : a ≠ 0) : ∃ x y : ZMod p, x ^ 2 - a * y ^ 2 = b := by
  obtain ⟨x, y, he⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C b)
    (g := Polynomial.C (-a) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by decide) b)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr ha))
    (by simpa using (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp)
  refine ⟨x, y, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul] at he
  linear_combination he

theorem padic_unit_of_residue_ne_zero (p : ℕ) [Fact p.Prime] (x : ℤ_[p])
    (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra h
  apply hx
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZMod]
  exact PadicInt.mem_nonunits.mpr (PadicInt.not_isUnit_iff.mp h)

theorem padic_simple_root (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ_[p]) (x : ℤ_[p])
    (hf : PadicInt.toZMod (f.eval x) = 0)
    (hd : PadicInt.toZMod (f.derivative.eval x) ≠ 0) : ∃ y : ℤ_[p], f.eval y = 0 := by
  have hn : ‖f.eval x‖ < 1 := by
    apply PadicInt.mem_nonunits.mp
    change f.eval x ∈ IsLocalRing.maximalIdeal ℤ_[p]
    rw [← PadicInt.ker_toZMod]
    exact hf
  have hu := PadicInt.isUnit_iff.mp (padic_unit_of_residue_ne_zero p _ hd)
  obtain ⟨y, hy, _⟩ := hensels_lemma (F := f) (a := x) (by simpa [hu] using hn)
  exact ⟨y, hy⟩

theorem norm_padic_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) :
    ∃ x y : ℤ_[p], x ^ 2 - a * y ^ 2 = b := by
  have ha₀ : PadicInt.toZMod a ≠ 0 := (ha.map PadicInt.toZMod).ne_zero
  have hb₀ : PadicInt.toZMod b ≠ 0 := (hb.map PadicInt.toZMod).ne_zero
  obtain ⟨x, y, he⟩ := norm_finite_field p hp (PadicInt.toZMod a) (PadicInt.toZMod b) ha₀
  let X : ℤ_[p] := x.val
  let Y : ℤ_[p] := y.val
  have hX : PadicInt.toZMod X = x := by simp [X]
  have hY : PadicInt.toZMod Y = y := by simp [Y]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    exact hp ((Nat.prime_two.eq_one_or_self_of_dvd p hd).resolve_left (Fact.out : p.Prime).ne_one)
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by intro hy; simp [hx, hy] at he; exact hb₀ he.symm
    obtain ⟨v, hv⟩ := padic_simple_root p
      (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (b - X ^ 2)) Y
      (by simp [hX, hY]; linear_combination -he)
      (by simpa [Polynomial.derivative_pow, map_ofNat, hY, show (1 : ℤ_[p]) + 1 = 2 by norm_num] using
        mul_ne_zero ha₀ (mul_ne_zero htwo hy))
    refine ⟨X, v, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hv
    linear_combination -hv
  · obtain ⟨u, hu⟩ := padic_simple_root p
      (Polynomial.X ^ 2 - Polynomial.C (a * Y ^ 2 + b)) X
      (by simp [hX, hY]; linear_combination he)
      (by simpa [Polynomial.derivative_pow, map_ofNat, hX, show (1 : ℤ_[p]) + 1 = 2 by norm_num] using mul_ne_zero htwo hx)
    refine ⟨u, Y, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hu
    linear_combination hu

theorem binaryNormSymbol_padic_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : binaryNormSymbol ℚ_[p] a b = 1 := by
  rw [binaryNormSymbol_eq_one]
  let A : ℤ_[p] := ⟨a, ha.le⟩
  let B : ℤ_[p] := ⟨b, hb.le⟩
  obtain ⟨x, y, he⟩ := norm_padic_units p hp A B
    (PadicInt.isUnit_iff.mpr ha) (PadicInt.isUnit_iff.mpr hb)
  refine ⟨x, y, ?_⟩
  exact congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) he

theorem rational_padic_unit_of_large (p : ℕ) [Fact p.Prime] (a : ℚ) (ha : a ≠ 0)
    (hn : a.num.natAbs < p) (hd : a.den < p) : ‖(a : ℚ_[p])‖ = 1 := by
  have hn₀ : 0 < a.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr ha)
  have hn' := padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn₀ hn)
  have hd' := padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt a.den_pos hd)
  rw [Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr ha), Padic.valuation_ratCast]
  simp [padicValRat, padicValInt, hn', hd']

/-- A finite set contains every finite place with nontrivial norm obstruction.
Source: Serre, A Course in Arithmetic, Chapter III, §2, Theorem 3. -/
theorem binaryNormSymbol_finite_support (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset ℕ, 2 ∈ S ∧ ∀ (p : ℕ) [Fact p.Prime], p ∉ S →
      binaryNormSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1 := by
  refine ⟨Finset.range (a.num.natAbs + a.den + b.num.natAbs + b.den + 3),
    Finset.mem_range.mpr (by omega), ?_⟩
  intro p _ hp
  simp only [Finset.mem_range, not_lt] at hp
  exact binaryNormSymbol_padic_units p (by omega) _ _
    (rational_padic_unit_of_large p a ha (by omega) (by omega))
    (rational_padic_unit_of_large p b hb (by omega) (by omega))

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Quadratic reciprocity multiplied over two disjoint finite sets of odd primes.
Source: Serre, A Course in Arithmetic, Chapter I, §3, quadratic reciprocity. -/
theorem reciprocity_finset (S T : Finset Nat.Primes)
    (hS : ∀ p ∈ S, p.val ≠ 2) (hT : ∀ q ∈ T, q.val ≠ 2)
    (hST : Disjoint S T) :
    (∏ p ∈ S, ∏ q ∈ T, legendreSym q.val p.val) *
      (∏ p ∈ S, ∏ q ∈ T, legendreSym p.val q.val) =
      (-1 : ℤ) ^ ((∑ p ∈ S, p.val / 2) * (∑ q ∈ T, q.val / 2)) := by
  rw [← Finset.prod_mul_distrib]
  have he : ∀ p ∈ S, ∀ q ∈ T,
      legendreSym q.val p.val * legendreSym p.val q.val = (-1 : ℤ) ^ (p.val / 2 * (q.val / 2)) := by
    intro p hp q hq
    exact legendreSym.quadratic_reciprocity (hS p hp) (hT q hq)
      (by intro he; have : p = q := Subtype.ext he; subst q; exact Finset.disjoint_left.mp hST hp hq)
  calc
    (∏ p ∈ S, (∏ q ∈ T, legendreSym q.val p.val) * (∏ q ∈ T, legendreSym p.val q.val)) =
        ∏ p ∈ S, ∏ q ∈ T, (-1 : ℤ) ^ (p.val / 2 * (q.val / 2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (he p hp)
    _ = _ := by
      simp only [← Finset.prod_pow_eq_pow_sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.prod_comm

theorem binaryNormSymbol_symm {K : Type*} [Field K] [CharZero K]
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    binaryNormSymbol K a b = binaryNormSymbol K b a := by
  have h : (∃ x y : K, x ^ 2 - a * y ^ 2 = b) ↔
      ∃ x y : K, x ^ 2 - b * y ^ 2 = a := by
    rw [← binaryNormSymbol_eq_one, ← binaryNormSymbol_eq_one,
      binaryNormSymbol_eq_one_iff_ternary a b ha,
      binaryNormSymbol_eq_one_iff_ternary b a hb]
    constructor <;> rintro ⟨x, y, z, hn, he⟩ <;>
      exact ⟨x, z, y, by tauto, by linear_combination he⟩
  unfold binaryNormSymbol
  split_ifs <;> simp_all

theorem binaryNormSymbol_mul_square_left {K : Type*} [Field K]
    (a b r : K) (hr : r ≠ 0) :
    binaryNormSymbol K (a * r ^ 2) b = binaryNormSymbol K a b := by
  have h : (∃ x y : K, x ^ 2 - (a * r ^ 2) * y ^ 2 = b) ↔
      ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
    constructor
    · rintro ⟨x, y, he⟩
      exact ⟨x, r * y, by linear_combination he⟩
    · rintro ⟨x, y, he⟩
      refine ⟨x, y / r, ?_⟩
      field_simp
      linear_combination he
  unfold binaryNormSymbol
  split_ifs <;> simp_all

theorem binaryNormSymbol_mul_square_right {K : Type*} [Field K] [CharZero K]
    (a b r : K) (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    binaryNormSymbol K a (b * r ^ 2) = binaryNormSymbol K a b := by
  rw [binaryNormSymbol_symm a _ ha (mul_ne_zero hb (pow_ne_zero 2 hr)),
    binaryNormSymbol_mul_square_left b a r hr, binaryNormSymbol_symm b a hb ha]

theorem binaryNormSymbol_neg_mul {K : Type*} [Field K]
    (a b : K) (ha : a ≠ 0) :
    binaryNormSymbol K a (-a * b) = binaryNormSymbol K a b := by
  have h : (∃ x y : K, x ^ 2 - a * y ^ 2 = -a * b) ↔
      ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
    constructor
    · rintro ⟨x, y, he⟩
      refine ⟨y, x / a, ?_⟩
      field_simp
      linear_combination -he
    · rintro ⟨x, y, he⟩
      refine ⟨a * y, x, ?_⟩
      linear_combination -a * he
  unfold binaryNormSymbol
  split_ifs <;> simp_all

theorem norm_primitive_vector (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι]
    (v : ι → ℚ_[p]) (hv : v ≠ 0) :
    ∃ d : ℚ_[p], d ≠ 0 ∧ ∃ w : ι → ℤ_[p],
      (∀ i, v i = d * w i) ∧ ∃ i, IsUnit (w i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
    ⟨j, Finset.mem_univ _⟩
  have hd : v i ≠ 0 := by
    intro he
    have hh := hi j (Finset.mem_univ _)
    rw [he, norm_zero] at hh
    exact hj (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  let w : ι → ℤ_[p] := fun j => ⟨v j / v i, by
    change ‖v j / v i‖ ≤ 1
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hd)).mpr (hi j (Finset.mem_univ _))⟩
  refine ⟨v i, hd, w, fun j => ?_, i, ?_⟩
  · change v j = v i * (v j / v i)
    field_simp
  · apply PadicInt.isUnit_iff.mpr
    change ‖v i / v i‖ = 1
    rw [div_self hd, norm_one]

theorem norm_padic_primitive (p : ℕ) [Fact p.Prime] (a b : ℤ_[p])
    (h : binaryNormSymbol ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p]) = 1) :
    ∃ x y z : ℤ_[p], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧
      x ^ 2 - a * y ^ 2 = b * z ^ 2 := by
  obtain ⟨x, y, he⟩ := (binaryNormSymbol_eq_one _ _).mp h
  have hv : (![x, y, 1] : Fin 3 → ℚ_[p]) ≠ 0 := by
    intro hh
    have ht := congrFun hh 2
    exact one_ne_zero (show (1 : ℚ_[p]) = 0 from ht)
  obtain ⟨d, hd, w, hw, i, hi⟩ := norm_primitive_vector p ![x, y, 1] hv
  have h0 : x = d * (w 0 : ℚ_[p]) := hw 0
  have h1 : y = d * (w 1 : ℚ_[p]) := hw 1
  have h2 : 1 = d * (w 2 : ℚ_[p]) := hw 2
  refine ⟨w 0, w 1, w 2, ?_, ?_⟩
  · fin_cases i <;> tauto
  · apply Subtype.ext
    change (w 0 : ℚ_[p]) ^ 2 - a * (w 1 : ℚ_[p]) ^ 2 = b * (w 2 : ℚ_[p]) ^ 2
    apply (mul_left_cancel₀ (pow_ne_zero 2 hd))
    rw [h0, h1] at he
    linear_combination he + (b : ℚ_[p]) * (1 + d * (w 2 : ℚ_[p])) * h2

theorem norm_unit_prime_residue (p : ℕ) [Fact p.Prime] (a b : ℤ_[p])
    (hb : IsUnit b) (x y z : ℤ_[p])
    (hu : IsUnit x ∨ IsUnit y ∨ IsUnit z)
    (he : x ^ 2 - a * y ^ 2 = (p : ℤ_[p]) * b * z ^ 2) :
    IsSquare (PadicInt.toZMod a) := by
  have hr := congrArg PadicInt.toZMod he
  simp only [map_sub, map_pow, map_mul, map_natCast, ZMod.natCast_self,
    zero_mul] at hr
  by_cases hy : PadicInt.toZMod y = 0
  · have hx : PadicInt.toZMod x = 0 := by
      simpa [hy] using hr
    have hz : IsUnit z := hu.resolve_left (fun h => (h.map PadicInt.toZMod).ne_zero hx) |>.resolve_left
      (fun h => (h.map PadicInt.toZMod).ne_zero hy)
    have hdiv : ∀ v : ℤ_[p], PadicInt.toZMod v = 0 → (p : ℤ_[p]) ∣ v := by
      intro v hv
      rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hv
    obtain ⟨X, hX⟩ := hdiv x hx
    obtain ⟨Y, hY⟩ := hdiv y hy
    have hpp : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hxx : (PadicInt.toZModPow 2 x) ^ 2 = 0 := by
      rw [hX, map_mul, map_natCast, mul_pow, hpp, zero_mul]
    have hyy : (PadicInt.toZModPow 2 y) ^ 2 = 0 := by
      rw [hY, map_mul, map_natCast, mul_pow, hpp, zero_mul]
    have hr₂ := congrArg (PadicInt.toZModPow 2) he
    simp only [map_sub, map_mul, map_pow, map_natCast, hxx, hyy, mul_zero, sub_zero] at hr₂
    have hp₀ : (p : ZMod (p ^ 2)) = 0 :=
      ((hb.map (PadicInt.toZModPow 2)).mul ((hz.map (PadicInt.toZModPow 2)).pow 2)).mul_right_cancel
        (by simpa only [zero_mul, mul_assoc] using hr₂.symm)
    have hd : p ^ 2 ∣ p := (CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) p).mp hp₀
    have hp := (Fact.out : p.Prime).two_le
    have hle := Nat.le_of_dvd (by omega : 0 < p) hd
    nlinarith
  · refine ⟨PadicInt.toZMod x / PadicInt.toZMod y, ?_⟩
    field_simp
    linear_combination -hr

theorem norm_padic_unit_prime_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) :
    binaryNormSymbol ℚ_[p] (a : ℚ_[p]) ((p : ℚ_[p]) * b) = 1 ↔
      IsSquare (PadicInt.toZMod a) := by
  constructor
  · intro h
    obtain ⟨x, y, z, hu, he⟩ := norm_padic_primitive p a (p * b) h
    exact norm_unit_prime_residue p a b hb x y z hu he
  · rintro ⟨r, hr⟩
    have hr₀ : r ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hr
      exact (ha.map PadicInt.toZMod).ne_zero hr
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro hh
      have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hh
      exact hp ((Nat.prime_two.eq_one_or_self_of_dvd p hd).resolve_left (Fact.out : p.Prime).ne_one)
    obtain ⟨s, hs⟩ := padic_simple_root p (Polynomial.X ^ 2 - Polynomial.C a) (r.val : ℤ_[p])
      (by simp [hr, sq])
      (by simpa [Polynomial.derivative_pow, map_ofNat, show (1 : ℤ_[p]) + 1 = 2 by norm_num] using
        mul_ne_zero htwo hr₀)
    have hs' : (s : ℚ_[p]) ^ 2 = a := by
      have ht : s ^ 2 = a := sub_eq_zero.mp (by simpa using hs)
      exact congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) ht
    rw [binaryNormSymbol_eq_one]
    exact binary_norm_of_square _ _ s hs' (by
      exact PadicInt.coe_ne_zero.mpr ha.ne_zero)

theorem binaryNormSymbol_eq_neg_one_iff {K : Type*} [Field K] (a b : K) :
    binaryNormSymbol K a b = -1 ↔ binaryNormSymbol K a b ≠ 1 := by
  unfold binaryNormSymbol
  split_ifs <;> norm_num

theorem binaryNormSymbol_common_factor {K : Type*} [Field K] [CharZero K]
    (a b t : K) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    binaryNormSymbol K (t * a) (t * b) = binaryNormSymbol K (-a * b) (t * a) := by
  have hab : -a * b ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ha) hb
  calc
    binaryNormSymbol K (t * a) (t * b) =
        binaryNormSymbol K (t * a) (-(t * a) * (t * b)) :=
      (binaryNormSymbol_neg_mul _ _ (mul_ne_zero ht ha)).symm
    _ = binaryNormSymbol K (t * a) ((-a * b) * t ^ 2) := by congr 1 <;> ring
    _ = binaryNormSymbol K (t * a) (-a * b) :=
      binaryNormSymbol_mul_square_right _ _ _ (mul_ne_zero ht ha) hab ht
    _ = _ := binaryNormSymbol_symm _ _ (mul_ne_zero ht ha) hab

/-- The odd-prime norm formula for a unit and a coefficient of valuation one.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_padic_unit_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) :
    binaryNormSymbol ℚ_[p] (a : ℚ_[p]) ((p : ℚ_[p]) * b) =
      legendreSym p (PadicInt.toZMod a).val := by
  by_cases hs : IsSquare (PadicInt.toZMod a)
  · rw [(norm_padic_unit_prime_iff p hp a b ha hb).mpr hs]
    symm
    exact (legendreSym.eq_one_iff' p (by simpa only [ZMod.natCast_zmod_val] using (ha.map PadicInt.toZMod).ne_zero)).mpr
      (by simpa only [ZMod.natCast_zmod_val] using hs)
  · rw [(binaryNormSymbol_eq_neg_one_iff _ _).mpr
      (fun h => hs ((norm_padic_unit_prime_iff p hp a b ha hb).mp h))]
    symm
    apply (legendreSym.eq_neg_one_iff' p).mpr
    simpa only [ZMod.natCast_zmod_val] using hs

/-- The four valuation-parity cases of the odd-prime formula.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_padic_parity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) (e f : Fin 2) :
    binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ e.val * a) ((p : ℚ_[p]) ^ f.val * b) =
      if e = 0 then
        if f = 0 then 1 else legendreSym p (PadicInt.toZMod a).val
      else if f = 0 then legendreSym p (PadicInt.toZMod b).val
      else legendreSym p (PadicInt.toZMod (-a * b)).val := by
  have ha₀ := PadicInt.coe_ne_zero.mpr ha.ne_zero
  have hb₀ := PadicInt.coe_ne_zero.mpr hb.ne_zero
  have hp₀ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  fin_cases e <;> fin_cases f <;> simp only [Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_mul, ↓reduceIte, Fin.zero_ne_one]
  · exact binaryNormSymbol_padic_units p hp _ _
      (by simpa only [PadicInt.norm_coe] using PadicInt.isUnit_iff.mp ha)
      (by simpa only [PadicInt.norm_coe] using PadicInt.isUnit_iff.mp hb)
  · exact binaryNormSymbol_padic_unit_prime p hp a b ha hb
  · rw [binaryNormSymbol_symm _ _ (mul_ne_zero hp₀ ha₀) hb₀]
    exact binaryNormSymbol_padic_unit_prime p hp b a hb ha
  · rw [binaryNormSymbol_common_factor _ _ _ ha₀ hb₀ hp₀]
    exact binaryNormSymbol_padic_unit_prime p hp (-a * b) a (ha.neg.mul hb) ha

theorem zpow_parity_factor {K : Type*} [Field K] (t : K) (ht : t ≠ 0) (n : ℤ) :
    t ^ n = t ^ (n % 2) * (t ^ (n / 2)) ^ 2 := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ ht]
  congr 1
  omega

theorem binaryNormSymbol_zpow_reduce {K : Type*} [Field K] [CharZero K]
    (t a b : K) (ht : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℤ) :
    binaryNormSymbol K (t ^ m * a) (t ^ n * b) =
      binaryNormSymbol K (t ^ (m % 2) * a) (t ^ (n % 2) * b) := by
  have hm : t ^ m * a = (t ^ (m % 2) * a) * (t ^ (m / 2)) ^ 2 := by
    rw [zpow_parity_factor t ht m]
    ring
  have hn : t ^ n * b = (t ^ (n % 2) * b) * (t ^ (n / 2)) ^ 2 := by
    rw [zpow_parity_factor t ht n]
    ring
  rw [hm, hn, binaryNormSymbol_mul_square_left _ _ _ (zpow_ne_zero _ ht),
    binaryNormSymbol_mul_square_right _ _ _ (mul_ne_zero (zpow_ne_zero _ ht) ha)
      (mul_ne_zero (zpow_ne_zero _ ht) hb) (zpow_ne_zero _ ht)]

theorem padic_unit_decomposition (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    ∃ u : ℤ_[p], IsUnit u ∧ x = (p : ℚ_[p]) ^ x.valuation * u := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hn : ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hx (zpow_ne_zero _ hp)),
      Padic.valuation_mul hx (zpow_ne_zero _ hp), Padic.valuation_zpow, Padic.valuation_p]
    simp
  let u : ℤ_[p] := ⟨x * (p : ℚ_[p]) ^ (-x.valuation), hn.le⟩
  refine ⟨u, PadicInt.isUnit_iff.mpr hn, ?_⟩
  change x = (p : ℚ_[p]) ^ x.valuation * (x * (p : ℚ_[p]) ^ (-x.valuation))
  rw [mul_left_comm, ← zpow_add₀ hp]
  simp

/-- The residue formula applies to arbitrary integer valuations, including negatives.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_padic_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) (m n : ℤ) :
    binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ m * a) ((p : ℚ_[p]) ^ n * b) =
      if m % 2 = 0 then
        if n % 2 = 0 then 1 else legendreSym p (PadicInt.toZMod a).val
      else if n % 2 = 0 then legendreSym p (PadicInt.toZMod b).val
      else legendreSym p (PadicInt.toZMod (-a * b)).val := by
  have hp₀ : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [binaryNormSymbol_zpow_reduce _ _ _ hp₀
    (PadicInt.coe_ne_zero.mpr ha.ne_zero) (PadicInt.coe_ne_zero.mpr hb.ne_zero)]
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · simpa [hm, hn] using binaryNormSymbol_padic_parity p hp a b ha hb 0 0
  · simpa [hm, hn] using binaryNormSymbol_padic_parity p hp a b ha hb 0 1
  · simpa [hm, hn] using binaryNormSymbol_padic_parity p hp a b ha hb 1 0
  · simpa [hm, hn] using binaryNormSymbol_padic_parity p hp a b ha hb 1 1

theorem norm_two_hensel (f : Polynomial ℤ_[2]) (x : ℤ_[2])
    (hf : PadicInt.toZModPow 3 (f.eval x) = 0)
    (hd : ‖f.derivative.eval x‖ = (2 : ℝ)⁻¹) :
    ∃ y : ℤ_[2], f.eval y = 0 := by
  have hk : f.eval x ∈ Ideal.span {(2 : ℤ_[2]) ^ 3} := by
    change f.eval x ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3}
    rw [← PadicInt.ker_toZModPow (p := 2) 3, RingHom.mem_ker]
    exact hf
  have hn := (PadicInt.norm_le_pow_iff_mem_span_pow (f.eval x) 3).mpr hk
  obtain ⟨y, hy, _⟩ := hensels_lemma (F := f) (a := x) (by
    change ‖f.eval x‖ < ‖f.derivative.eval x‖ ^ 2
    rw [hd]
    norm_num at hn ⊢
    linarith)
  exact ⟨y, hy⟩

theorem norm_two_lift_unit (x : ZMod 8) (hx : IsUnit x) : IsUnit (x.val : ℤ_[2]) := by
  apply PadicInt.isUnit_iff.mpr
  apply PadicInt.norm_natCast_eq_one_iff.mpr
  have hcop : x.val.Coprime 8 := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using hx)
  exact (hcop.of_dvd_right (by decide : 2 ∣ 8)).symm

theorem norm_two_of_residue (a b : ℤ_[2]) (ha : IsUnit a)
    (x y z : ZMod 8) (hu : IsUnit x ∨ IsUnit y)
    (he : x ^ 2 - PadicInt.toZModPow 3 a * y ^ 2 = PadicInt.toZModPow 3 b * z ^ 2) :
    binaryNormSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) = 1 := by
  letI : NeZero (8 : ℕ) := ⟨by decide⟩
  letI : Fact (1 < (8 : ℕ)) := ⟨by decide⟩
  have ht : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
  let X : ℤ_[2] := x.val
  let Y : ℤ_[2] := y.val
  let Z : ℤ_[2] := z.val
  have hX : PadicInt.toZModPow 3 X = x := by simp [X]
  have hY : PadicInt.toZModPow 3 Y = y := by simp [Y]
  have hZ : PadicInt.toZModPow 3 Z = z := by simp [Z]
  rw [binaryNormSymbol_eq_one_iff_ternary _ _ (PadicInt.coe_ne_zero.mpr ha.ne_zero)]
  rcases hu with hx | hy
  · have hXu : IsUnit X := norm_two_lift_unit x hx
    obtain ⟨u, hu⟩ := norm_two_hensel
      (Polynomial.X ^ 2 - Polynomial.C (a * Y ^ 2 + b * Z ^ 2)) X
      (by simp [hX, hY, hZ]; linear_combination he)
      (by simp [Polynomial.derivative_pow, norm_mul, PadicInt.isUnit_iff.mp hXu,
        show (1 : ℤ_[2]) + 1 = 2 by norm_num, ht])
    have heq : u ^ 2 - a * Y ^ 2 = b * Z ^ 2 := by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hu
      linear_combination hu
    have hn : u ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0 := by
      by_contra! hh
      have hzero : x ^ 2 = 0 := by
        have hy₀ : y = 0 := by rw [← hY, hh.2.1, map_zero]
        have hz₀ : z = 0 := by rw [← hZ, hh.2.2, map_zero]
        simpa [hy₀, hz₀] using he
      exact (hx.pow 2).ne_zero hzero
    exact ⟨u, Y, Z, by simpa only [ne_eq, PadicInt.coe_eq_zero] using hn,
      congrArg (fun v : ℤ_[2] => (v : ℚ_[2])) heq⟩
  · have hYu : IsUnit Y := norm_two_lift_unit y hy
    obtain ⟨v, hv⟩ := norm_two_hensel
      (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (b * Z ^ 2 - X ^ 2)) Y
      (by simp [hX, hY, hZ]; linear_combination -he)
      (by simp [Polynomial.derivative_pow, norm_mul, PadicInt.isUnit_iff.mp hYu,
        PadicInt.isUnit_iff.mp ha, show (1 : ℤ_[2]) + 1 = 2 by norm_num, ht])
    have heq : X ^ 2 - a * v ^ 2 = b * Z ^ 2 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at hv
      linear_combination -hv
    have hn : X ≠ 0 ∨ v ≠ 0 ∨ Z ≠ 0 := by
      by_contra! hh
      have hzero : PadicInt.toZModPow 3 a * y ^ 2 = 0 := by
        have hx₀ : x = 0 := by rw [← hX, hh.1, map_zero]
        have hz₀ : z = 0 := by rw [← hZ, hh.2.2, map_zero]
        simpa [hx₀, hz₀] using he
      exact ((ha.map (PadicInt.toZModPow 3)).mul (hy.pow 2)).ne_zero hzero
    exact ⟨X, v, Z, by simpa only [ne_eq, PadicInt.coe_eq_zero] using hn,
      congrArg (fun v : ℤ_[2] => (v : ℚ_[2])) heq⟩

set_option maxSynthPendingDepth 32 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem norm_two_residue_table :
    ∀ (a b : (ZMod 8)ˣ) (e : Fin 2) (x y z : ZMod 8),
      (IsUnit x ∨ IsUnit y ∨ IsUnit z) →
        x ^ 2 - (a : ZMod 8) * y ^ 2 = (2 ^ e.val * (b : ZMod 8)) * z ^ 2 →
      (((a : ZMod 8).val / 2) * ((b : ZMod 8).val / 2) +
        e.val * (((a : ZMod 8).val ^ 2 - 1) / 8)) % 2 = 0 := by
  decide

set_option maxSynthPendingDepth 32 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem norm_two_residue_witness :
    ∀ (a b : (ZMod 8)ˣ) (e : Fin 2),
      (((a : ZMod 8).val / 2) * ((b : ZMod 8).val / 2) +
        e.val * (((a : ZMod 8).val ^ 2 - 1) / 8)) % 2 = 0 →
      ∃ x y z : ZMod 8, (IsUnit x ∨ IsUnit y) ∧
        x ^ 2 - (a : ZMod 8) * y ^ 2 = (2 ^ e.val * (b : ZMod 8)) * z ^ 2 := by
  decide

theorem norm_two_unit_iff (a b : ℤ_[2]) (ha : IsUnit a) (hb : IsUnit b) (e : Fin 2) :
    binaryNormSymbol ℚ_[2] (a : ℚ_[2]) ((2 : ℚ_[2]) ^ e.val * b) = 1 ↔
      ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
        e.val * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8)) % 2 = 0 := by
  let A : (ZMod 8)ˣ := (ha.map (PadicInt.toZModPow 3)).unit
  let B : (ZMod 8)ˣ := (hb.map (PadicInt.toZModPow 3)).unit
  have hA : (A : ZMod 8) = PadicInt.toZModPow 3 a := IsUnit.unit_spec _
  have hB : (B : ZMod 8) = PadicInt.toZModPow 3 b := IsUnit.unit_spec _
  constructor
  · intro h
    obtain ⟨x, y, z, hu, he⟩ := norm_padic_primitive 2 a (2 ^ e.val * b) h
    have hr := congrArg (PadicInt.toZModPow 3) he
    have hc : ∃ x y z : ZMod 8, (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧
        x ^ 2 - (A : ZMod 8) * y ^ 2 = (2 ^ e.val * (B : ZMod 8)) * z ^ 2 := by
      refine ⟨PadicInt.toZModPow 3 x, PadicInt.toZModPow 3 y, PadicInt.toZModPow 3 z, ?_, ?_⟩
      · rcases hu with hu | hu | hu
        · exact Or.inl (hu.map _)
        · exact Or.inr (Or.inl (hu.map _))
        · exact Or.inr (Or.inr (hu.map _))
      · simpa only [hA, hB, map_sub, map_pow, map_mul, map_ofNat] using hr
    obtain ⟨X, Y, Z, hunit, heq⟩ := hc
    simpa only [hA, hB] using norm_two_residue_table A B e X Y Z hunit heq
  · intro h
    obtain ⟨x, y, z, hu, he⟩ := norm_two_residue_witness A B e (by simpa only [hA, hB] using h)
    apply norm_two_of_residue a (2 ^ e.val * b) ha x y z hu
    simpa only [map_mul, map_pow, map_ofNat, hA, hB] using he

/-- The dyadic norm formula when the first coefficient is a unit.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_two_unit (a b : ℤ_[2]) (ha : IsUnit a) (hb : IsUnit b) (e : Fin 2) :
    binaryNormSymbol ℚ_[2] (a : ℚ_[2]) ((2 : ℚ_[2]) ^ e.val * b) =
      (-1 : ℤ) ^ ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
        e.val * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8)) := by
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases h : ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
      e.val * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8)) % 2 = 0
  · rw [h, pow_zero]
    exact (norm_two_unit_iff a b ha hb e).mpr h
  · have hmod : ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
        e.val * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8)) % 2 = 1 := by omega
    rw [hmod, pow_one, binaryNormSymbol_eq_neg_one_iff]
    exact fun hh => h ((norm_two_unit_iff a b ha hb e).mp hh)

set_option maxHeartbeats 400000 in
theorem norm_two_sign_identity : ∀ a b : (ZMod 8)ˣ,
    (-1 : ℤ) ^ (((-(a : ZMod 8) * b).val / 2) * ((a : ZMod 8).val / 2) +
      ((-(a : ZMod 8) * b).val ^ 2 - 1) / 8) =
    (-1 : ℤ) ^ (((a : ZMod 8).val / 2) * ((b : ZMod 8).val / 2) +
      ((a : ZMod 8).val ^ 2 - 1) / 8 + ((b : ZMod 8).val ^ 2 - 1) / 8) := by
  decide

/-- The dyadic formula in all four valuation-parity cases.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_two_parity (a b : ℤ_[2]) (ha : IsUnit a) (hb : IsUnit b)
    (e f : Fin 2) :
    binaryNormSymbol ℚ_[2] ((2 : ℚ_[2]) ^ e.val * a) ((2 : ℚ_[2]) ^ f.val * b) =
      (-1 : ℤ) ^ ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
        f.val * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8) +
        e.val * (((PadicInt.toZModPow 3 b).val ^ 2 - 1) / 8)) := by
  have ha₀ := PadicInt.coe_ne_zero.mpr ha.ne_zero
  have hb₀ := PadicInt.coe_ne_zero.mpr hb.ne_zero
  have ht : (2 : ℚ_[2]) ≠ 0 := by norm_num
  fin_cases e <;> fin_cases f
  · simpa using binaryNormSymbol_two_unit a b ha hb 0
  · simpa using binaryNormSymbol_two_unit a b ha hb 1
  · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, zero_mul, add_zero]
    rw [binaryNormSymbol_symm _ _ (mul_ne_zero ht ha₀) hb₀]
    simpa [mul_comm] using binaryNormSymbol_two_unit b a hb ha 1
  · simp only [Fin.val_one, pow_one, one_mul]
    rw [binaryNormSymbol_common_factor _ _ _ ha₀ hb₀ ht]
    have h := binaryNormSymbol_two_unit (-a * b) a (ha.neg.mul hb) ha 1
    simp only [Fin.val_one, pow_one, one_mul, PadicInt.coe_mul, PadicInt.coe_neg] at h
    rw [h]
    have hf := norm_two_sign_identity (ha.map (PadicInt.toZModPow 3)).unit
      (hb.map (PadicInt.toZModPow 3)).unit
    simpa only [IsUnit.unit_spec, map_mul, map_neg] using hf

/-- The dyadic valuation and unit-residue formula for arbitrary nonzero factors.
Source: Serre, A Course in Arithmetic, Chapter III, §1, Theorem 1. -/
theorem binaryNormSymbol_two (a b : ℤ_[2]) (ha : IsUnit a) (hb : IsUnit b) (m n : ℤ) :
    binaryNormSymbol ℚ_[2] ((2 : ℚ_[2]) ^ m * a) ((2 : ℚ_[2]) ^ n * b) =
      (-1 : ℤ) ^ ((PadicInt.toZModPow 3 a).val / 2 * ((PadicInt.toZModPow 3 b).val / 2) +
        (n % 2).toNat * (((PadicInt.toZModPow 3 a).val ^ 2 - 1) / 8) +
        (m % 2).toNat * (((PadicInt.toZModPow 3 b).val ^ 2 - 1) / 8)) := by
  rw [binaryNormSymbol_zpow_reduce _ _ _ (by norm_num : (2 : ℚ_[2]) ≠ 0)
    (PadicInt.coe_ne_zero.mpr ha.ne_zero) (PadicInt.coe_ne_zero.mpr hb.ne_zero)]
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn
  · simpa [hm, hn] using binaryNormSymbol_two_parity a b ha hb 0 0
  · simpa [hm, hn] using binaryNormSymbol_two_parity a b ha hb 0 1
  · simpa [hm, hn] using binaryNormSymbol_two_parity a b ha hb 1 0
  · simpa [hm, hn] using binaryNormSymbol_two_parity a b ha hb 1 1

theorem binaryNormSymbol_at_odd_prime (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hpq : p ≠ q) :
    binaryNormSymbol ℚ_[p] (p : ℚ_[p]) (q : ℚ_[p]) = legendreSym p q := by
  have hcop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq
  have hqu : IsUnit (q : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have h := binaryNormSymbol_padic_unit_prime p hp (q : ℤ_[p]) 1 hqu isUnit_one
  rw [binaryNormSymbol_symm _ _
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)]
  simpa only [PadicInt.coe_natCast, PadicInt.coe_one, mul_one, map_natCast,
    ZMod.val_natCast, Int.natCast_emod, Nat.cast_id] using h.trans (by
      simpa using (legendreSym.mod p (q : ℤ)).symm)

theorem binaryNormSymbol_two_odd_primes (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    binaryNormSymbol ℚ_[2] (p : ℚ_[2]) (q : ℚ_[2]) =
      (-1 : ℤ) ^ (p / 2 * (q / 2)) := by
  have hpu : IsUnit (p : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm))
  have hqu : IsUnit (q : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Nat.prime_two (Fact.out : q.Prime)).mpr hq.symm))
  have h := binaryNormSymbol_two_unit (p : ℤ_[2]) q hpu hqu 0
  simp only [Fin.val_zero, pow_zero, one_mul, zero_mul, add_zero, PadicInt.coe_natCast,
    map_natCast, ZMod.val_natCast] at h
  rw [h, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (p / 2 * (q / 2))]
  congr 1
  rw [Nat.mul_mod, Nat.mul_mod (p / 2) (q / 2)]
  have hpmod : p % 2 ^ 3 / 2 % 2 = p / 2 % 2 := by omega
  have hqmod : q % 2 ^ 3 / 2 % 2 = q / 2 % 2 := by omega
  rw [hpmod, hqmod]

/-- The product formula on two distinct odd prime generators follows from reciprocity.
Source: Serre, A Course in Arithmetic, Chapter III, §2, Theorem 3. -/
theorem binaryNormSymbol_prime_pair_product (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    binaryNormSymbol ℝ (p : ℝ) (q : ℝ) *
      binaryNormSymbol ℚ_[2] (p : ℚ_[2]) (q : ℚ_[2]) *
      binaryNormSymbol ℚ_[p] (p : ℚ_[p]) (q : ℚ_[p]) *
      binaryNormSymbol ℚ_[q] (p : ℚ_[q]) (q : ℚ_[q]) = 1 := by
  have hp₀ : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hq₀ : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  rw [binaryNormSymbol_real _ _ hp₀ hq₀,
    ite_eq_right (by intro h; exact (not_lt_of_ge (Nat.cast_nonneg p)) h.1), one_mul,
    binaryNormSymbol_two_odd_primes p q hp hq,
    binaryNormSymbol_at_odd_prime p q hp hpq,
    binaryNormSymbol_symm (p : ℚ_[q]) q
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero),
    binaryNormSymbol_at_odd_prime q p hq hpq.symm]
  have hrec := legendreSym.quadratic_reciprocity hp hq hpq
  calc
    (-1 : ℤ) ^ (p / 2 * (q / 2)) * legendreSym p q * legendreSym q p =
        ((-1 : ℤ) ^ (p / 2 * (q / 2))) ^ 2 := by rw [← hrec]; ring
    _ = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

set_option maxHeartbeats 400000 in
theorem norm_odd_multiplicative_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b c : ℤ_[p]) (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (m n k : ℤ) :
    binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ m * a) ((p : ℚ_[p]) ^ (n + k) * (b * c)) =
      binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ m * a) ((p : ℚ_[p]) ^ n * b) *
      binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ m * a) ((p : ℚ_[p]) ^ k * c) := by
  rw [← PadicInt.coe_mul]
  rw [binaryNormSymbol_padic_odd p hp a (b * c) ha (hb.mul hc),
    binaryNormSymbol_padic_odd p hp a b ha hb, binaryNormSymbol_padic_odd p hp a c ha hc]
  have hneg : quadraticChar (ZMod p) (-PadicInt.toZMod a) =
      quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (PadicInt.toZMod a) := by
    rw [neg_eq_neg_one_mul, map_mul]
  simp only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val,
    map_mul, map_neg, hneg]
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hχa := quadraticChar_dichotomy (ha.map PadicInt.toZMod).ne_zero
  have hχn := quadraticChar_dichotomy (show (-1 : ZMod p) ≠ 0 by simp)
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> rcases hk with hk | hk <;>
    rcases hχa with hχa | hχa <;> rcases hχn with hχn | hχn <;>
    simp [Int.add_emod, hm, hn, hk, hχa, hχn] <;> ring

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem norm_two_multiplicative_signs : ∀ (a b c : (ZMod 8)ˣ) (e f g : Fin 2),
    (-1 : ℤ) ^ (((a : ZMod 8).val / 2) * (((b * c : (ZMod 8)ˣ) : ZMod 8).val / 2) +
      (f + g).val * (((a : ZMod 8).val ^ 2 - 1) / 8) +
      e.val * ((((b * c : (ZMod 8)ˣ) : ZMod 8).val ^ 2 - 1) / 8)) =
    (-1 : ℤ) ^ (((a : ZMod 8).val / 2) * ((b : ZMod 8).val / 2) +
      f.val * (((a : ZMod 8).val ^ 2 - 1) / 8) +
      e.val * (((b : ZMod 8).val ^ 2 - 1) / 8)) *
    (-1 : ℤ) ^ (((a : ZMod 8).val / 2) * ((c : ZMod 8).val / 2) +
      g.val * (((a : ZMod 8).val ^ 2 - 1) / 8) +
      e.val * (((c : ZMod 8).val ^ 2 - 1) / 8)) := by
  decide

theorem norm_two_multiplicative_units (a b c : ℤ_[2])
    (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (m n k : ℤ) :
    binaryNormSymbol ℚ_[2] ((2 : ℚ_[2]) ^ m * a) ((2 : ℚ_[2]) ^ (n + k) * (b * c)) =
      binaryNormSymbol ℚ_[2] ((2 : ℚ_[2]) ^ m * a) ((2 : ℚ_[2]) ^ n * b) *
      binaryNormSymbol ℚ_[2] ((2 : ℚ_[2]) ^ m * a) ((2 : ℚ_[2]) ^ k * c) := by
  rw [← PadicInt.coe_mul]
  rw [binaryNormSymbol_two a (b * c) ha (hb.mul hc),
    binaryNormSymbol_two a b ha hb, binaryNormSymbol_two a c ha hc]
  have hf := norm_two_multiplicative_signs (ha.map (PadicInt.toZModPow 3)).unit
    (hb.map (PadicInt.toZModPow 3)).unit (hc.map (PadicInt.toZModPow 3)).unit
  simp only [Units.val_mul, IsUnit.unit_spec] at hf
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> rcases hk with hk | hk
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 0 0 0
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 0 0 1
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 0 1 0
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 0 1 1
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 1 0 0
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 1 0 1
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 1 1 0
  · simpa [Int.add_emod, hm, hn, hk, map_mul] using hf 1 1 1

theorem binaryNormSymbol_padic_mul_right (p : ℕ) [Fact p.Prime]
    (x y z : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    binaryNormSymbol ℚ_[p] x (y * z) =
      binaryNormSymbol ℚ_[p] x y * binaryNormSymbol ℚ_[p] x z := by
  obtain ⟨a, ha, hxa⟩ := padic_unit_decomposition p x hx
  obtain ⟨b, hb, hyb⟩ := padic_unit_decomposition p y hy
  obtain ⟨c, hc, hzc⟩ := padic_unit_decomposition p z hz
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hyz : y * z = (p : ℚ_[p]) ^ (y.valuation + z.valuation) * ((b : ℚ_[p]) * c) := by
    conv_lhs => rw [hyb, hzc]
    rw [zpow_add₀ hp]
    ring
  have h : binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ x.valuation * a)
      ((p : ℚ_[p]) ^ (y.valuation + z.valuation) * (b * c)) =
      binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ x.valuation * a) ((p : ℚ_[p]) ^ y.valuation * b) *
      binaryNormSymbol ℚ_[p] ((p : ℚ_[p]) ^ x.valuation * a) ((p : ℚ_[p]) ^ z.valuation * c) := by
    by_cases hp₂ : p = 2
    · subst p
      exact norm_two_multiplicative_units a b c ha hb hc _ _ _
    · exact norm_odd_multiplicative_units p hp₂ a b c ha hb hc _ _ _
  rwa [← hxa, ← hyb, ← hzc, ← hyz] at h

theorem binaryNormSymbol_real_mul_right (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    binaryNormSymbol ℝ a (b * c) = binaryNormSymbol ℝ a b * binaryNormSymbol ℝ a c := by
  rw [binaryNormSymbol_real _ _ ha (mul_ne_zero hb hc),
    binaryNormSymbol_real _ _ ha hb, binaryNormSymbol_real _ _ ha hc]
  rcases lt_or_gt_of_ne ha with ha | ha <;>
    rcases lt_or_gt_of_ne hb with hb | hb <;>
      rcases lt_or_gt_of_ne hc with hc | hc <;>
      simp [ha, hb, hc, not_lt_of_ge ha.le, not_lt_of_ge hb.le, not_lt_of_ge hc.le,
        mul_pos_of_neg_of_neg, mul_pos, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  · exact (mul_pos_of_neg_of_neg hb hc).le
  · exact hc.le

/-- The product of the real and finite local norm signs.
Source: Serre, A Course in Arithmetic, Chapter III, §2. -/
def rationalNormProduct (a b : ℚ) : ℤ :=
  binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
    ∏ᶠ p : Nat.Primes, binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val])

theorem norm_finiteMulSupport (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.HasFiniteMulSupport
      (fun p : Nat.Primes => binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val])) := by
  obtain ⟨S, _, hS⟩ := binaryNormSymbol_finite_support a b ha hb
  apply (S.finite_toSet.preimage (f := fun p : Nat.Primes => p.val)
    (fun _ _ _ _ h => Subtype.ext h)).subset
  intro p hp
  by_contra h
  exact hp (hS p.val h)

theorem rationalNormProduct_mul_right (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    rationalNormProduct a (b * c) = rationalNormProduct a b * rationalNormProduct a c := by
  unfold rationalNormProduct
  simp only [Rat.cast_mul]
  rw [binaryNormSymbol_real_mul_right _ _ _ (Rat.cast_ne_zero.mpr ha)
    (Rat.cast_ne_zero.mpr hb) (Rat.cast_ne_zero.mpr hc)]
  have h : (fun p : Nat.Primes => binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val])
      ((b : ℚ_[p.val]) * (c : ℚ_[p.val]))) =
      fun p : Nat.Primes => binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) *
        binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (c : ℚ_[p.val]) := by
    funext p
    exact binaryNormSymbol_padic_mul_right p.val _ _ _ (Rat.cast_ne_zero.mpr ha)
      (Rat.cast_ne_zero.mpr hb) (Rat.cast_ne_zero.mpr hc)
  rw [h, finprod_mul_distrib (norm_finiteMulSupport a b ha hb) (norm_finiteMulSupport a c ha hc)]
  ring

theorem rationalNormProduct_symm (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    rationalNormProduct a b = rationalNormProduct b a := by
  unfold rationalNormProduct
  rw [binaryNormSymbol_symm _ _ (Rat.cast_ne_zero.mpr ha) (Rat.cast_ne_zero.mpr hb)]
  congr 1
  apply finprod_congr
  intro p
  exact binaryNormSymbol_symm _ _ (Rat.cast_ne_zero.mpr ha) (Rat.cast_ne_zero.mpr hb)

theorem binaryNormSymbol_one_right {K : Type*} [Field K] (a : K) :
    binaryNormSymbol K a 1 = 1 := by
  rw [binaryNormSymbol_eq_one]
  exact ⟨1, 0, by simp⟩

theorem rationalNormProduct_one (a : ℚ) : rationalNormProduct a 1 = 1 := by
  simp only [rationalNormProduct, Rat.cast_one, binaryNormSymbol_one_right, finprod_one, mul_one]

theorem rationalNormProduct_restrict (a b : ℚ) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∉ S →
      binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) = 1) :
    rationalNormProduct a b = binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
      ∏ p ∈ S, binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) := by
  unfold rationalNormProduct
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  intro p hp
  by_contra h
  exact hp (hS p h)

theorem rational_multiplicative_generators (F : ℚ → ℤ)
    (hmul : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → F (a * b) = F a * F b)
    (h1 : F 1 = 1) (hneg : F (-1) = 1)
    (hprime : ∀ p : ℕ, p.Prime → F p = 1) (x : ℚ) (hx : x ≠ 0) : F x = 1 := by
  have hn : ∀ n : ℕ, n ≠ 0 → F n = 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; contradiction
    | one => intro _; exact h1
    | prime p hp => intro _; exact hprime p hp
    | mul a b ha hb =>
      intro h
      have ha₀ : a ≠ 0 := left_ne_zero_of_mul h
      have hb₀ : b ≠ 0 := right_ne_zero_of_mul h
      rw [Nat.cast_mul, hmul _ _ (Nat.cast_ne_zero.mpr ha₀) (Nat.cast_ne_zero.mpr hb₀),
        ha ha₀, hb hb₀, one_mul]
  have hi : ∀ n : ℤ, n ≠ 0 → F n = 1 := by
    intro n hn₀
    cases n with
    | ofNat n => exact hn n (by intro h; subst n; exact hn₀ rfl)
    | negSucc n =>
      change F (-((n + 1 : ℕ) : ℚ)) = 1
      rw [neg_eq_neg_one_mul, hmul _ _ (by norm_num) (by positivity), hneg,
        hn (n + 1) (by omega), one_mul]
  have hd : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_ne_zero
  have he : x * (x.den : ℚ) = x.num := by
    exact ((div_eq_iff hd).mp (Rat.num_div_den x)).symm
  have h := hmul x x.den hx hd
  rw [he, hn x.den x.den_ne_zero, hi x.num (Rat.num_ne_zero.mpr hx), mul_one] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormProduct_pair_support (a b : ℚ) (p q : Nat.Primes)
    (hp : p.val ≠ 2) (hq : q.val ≠ 2) (hpq : p ≠ q)
    (hS : ∀ r : Nat.Primes, r.val ≠ 2 → r ≠ p → r ≠ q →
      binaryNormSymbol ℚ_[r.val] (a : ℚ_[r.val]) (b : ℚ_[r.val]) = 1) :
    rationalNormProduct a b = binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
      binaryNormSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) *
      binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) *
      binaryNormSymbol ℚ_[q.val] (a : ℚ_[q.val]) (b : ℚ_[q.val]) := by
  classical
  let t : Nat.Primes := ⟨2, Nat.prime_two⟩
  have htp : t ≠ p := fun h => hp (congrArg Subtype.val h).symm
  have htq : t ≠ q := fun h => hq (congrArg Subtype.val h).symm
  rw [rationalNormProduct_restrict a b {t, p, q} (by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact hS r (fun h => hr.1 (Subtype.ext h)) hr.2.1 hr.2.2)]
  simp only [Finset.prod_insert (by simp [htp, htq] : t ∉ ({p, q} : Finset Nat.Primes)),
    Finset.prod_insert (by simpa using hpq : p ∉ ({q} : Finset Nat.Primes)), Finset.prod_singleton]
  dsimp [t]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormProduct_single_support (a b : ℚ) (p : Nat.Primes) (hp : p.val ≠ 2)
    (hS : ∀ r : Nat.Primes, r.val ≠ 2 → r ≠ p →
      binaryNormSymbol ℚ_[r.val] (a : ℚ_[r.val]) (b : ℚ_[r.val]) = 1) :
    rationalNormProduct a b = binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
      binaryNormSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) *
      binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) := by
  classical
  let t : Nat.Primes := ⟨2, Nat.prime_two⟩
  have htp : t ≠ p := fun h => hp (congrArg Subtype.val h).symm
  rw [rationalNormProduct_restrict a b {t, p} (by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact hS r (fun h => hr.1 (Subtype.ext h)) hr.2)]
  simp only [Finset.prod_insert (by simpa using htp : t ∉ ({p} : Finset Nat.Primes)), Finset.prod_singleton]
  dsimp [t]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormProduct_two_support (a b : ℚ)
    (hS : ∀ r : Nat.Primes, r.val ≠ 2 →
      binaryNormSymbol ℚ_[r.val] (a : ℚ_[r.val]) (b : ℚ_[r.val]) = 1) :
    rationalNormProduct a b = binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
      binaryNormSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) := by
  classical
  rw [rationalNormProduct_restrict a b {⟨2, Nat.prime_two⟩} (by
    intro r hr
    exact hS r (fun h => hr (Finset.mem_singleton.mpr (Subtype.ext h))))]
  rw [Finset.prod_singleton]

theorem binaryNormSymbol_integer_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (u : ℤ) (hu : IsCoprime u p) :
    binaryNormSymbol ℚ_[p] (u : ℚ_[p]) (p : ℚ_[p]) = legendreSym p u := by
  have hunit : IsUnit (u : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (by simpa only [← PadicInt.norm_coe, PadicInt.coe_intCast] using Padic.norm_intCast_eq_one_iff.mpr hu)
  have h := binaryNormSymbol_padic_unit_prime p hp (u : ℤ_[p]) 1 hunit isUnit_one
  simpa only [PadicInt.coe_intCast, PadicInt.coe_one, mul_one, legendreSym,
    Int.cast_natCast, ZMod.natCast_zmod_val, map_intCast] using h

theorem binaryNormSymbol_two_neg_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    binaryNormSymbol ℚ_[2] (-1) (p : ℚ_[2]) = legendreSym p (-1) := by
  have hpu : IsUnit (p : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm))
  have h := binaryNormSymbol_two_unit (-1) p isUnit_one.neg hpu 0
  norm_num only [Fin.val_zero, pow_zero, one_mul, zero_mul, add_zero,
    map_neg, map_one, map_natCast, PadicInt.coe_neg, PadicInt.coe_one,
    PadicInt.coe_natCast, ZMod.val_natCast] at h
  rw [h, legendreSym.at_neg_one hp,
    ZMod.χ₄_eq_neg_one_pow ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp),
    neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (p / 2)]
  congr 1
  norm_num
  omega

theorem binaryNormSymbol_two_two_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    binaryNormSymbol ℚ_[2] (2 : ℚ_[2]) (p : ℚ_[2]) = legendreSym p 2 := by
  have hpu : IsUnit (p : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm))
  rw [binaryNormSymbol_symm _ _ (by norm_num)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  have h := binaryNormSymbol_two_unit (p : ℤ_[2]) 1 hpu isUnit_one 1
  simp only [Fin.val_one, pow_one, mul_one, one_mul, map_one, map_natCast,
    PadicInt.coe_one, PadicInt.coe_natCast, ZMod.val_natCast] at h
  norm_num [show (1 : ZMod 8).val = 1 by decide] at h
  rw [h, legendreSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
  have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  have hcases : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hcases with h | h | h | h <;> norm_num [hodd, h]

theorem norm_prime_unit_at_other (p q : Nat.Primes) (hpq : p ≠ q) :
    ‖(q.val : ℚ_[p.val])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  exact (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h))

theorem rationalNormProduct_distinct_odd (p q : Nat.Primes)
    (hp : p.val ≠ 2) (hq : q.val ≠ 2) (hpq : p ≠ q) :
    rationalNormProduct p.val q.val = 1 := by
  rw [rationalNormProduct_pair_support _ _ p q hp hq hpq (by
    intro r hr₂ hrp hrq
    simp only [Rat.cast_natCast]
    exact binaryNormSymbol_padic_units r.val hr₂ _ _
      (norm_prime_unit_at_other r p hrp) (norm_prime_unit_at_other r q hrq))]
  simpa only [Rat.cast_natCast] using binaryNormSymbol_prime_pair_product p.val q.val hp hq
    (fun h => hpq (Subtype.ext h))

theorem binaryNormSymbol_real_nonneg_right (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hb₀ : 0 ≤ b) :
    binaryNormSymbol ℝ a b = 1 := by
  rw [binaryNormSymbol_real a b ha hb, ite_eq_right]
  exact fun h => (not_lt_of_ge hb₀) h.2

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormProduct_neg_odd_prime (p : Nat.Primes) (hp : p.val ≠ 2) :
    rationalNormProduct (-1) p.val = 1 := by
  rw [rationalNormProduct_single_support _ _ p hp (by
    intro r hr₂ hrp
    simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
    exact binaryNormSymbol_padic_units r.val hr₂ _ _ (by simp)
      (norm_prime_unit_at_other r p hrp))]
  simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]
  rw [binaryNormSymbol_real_nonneg_right _ _ (by norm_num)
      (Nat.cast_ne_zero.mpr p.property.ne_zero) (Nat.cast_nonneg _), one_mul,
    binaryNormSymbol_two_neg_prime p.val hp]
  have h := binaryNormSymbol_integer_prime p.val hp (-1) isCoprime_one_left.neg_left
  norm_num only [Int.cast_neg, Int.cast_one] at h
  rw [h, ← sq]
  exact legendreSym.sq_one p.val (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem rationalNormProduct_two_odd_prime (p : Nat.Primes) (hp : p.val ≠ 2) :
    rationalNormProduct 2 p.val = 1 := by
  rw [rationalNormProduct_single_support _ _ p hp (by
    intro r hr₂ hrp
    simp only [Rat.cast_ofNat, Rat.cast_natCast]
    apply binaryNormSymbol_padic_units r.val hr₂
    · exact Padic.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes r.property Nat.prime_two).mpr hr₂)
    · exact norm_prime_unit_at_other r p hrp)]
  simp only [Rat.cast_ofNat, Rat.cast_natCast]
  rw [binaryNormSymbol_real_nonneg_right _ _ (by norm_num)
      (Nat.cast_ne_zero.mpr p.property.ne_zero) (Nat.cast_nonneg _), one_mul,
    binaryNormSymbol_two_two_prime p.val hp]
  have hcop : IsCoprime (2 : ℤ) p.val :=
    (Nat.coprime_primes Nat.prime_two p.property).mpr hp.symm |>.isCoprime
  have h := binaryNormSymbol_integer_prime p.val hp 2 hcop
  norm_num only [Int.cast_ofNat] at h
  rw [h, ← sq]
  apply legendreSym.sq_one
  simpa only [Nat.cast_ofNat, Int.cast_ofNat] using
    ((ZMod.isUnit_iff_coprime 2 p.val).mpr
      ((Nat.coprime_primes Nat.prime_two p.property).mpr hp.symm)).ne_zero

theorem rationalNormProduct_neg_neg : rationalNormProduct (-1) (-1) = 1 := by
  rw [rationalNormProduct_two_support _ _ (by
    intro r hr
    simp only [Rat.cast_neg, Rat.cast_one]
    exact binaryNormSymbol_padic_units r.val hr _ _ (by simp) (by simp))]
  simp only [Rat.cast_neg, Rat.cast_one]
  rw [binaryNormSymbol_real _ _ (by norm_num) (by norm_num)]
  have h := binaryNormSymbol_two_unit (-1) (-1) isUnit_one.neg isUnit_one.neg 0
  norm_num at h ⊢
  linarith

theorem rationalNormProduct_neg_two : rationalNormProduct (-1) 2 = 1 := by
  rw [rationalNormProduct_two_support _ _ (by
    intro r hr
    simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
    apply binaryNormSymbol_padic_units r.val hr
    · simp
    · exact Padic.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes r.property Nat.prime_two).mpr hr))]
  simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
  rw [binaryNormSymbol_real_nonneg_right _ _ (by norm_num) (by norm_num) (by norm_num), one_mul]
  have h := binaryNormSymbol_two_unit (-1) 1 isUnit_one.neg isUnit_one 1
  norm_num at h
  exact h

theorem binaryNormSymbol_self {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    binaryNormSymbol K a a = binaryNormSymbol K a (-1) := by
  simpa using binaryNormSymbol_neg_mul a (-1) ha

theorem rationalNormProduct_self (a : ℚ) (ha : a ≠ 0) :
    rationalNormProduct a a = rationalNormProduct a (-1) := by
  unfold rationalNormProduct
  simp only [Rat.cast_neg, Rat.cast_one]
  rw [binaryNormSymbol_self _ (Rat.cast_ne_zero.mpr ha)]
  congr 1
  apply finprod_congr
  intro p
  exact binaryNormSymbol_self _ (Rat.cast_ne_zero.mpr ha)

theorem rationalNormProduct_neg_prime (p : Nat.Primes) : rationalNormProduct (-1) p.val = 1 := by
  by_cases hp : p.val = 2
  · rw [hp]
    exact rationalNormProduct_neg_two
  · exact rationalNormProduct_neg_odd_prime p hp

theorem rationalNormProduct_primes (p q : Nat.Primes) : rationalNormProduct p.val q.val = 1 := by
  have hp₀ : (p.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hq₀ : (q.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.property.ne_zero
  by_cases hpq : p = q
  · subst q
    rw [rationalNormProduct_self _ hp₀, rationalNormProduct_symm _ _ hp₀ (by norm_num)]
    exact rationalNormProduct_neg_prime p
  · by_cases hp : p.val = 2
    · rw [hp]
      exact rationalNormProduct_two_odd_prime q
        (fun hq => hpq (Subtype.ext (hp.trans hq.symm)))
    · by_cases hq : q.val = 2
      · rw [rationalNormProduct_symm _ _ hp₀ hq₀, hq]
        exact rationalNormProduct_two_odd_prime p hp
      · exact rationalNormProduct_distinct_odd p q hp hq hpq

theorem rationalNormProduct_mul_left (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    rationalNormProduct (a * b) c = rationalNormProduct a c * rationalNormProduct b c := by
  rw [rationalNormProduct_symm _ _ (mul_ne_zero ha hb) hc,
    rationalNormProduct_mul_right _ _ _ hc ha hb,
    rationalNormProduct_symm c a hc ha, rationalNormProduct_symm c b hc hb]

/-- The restricted Hilbert product formula for nonzero rational coefficients.
Source: Serre, A Course in Arithmetic, Chapter III, §2, Theorem 3. -/
theorem binaryNormSymbol_product (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    binaryNormSymbol ℝ (a : ℝ) (b : ℝ) *
      (∏ᶠ p : Nat.Primes, binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val])) = 1 := by
  change rationalNormProduct a b = 1
  have hneg (x : ℚ) (hx : x ≠ 0) : rationalNormProduct x (-1) = 1 := by
    apply rational_multiplicative_generators (fun x => rationalNormProduct x (-1))
      (fun x y hx hy => rationalNormProduct_mul_left x y (-1) hx hy (by norm_num))
    · rw [rationalNormProduct_symm _ _ one_ne_zero (by norm_num), rationalNormProduct_one]
    · exact rationalNormProduct_neg_neg
    · intro p hp
      rw [rationalNormProduct_symm _ _ (Nat.cast_ne_zero.mpr hp.ne_zero) (by norm_num)]
      exact rationalNormProduct_neg_prime ⟨p, hp⟩
    · exact hx
  have hprime (p : ℕ) (hp : p.Prime) (x : ℚ) (hx : x ≠ 0) : rationalNormProduct x p = 1 := by
    apply rational_multiplicative_generators (fun x => rationalNormProduct x p)
      (fun x y hx hy => rationalNormProduct_mul_left x y p hx hy (Nat.cast_ne_zero.mpr hp.ne_zero))
    · rw [rationalNormProduct_symm _ _ one_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero), rationalNormProduct_one]
    · exact rationalNormProduct_neg_prime ⟨p, hp⟩
    · intro q hq
      exact rationalNormProduct_primes ⟨q, hq⟩ ⟨p, hp⟩
    · exact hx
  exact rational_multiplicative_generators (fun x => rationalNormProduct a x)
    (fun x y hx hy => rationalNormProduct_mul_right a x y ha hx hy)
    (rationalNormProduct_one a) (hneg a ha) (fun p hp => hprime p hp a ha) b hb

/-- Local ternary isotropy at the real place and every other prime forces it at the missing prime.
Source: Serre, A Course in Arithmetic, Chapter III, §2, Theorem 3. -/
theorem ternary_missing_prime (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (q : Nat.Primes)
    (hr : ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 - (a : ℝ) * y ^ 2 = (b : ℝ) * z ^ 2)
    (hf : ∀ p : Nat.Primes, p ≠ q → ∃ x y z : ℚ_[p.val],
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - (a : ℚ_[p.val]) * y ^ 2 = (b : ℚ_[p.val]) * z ^ 2) :
    ∃ x y z : ℚ_[q.val], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 - (a : ℚ_[q.val]) * y ^ 2 = (b : ℚ_[q.val]) * z ^ 2 := by
  classical
  have hr' := (binaryNormSymbol_eq_one_iff_ternary _ _ (Rat.cast_ne_zero.mpr ha)).mpr hr
  have hf' (p : Nat.Primes) (hp : p ≠ q) :
      binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) = 1 :=
    (binaryNormSymbol_eq_one_iff_ternary _ _ (Rat.cast_ne_zero.mpr ha)).mpr (hf p hp)
  have h := binaryNormSymbol_product a b ha hb
  rw [hr', one_mul, finprod_eq_prod_of_mulSupport_subset _ (s := {q}) (by
    intro p hp
    by_contra hn
    exact hp (hf' p (by simpa using hn))), Finset.prod_singleton] at h
  exact (binaryNormSymbol_eq_one_iff_ternary _ _ (Rat.cast_ne_zero.mpr ha)).mp h

/-- Local ternary isotropy at every finite place forces real isotropy.
Source: Serre, A Course in Arithmetic, Chapter III, §2, Theorem 3. -/
theorem ternary_missing_real (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : ∀ p : Nat.Primes, ∃ x y z : ℚ_[p.val],
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - (a : ℚ_[p.val]) * y ^ 2 = (b : ℚ_[p.val]) * z ^ 2) :
    ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x ^ 2 - (a : ℝ) * y ^ 2 = (b : ℝ) * z ^ 2 := by
  have hf' (p : Nat.Primes) :
      binaryNormSymbol ℚ_[p.val] (a : ℚ_[p.val]) (b : ℚ_[p.val]) = 1 :=
    (binaryNormSymbol_eq_one_iff_ternary _ _ (Rat.cast_ne_zero.mpr ha)).mpr (hf p)
  have h := binaryNormSymbol_product a b ha hb
  simp only [hf', finprod_one, mul_one] at h
  exact (binaryNormSymbol_eq_one_iff_ternary _ _ (Rat.cast_ne_zero.mpr ha)).mp h

example : binaryNormSymbol ℚ_[2] (-1) (-1) = -1 := by
  have h := binaryNormSymbol_two_unit (-1) (-1) isUnit_one.neg isUnit_one.neg 0
  norm_num at h
  exact h

example : binaryNormSymbol ℝ (-1) (-1) = -1 := by
  rw [binaryNormSymbol_real _ _ (by norm_num) (by norm_num)]
  norm_num

end HodgeLean.Foundations.MeyerRational
