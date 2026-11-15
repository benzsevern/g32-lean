import HodgeLean.Foundations.MeyerRationalS5
import Mathlib.FieldTheory.Finite.Basic

/-! Local isotropy of regular diagonal forms in five variables over `ℚ_[p]`. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

theorem isotropic_of_smul {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) (c : K) (hc : c ≠ 0)
    (h : ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, c * a i * x i ^ 2 = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨x, hx, hs⟩ := h
  refine ⟨x, hx, ?_⟩
  simp_rw [mul_assoc, ← Finset.mul_sum] at hs
  exact (mul_eq_zero.mp hs).resolve_left hc

theorem isotropic_of_square_mul {K : Type*} [Field K] {n : ℕ} (a b c : Fin n → K)
    (hc : ∀ i, c i ≠ 0) (hab : ∀ i, a i = b i * c i ^ 2)
    (h : ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨y, hy, hs⟩ := h
  refine ⟨fun i => y i / c i, ?_, ?_⟩
  · intro h0
    apply hy
    funext i
    have := congrFun h0 i
    simpa [hc i] using this
  · rw [← hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hab i]
    field_simp [hc i]

theorem isotropic_of_comp {K : Type*} [Field K] {n : ℕ} (a : Fin n → K)
    (σ : Fin n → Fin n) (hσ : Function.Injective σ)
    (h : ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a (σ i) * x i ^ 2 = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨y, hy, hs⟩ := h
  let e := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ)
  refine ⟨fun j => y (e.symm j), ?_, ?_⟩
  · intro h0
    apply hy
    funext i
    simpa using congrFun h0 (e i)
  · rw [← hs, ← e.sum_comp]
    simp [e]

theorem isotropic_of_first {K : Type*} [Field K] (b : Fin 5 → K) (hb : b 0 ≠ 0)
    (X : K) (Y : Fin 5 → K) (hX : X ≠ 0)
    (hXY : X * X = -(b 1 * Y 1 ^ 2 + b 2 * Y 2 ^ 2 + b 3 * Y 3 ^ 2 + b 4 * Y 4 ^ 2) / b 0) :
    ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0 := by
  refine ⟨![X, Y 1, Y 2, Y 3, Y 4], fun h => hX (by simpa using congrFun h 0), ?_⟩
  have h0 : b 0 * X ^ 2 =
      -(b 1 * Y 1 ^ 2 + b 2 * Y 2 ^ 2 + b 3 * Y 3 ^ 2 + b 4 * Y 4 ^ 2) := by
    rw [sq, hXY]; field_simp
  simp [Fin.sum_univ_five]
  linear_combination h0

theorem square_normal_form (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ (x / c ^ 2).valuation = x.valuation % 2 := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine ⟨(p : ℚ_[p]) ^ (x.valuation / 2), zpow_ne_zero _ hp, ?_⟩
  have hc : ((p : ℚ_[p]) ^ (x.valuation / 2)) ^ 2 ≠ 0 := pow_ne_zero _ (zpow_ne_zero _ hp)
  rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hc), Padic.valuation_inv,
    Padic.valuation_pow, Padic.valuation_zpow, Padic.valuation_p]
  simp only [Nat.cast_ofNat]
  omega

theorem three_same_parity_aux : ∀ b0 b1 b2 b3 b4 : Bool, ∃ i j k l m : Fin 5,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m ∧
    ![b0, b1, b2, b3, b4] i = ![b0, b1, b2, b3, b4] j ∧
    ![b0, b1, b2, b3, b4] j = ![b0, b1, b2, b3, b4] k := by
  decide

theorem three_same_parity (e : Fin 5 → Bool) :
    ∃ σ : Fin 5 → Fin 5, Function.Injective σ ∧ e (σ 0) = e (σ 1) ∧ e (σ 1) = e (σ 2) := by
  obtain ⟨i, j, k, l, m, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hij, hjk⟩ :=
    three_same_parity_aux (e 0) (e 1) (e 2) (e 3) (e 4)
  have he : ![e 0, e 1, e 2, e 3, e 4] = e := by
    funext t; fin_cases t <;> rfl
  rw [he] at hij hjk
  refine ⟨![i, j, k, l, m], ?_, hij, hjk⟩
  intro s t hst
  fin_cases s <;> fin_cases t <;> simp_all [eq_comm]

theorem norm_eq_one_of_valuation (p : ℕ) [Fact p.Prime] (b : ℚ_[p]) (hb : b ≠ 0)
    (hv : b.valuation = 0) : ‖b‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation hb, hv]
  simp

theorem square_quotient_of_residue_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (u v : ℤ_[p]) (hu : IsUnit u) (h : PadicInt.toZMod v = PadicInt.toZMod u) :
    IsSquare ((v : ℚ_[p]) / (u : ℚ_[p])) := by
  have hunit : ∀ z : ℤ_[p], PadicInt.toZMod z ≠ 0 → IsUnit z := by
    intro z hz
    by_contra hn
    apply hz
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact hn
  let w : ℤ_[p] := v * ↑hu.unit⁻¹
  have hw1 : PadicInt.toZMod w = 1 := by
    have hi : PadicInt.toZMod u * PadicInt.toZMod (↑hu.unit⁻¹ : ℤ_[p]) = 1 := by
      rw [← map_mul, hu.mul_val_inv, map_one]
    simp only [w, map_mul, h, hi]
  have hwu : IsUnit w := hunit w (by rw [hw1]; exact one_ne_zero)
  obtain ⟨z, hz⟩ := (unit_square_odd p hp w hwu).mpr ⟨1, by rw [hw1, mul_one]⟩
  refine ⟨(z : ℚ_[p]), ?_⟩
  have hu' : (u : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  have hv : v = w * u := by
    simp only [w, mul_assoc]
    rw [hu.val_inv_mul, mul_one]
  rw [div_eq_iff hu', hv, hz]
  push_cast
  ring

theorem odd_ternary_residue (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (r0 r1 r2 : ZMod p)
    (h1 : r1 ≠ 0) (h2 : r2 ≠ 0) :
    ∃ y1 y2 : ZMod p, r0 + r1 * y1 ^ 2 + r2 * y2 ^ 2 = 0 := by
  open Polynomial in
  have hf : degree (C r1 * X ^ 2) = 2 := degree_C_mul_X_pow 2 h1
  open Polynomial in
  have hg : degree (C r2 * X ^ 2 + C r0) = 2 := by
    rw [degree_add_C (by rw [degree_C_mul_X_pow 2 h2]; norm_num), degree_C_mul_X_pow 2 h2]
    rfl
  have hc : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  obtain ⟨y1, y2, hy⟩ := FiniteField.exists_root_sum_quadratic hf hg hc
  refine ⟨y1, y2, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hy
  linear_combination hy

/-- A coefficient of nonnegative valuation as a local integer. -/
def intOf (p : ℕ) [Fact p.Prime] (b : ℚ_[p]) (hv : 0 ≤ b.valuation) : ℤ_[p] :=
  ⟨b, (Padic.norm_le_one_iff_val_nonneg b).2 hv⟩

theorem intOf_isUnit (p : ℕ) [Fact p.Prime] (b : ℚ_[p]) (hb : b ≠ 0)
    (hv : b.valuation = 0) : IsUnit (intOf p b hv.ge) :=
  PadicInt.isUnit_iff.mpr (norm_eq_one_of_valuation p b hb hv)

theorem odd_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (b : Fin 5 → ℚ_[p])
    (hb : ∀ i, b i ≠ 0) (h0 : (b 0).valuation = 0) (h1 : (b 1).valuation = 0)
    (h2 : (b 2).valuation = 0) :
    ∃ x : Fin 5 → ℚ_[p], x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0 := by
  have hr : ∀ (c : ℚ_[p]) (hc : c ≠ 0) (hv : c.valuation = 0),
      PadicInt.toZMod (intOf p c hv.ge) ≠ 0 := fun c hc hv =>
    ((intOf_isUnit p c hc hv).map PadicInt.toZMod).ne_zero
  obtain ⟨y1, y2, hy⟩ := odd_ternary_residue p hp
    (PadicInt.toZMod (intOf p _ h0.ge)) _ _ (hr _ (hb 1) h1) (hr _ (hb 2) h2)
  let v : ℤ_[p] := -(intOf p _ h1.ge * (y1.val : ℤ_[p]) ^ 2 +
    intOf p _ h2.ge * (y2.val : ℤ_[p]) ^ 2)
  have hv : PadicInt.toZMod v = PadicInt.toZMod (intOf p _ h0.ge) := by
    simp only [v, map_neg, map_add, map_mul, map_pow, map_natCast, ZMod.natCast_zmod_val]
    linear_combination -hy
  obtain ⟨X, hX⟩ := square_quotient_of_residue_odd p hp _ v (intOf_isUnit p _ (hb 0) h0) hv
  have hb0 : ((intOf p _ h0.ge : ℤ_[p]) : ℚ_[p]) = b 0 := rfl
  rw [hb0] at hX
  apply isotropic_of_first b (hb 0) X ![0, (y1.val : ℚ_[p]), (y2.val : ℚ_[p]), 0, 0]
  · rintro rfl
    rw [mul_zero, div_eq_zero_iff, or_iff_left (hb 0)] at hX
    apply hr _ (hb 0) h0
    rw [← hv, PadicInt.coe_eq_zero.mp hX, map_zero]
  · have hvq : (v : ℚ_[p]) = -(b 1 * (y1.val : ℚ_[p]) ^ 2 + b 2 * (y2.val : ℚ_[p]) ^ 2) := by
      simp only [v, PadicInt.coe_neg, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast]
      rfl
    rw [← hX, hvq]
    simp

theorem dyadic_table : ∀ r0 r1 r2 c3 c4 : ZMod 8, r0.val % 2 = 1 → r1.val % 2 = 1 →
    r2.val % 2 = 1 → c3.val % 4 ≠ 0 → c4.val % 4 ≠ 0 →
    ∃ y1 y2 y3 y4 : Fin 3, r0 + r1 * ((y1 : ℕ) : ZMod 8) ^ 2 + r2 * ((y2 : ℕ) : ZMod 8) ^ 2 +
      c3 * ((y3 : ℕ) : ZMod 8) ^ 2 + c4 * ((y4 : ℕ) : ZMod 8) ^ 2 = 0 := by
  decide +kernel

theorem norm_le_of_residue_dvd (b : ℤ_[2]) (n : ℕ) (hn : n ≤ 3)
    (h : 2 ^ n ∣ (PadicInt.toZModPow 3 b).val) : ‖b‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  have h1 : b - (((PadicInt.toZModPow 3 b).val : ℕ) : ℤ_[2]) ∈
      Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  have h2 : (((PadicInt.toZModPow 3 b).val : ℕ) : ℤ_[2]) ∈
      Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} := by
    rw [Ideal.mem_span_singleton, ← Nat.cast_pow]
    exact Nat.cast_dvd_cast h
  have h3 : Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} ≤ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hn)
  have h4 := Ideal.add_mem _ (h3 h1) h2
  rw [sub_add_cancel] at h4
  exact_mod_cast (PadicInt.norm_le_pow_iff_mem_span_pow b n).mpr h4

theorem residue_not_dvd (b : ℚ_[2]) (hb : b ≠ 0) (hv : 0 ≤ b.valuation) (n : ℕ) (hn : n ≤ 3)
    (hlt : b.valuation < n) : ¬ 2 ^ n ∣ (PadicInt.toZModPow 3 (intOf 2 b hv)).val := by
  intro h
  have h1 := norm_le_of_residue_dvd _ n hn h
  rw [← PadicInt.norm_coe] at h1
  change ‖b‖ ≤ _ at h1
  rw [Padic.norm_eq_zpow_neg_valuation hb] at h1
  have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < (2 : ℕ))).mp (by exact_mod_cast h1)
  omega

theorem dyadic_core (b : Fin 5 → ℚ_[2])
    (hb : ∀ i, b i ≠ 0) (h0 : (b 0).valuation = 0) (h1 : (b 1).valuation = 0)
    (h2 : (b 2).valuation = 0) (h3 : (b 3).valuation = 0 ∨ (b 3).valuation = 1)
    (h4 : (b 4).valuation = 0 ∨ (b 4).valuation = 1) :
    ∃ x : Fin 5 → ℚ_[2], x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0 := by
  have g0 : 0 ≤ (b 0).valuation := h0.ge
  have g1 : 0 ≤ (b 1).valuation := h1.ge
  have g2 : 0 ≤ (b 2).valuation := h2.ge
  have g3 : 0 ≤ (b 3).valuation := by omega
  have g4 : 0 ≤ (b 4).valuation := by omega
  have hodd : ∀ i, (hv : (b i).valuation = 0) →
      (PadicInt.toZModPow 3 (intOf 2 (b i) (hv.ge))).val % 2 = 1 := by
    intro i hv
    have := residue_not_dvd (b i) (hb i) hv.ge 1 (by norm_num) (by omega)
    omega
  have hfour : ∀ i, (hv : 0 ≤ (b i).valuation) → (b i).valuation < 2 →
      (PadicInt.toZModPow 3 (intOf 2 (b i) hv)).val % 4 ≠ 0 := by
    intro i hv hlt
    have := residue_not_dvd (b i) (hb i) hv 2 (by norm_num) (by omega)
    omega
  obtain ⟨y1, y2, y3, y4, hy⟩ := dyadic_table _ _ _ _ _ (hodd 0 h0) (hodd 1 h1) (hodd 2 h2)
    (hfour 3 g3 (by omega)) (hfour 4 g4 (by omega))
  let v : ℤ_[2] := -(intOf 2 _ g1 * ((y1 : ℕ) : ℤ_[2]) ^ 2 +
    intOf 2 _ g2 * ((y2 : ℕ) : ℤ_[2]) ^ 2 + intOf 2 _ g3 * ((y3 : ℕ) : ℤ_[2]) ^ 2 +
    intOf 2 _ g4 * ((y4 : ℕ) : ℤ_[2]) ^ 2)
  have hv : PadicInt.toZModPow 3 v = PadicInt.toZModPow 3 (intOf 2 _ g0) := by
    simp only [v, map_neg, map_add, map_mul, map_pow, map_natCast]
    linear_combination -hy
  have hu0 : IsUnit (intOf 2 _ g0) := intOf_isUnit 2 _ (hb 0) h0
  obtain ⟨X, hX⟩ := square_quotient_of_residue 2 _ v hu0 hv
  change (v : ℚ_[2]) / b 0 = X * X at hX
  apply isotropic_of_first b (hb 0) X
    ![0, ((y1 : ℕ) : ℚ_[2]), ((y2 : ℕ) : ℚ_[2]), ((y3 : ℕ) : ℚ_[2]), ((y4 : ℕ) : ℚ_[2])]
  · rintro rfl
    rw [mul_zero, div_eq_zero_iff, or_iff_left (hb 0)] at hX
    have := hodd 0 h0
    rw [← hv, PadicInt.coe_eq_zero.mp hX, map_zero, ZMod.val_zero] at this
    exact absurd this (by norm_num)
  · have hvq : (v : ℚ_[2]) = -(b 1 * ((y1 : ℕ) : ℚ_[2]) ^ 2 + b 2 * ((y2 : ℕ) : ℚ_[2]) ^ 2 +
        b 3 * ((y3 : ℕ) : ℚ_[2]) ^ 2 + b 4 * ((y4 : ℕ) : ℚ_[2]) ^ 2) := by
      simp only [v, PadicInt.coe_neg, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast]
      rfl
    rw [← hX, hvq]
    simp

theorem local_five_sum (p : ℕ) [Fact p.Prime] (a : Fin 5 → ℚ_[p]) (ha : ∀ i, a i ≠ 0) :
    ∃ x : Fin 5 → ℚ_[p], x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨σ, hσ, he01, he12⟩ :=
    three_same_parity (fun i => decide ((a i).valuation % 2 = 0))
  simp only [decide_eq_decide] at he01 he12
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set t : ℤ := (a (σ 0)).valuation % 2 with ht
  have hlam : (p : ℚ_[p]) ^ (-t) ≠ 0 := zpow_ne_zero _ hp
  have hla : ∀ i, (p : ℚ_[p]) ^ (-t) * a i ≠ 0 := fun i => mul_ne_zero hlam (ha i)
  apply isotropic_of_smul a _ hlam
  choose c hc hcv using fun i => square_normal_form p _ (hla i)
  apply isotropic_of_square_mul _ (fun i => (p : ℚ_[p]) ^ (-t) * a i / c i ^ 2) c hc
    (fun i => by field_simp [hc i])
  apply isotropic_of_comp _ σ hσ
  have hb : ∀ k, (p : ℚ_[p]) ^ (-t) * a (σ k) / c (σ k) ^ 2 ≠ 0 :=
    fun k => div_ne_zero (hla _) (pow_ne_zero _ (hc _))
  have hv : ∀ k, ((p : ℚ_[p]) ^ (-t) * a (σ k) / c (σ k) ^ 2).valuation =
      ((a (σ k)).valuation - t) % 2 := by
    intro k
    rw [hcv, Padic.valuation_mul hlam (ha _), Padic.valuation_zpow, Padic.valuation_p]
    ring_nf
  have v0 := hv 0
  have v1 := hv 1
  have v2 := hv 2
  have v3 := hv 3
  have v4 := hv 4
  by_cases h2 : p = 2
  · subst p
    exact dyadic_core _ hb (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact odd_core p h2 _ hb (by omega) (by omega) (by omega)

/-- Every regular diagonal form in five variables over `ℚ_[p]` is isotropic,
for every prime `p`, including `p = 2`.
Source: Serre, A Course in Arithmetic, Chapter IV, §2.2, Theorem 6. -/
theorem local_five_isotropic (p : ℕ) [Fact p.Prime] (a : Fin 5 → ℚ_[p])
    (ha : ∀ i, a i ≠ 0) :
    ∃ x : Fin 5 → ℚ_[p], x ≠ 0 ∧ QuadraticMap.weightedSumSquares ℚ_[p] a x = 0 := by
  obtain ⟨x, hx, hs⟩ := local_five_sum p a ha
  refine ⟨x, hx, ?_⟩
  simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, sq] using hs

example : ∃ x : Fin 5 → ℚ_[2], x ≠ 0 ∧
    QuadraticMap.weightedSumSquares ℚ_[2] (![1, 1, 1, 1, 1] : Fin 5 → ℚ_[2]) x = 0 := by
  apply local_five_isotropic 2
  intro i
  fin_cases i <;> simp

example : QuadraticMap.weightedSumSquares ℚ_[3] ![1, 1, 1, 1, -1] ![1, 1, 1, 1, 2] = 0 := by
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_five]
  norm_num

example : ¬∃ y1 y2 y3 : Fin 3, (1 : ZMod 8) + ((y1 : ℕ) : ZMod 8) ^ 2 +
    ((y2 : ℕ) : ZMod 8) ^ 2 + ((y3 : ℕ) : ZMod 8) ^ 2 = 0 := by
  decide

end HodgeLean.Foundations.MeyerRational
