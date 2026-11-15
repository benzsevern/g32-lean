import HodgeLean.Foundations.MeyerRationalS6
import HodgeLean.Foundations.MeyerRationalS7

/-! Rational isotropy in dimension five by a binary and ternary split. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

theorem odd_ternary_universal (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b c : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (t : ℚ_[p]) : ∃ x y z : ℚ_[p], a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t := by
  obtain ⟨x, y, hxy⟩ := binary_rep_padic_units p hp a b (-c) ha hb (by simpa using hc)
  have hne : ∀ i : Fin 3, (![a, b, c] : Fin 3 → ℚ_[p]) i ≠ 0 := by
    intro i
    fin_cases i
    · change a ≠ 0
      intro h; simp [h] at ha
    · change b ≠ 0
      intro h; simp [h] at hb
    · change c ≠ 0
      intro h; simp [h] at hc
  obtain ⟨v, hv⟩ := diagonal_universal_of_zero ![a, b, c] hne ![x, y, 1]
    (by intro h; have := congrFun h 2; simp at this)
    (by simp [Fin.sum_univ_succ]; linear_combination hxy) t
  exact ⟨v 0, v 1, v 2, by simpa [Fin.sum_univ_succ, add_assoc] using hv⟩

theorem ternary_rep_of_four {K : Type*} [Field K] [CharZero K]
    (a b c t : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ∃ v : Fin 4 → K, v ≠ 0 ∧
      ∑ i, (![a, b, c, -t] : Fin 4 → K) i * v i ^ 2 = 0) :
    ∃ x y z : K, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t := by
  obtain ⟨v, hv, he⟩ := h
  have he' : a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 - t * v 3 ^ 2 = 0 := by
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using he
  by_cases h3 : v 3 = 0
  · have hne : (![v 0, v 1, v 2] : Fin 3 → K) ≠ 0 := by
      intro h
      apply hv
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      funext i
      fin_cases i <;> simpa using (by assumption)
    obtain ⟨u, hu⟩ := diagonal_universal_of_zero ![a, b, c]
      (by intro i; fin_cases i <;> simpa using (by assumption))
      ![v 0, v 1, v 2] hne (by simpa [Fin.sum_univ_succ, h3, add_assoc] using he') t
    exact ⟨u 0, u 1, u 2, by simpa [Fin.sum_univ_succ, add_assoc] using hu⟩
  · refine ⟨v 0 / v 3, v 1 / v 3, v 2 / v 3, ?_⟩
    field_simp
    linear_combination he'

theorem ternary_rep_local_global (a b c t : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0)
    (hr : ∃ x y z : ℝ, (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p],
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t) :
    ∃ x y z : ℚ, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t := by
  apply ternary_rep_of_four a b c t ha hb hc
  have lift (K : Type) [Field K] [CharZero K]
      (h : ∃ x y z : K, (a : K) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t) :
      ∃ v : Fin 4 → K, v ≠ 0 ∧
        ∑ i, ((![a, b, c, -t] : Fin 4 → ℚ) i : K) * v i ^ 2 = 0 := by
    obtain ⟨x, y, z, he⟩ := h
    refine ⟨![x, y, z, 1], ?_, ?_⟩
    · intro h
      have := congrFun h 3
      simp at this
    · simp [Fin.sum_univ_succ]
      linear_combination he
  exact four_local_global_sum ![a, b, c, -t]
    (by intro i; fin_cases i <;> simpa using (by assumption))
    (lift ℝ hr) (fun p _ => lift ℚ_[p] (hf p))

theorem common_value_five {K : Type*} [Field K] [CharZero K]
    (a : Fin 5 → K) (ha : ∀ i, a i ≠ 0)
    (h : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) :
    ∃ t : K, t ≠ 0 ∧
      (∃ x : Fin 2 → K, ∑ i, (![a 0, a 1] : Fin 2 → K) i * x i ^ 2 = t) ∧
      (∃ y : Fin 3 → K, ∑ i, (![-a 2, -a 3, -a 4] : Fin 3 → K) i * y i ^ 2 = t) := by
  obtain ⟨v, hv, he⟩ := h
  apply diagonal_common_value ![a 0, a 1] ![-a 2, -a 3, -a 4]
    (by intro i; fin_cases i <;> simpa using ha _)
    (by intro i; fin_cases i <;> simpa using ha _) ![v 0, v 1] ![v 2, v 3, v 4]
  · by_contra hn
    push Not at hn
    apply hv
    have h0 := congrFun hn.1 0
    have h1 := congrFun hn.1 1
    have h2 := congrFun hn.2 0
    have h3 := congrFun hn.2 1
    have h4 := congrFun hn.2 2
    funext i
    fin_cases i <;> simpa using (by assumption)
  · simp only [Fin.sum_univ_succ] at he ⊢
    simp at he ⊢
    linear_combination he

theorem five_local_global_sum (a : Fin 5 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hr : ∃ x : Fin 5 → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 5 → ℚ_[p],
      x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 5 → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨S, h2, hS⟩ := rational_unit_places a ha
  have common (K : Type) [Field K] [CharZero K]
      (h : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, (a i : K) * x i ^ 2 = 0) :
      ∃ s : K, s ≠ 0 ∧
        (∃ x : Fin 2 → K, ∑ i, ((![a 0, a 1] : Fin 2 → ℚ) i : K) * x i ^ 2 = s) ∧
        (∃ y : Fin 3 → K, ∑ i, ((![-a 2, -a 3, -a 4] : Fin 3 → ℚ) i : K) * y i ^ 2 = s) := by
    simpa only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, Rat.cast_neg] using
      common_value_five (fun i => (a i : K)) (fun i => Rat.cast_ne_zero.mpr (ha i)) h
  obtain ⟨t, ell, ht, hell, hell2, hrA, hrB, hfAB, hval⟩ :=
    select_common_value ![a 0, a 1] ![-a 2, -a 3, -a 4] S h2
      (common ℝ hr) (fun p => common ℚ_[p.val] (hf p.val))
  have unpackA (K : Type) [Field K] [CharZero K]
      (h : ∃ x : Fin 2 → K, ∑ i, ((![a 0, a 1] : Fin 2 → ℚ) i : K) * x i ^ 2 = t) :
      ∃ x y : K, (a 0 : K) * x ^ 2 + a 1 * y ^ 2 = t := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x 0, x 1, by simpa [Fin.sum_univ_two] using hx⟩
  have unpackB (K : Type) [Field K] [CharZero K]
      (h : ∃ x : Fin 3 → K, ∑ i, ((![-a 2, -a 3, -a 4] : Fin 3 → ℚ) i : K) * x i ^ 2 = t) :
      ∃ x y z : K, ((-a 2 : ℚ) : K) * x ^ 2 + ((-a 3 : ℚ) : K) * y ^ 2 +
        ((-a 4 : ℚ) : K) * z ^ 2 = t := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x 0, x 1, x 2, by simpa [Fin.sum_univ_succ, add_assoc] using hx⟩
  obtain ⟨x, y, hxy⟩ := binary_rep_selected (a 0) (a 1) t (ha 0) (ha 1) ht S ell
    (fun p hp => ⟨(hS p hp).1, (hS p hp).2 0, (hS p hp).2 1⟩)
    (unpackA ℝ hrA) (fun p hp => unpackA ℚ_[p.val] (hfAB p hp).1) hval
  have hB (p : ℕ) [hp : Fact p.Prime] : ∃ x y z : ℚ_[p],
      ((-a 2 : ℚ) : ℚ_[p]) * x ^ 2 + ((-a 3 : ℚ) : ℚ_[p]) * y ^ 2 +
        ((-a 4 : ℚ) : ℚ_[p]) * z ^ 2 = t := by
    let P : Nat.Primes := ⟨p, hp.out⟩
    by_cases hmem : P ∈ S
    · exact unpackB ℚ_[p] (hfAB P hmem).2
    · exact odd_ternary_universal p (hS P hmem).1 _ _ _
        (by simpa using (hS P hmem).2 2)
        (by simpa using (hS P hmem).2 3)
        (by simpa using (hS P hmem).2 4) _
  obtain ⟨z, w, u, hzwu⟩ := ternary_rep_local_global (-a 2) (-a 3) (-a 4) t
    (neg_ne_zero.mpr (ha 2)) (neg_ne_zero.mpr (ha 3)) (neg_ne_zero.mpr (ha 4)) ht
    (unpackB ℝ hrB) hB
  refine ⟨![x, y, z, w, u], ?_, ?_⟩
  · intro h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp at hx hy
    apply ht
    simpa [hx, hy] using hxy.symm
  · simp [Fin.sum_univ_succ]
    linear_combination hxy - hzwu

/-- Local isotropy implies rational isotropy for a regular diagonal in five variables.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, Theorem 8. -/
theorem five_local_global (a : Fin 5 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hr : ∃ x : Fin 5 → ℝ, x ≠ 0 ∧
      QuadraticMap.weightedSumSquares ℝ (fun i => (a i : ℝ)) x = 0)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 5 → ℚ_[p], x ≠ 0 ∧
      QuadraticMap.weightedSumSquares ℚ_[p] (fun i => (a i : ℚ_[p])) x = 0) :
    ∃ x : Fin 5 → ℚ, x ≠ 0 ∧ QuadraticMap.weightedSumSquares ℚ a x = 0 := by
  simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using
    five_local_global_sum a ha
      (by simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using hr)
      (fun p _ => by simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using hf p)

end HodgeLean.Foundations.MeyerRational
