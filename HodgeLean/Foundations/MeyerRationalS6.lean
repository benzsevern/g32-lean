import HodgeLean.Foundations.MeyerRationalS3
import HodgeLean.Foundations.MeyerRationalS4
import HodgeLean.Foundations.MeyerRationalS5

/-! Rational isotropy in dimension four by a common represented value. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

theorem diagonal_universal_of_zero {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (v : Fin n → K) (hv : v ≠ 0) (hz : ∑ i, a i * v i ^ 2 = 0) (t : K) :
    ∃ x : Fin n → K, ∑ i, a i * x i ^ 2 = t := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    simpa only [not_exists, not_not, funext_iff, Pi.zero_apply] using h
  let s := (t - a j) / (2 * a j * v j)
  refine ⟨fun i => (if i = j then 1 else 0) + s * v i, ?_⟩
  have he (i : Fin n) :
      a i * ((if i = j then 1 else 0) + s * v i) ^ 2 =
      s ^ 2 * (a i * v i ^ 2) + if i = j then a j + 2 * s * a j * v j else 0 := by
    split_ifs with h
    · subst i; ring
    · ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [hz, mul_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  dsimp [s]
  field_simp [ha j, hj]
  ring

theorem diagonal_common_value {K : Type*} [Field K] [CharZero K]
    {m n : ℕ} (a : Fin (m + 1) → K) (b : Fin (n + 1) → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (x : Fin (m + 1) → K) (y : Fin (n + 1) → K)
    (hn : x ≠ 0 ∨ y ≠ 0) (he : ∑ i, a i * x i ^ 2 = ∑ i, b i * y i ^ 2) :
    ∃ t : K, t ≠ 0 ∧ (∃ u : Fin (m + 1) → K, ∑ i, a i * u i ^ 2 = t) ∧
      (∃ v : Fin (n + 1) → K, ∑ i, b i * v i ^ 2 = t) := by
  classical
  by_cases ht : ∑ i, a i * x i ^ 2 = 0
  · have ht' : ∑ i, b i * y i ^ 2 = 0 := he.symm.trans ht
    rcases hn with hx | hy
    · refine ⟨b 0, hb 0, diagonal_universal_of_zero a ha x hx ht _, ?_⟩
      exact ⟨Pi.single 0 1, by simp [Pi.single_apply]⟩
    · refine ⟨a 0, ha 0, ?_, diagonal_universal_of_zero b hb y hy ht' _⟩
      exact ⟨Pi.single 0 1, by simp [Pi.single_apply]⟩
  · exact ⟨_, ht, ⟨x, rfl⟩, ⟨y, he.symm⟩⟩

theorem binary_rep_iff_norm {K : Type*} [Field K] (a b t : K) (ha : a ≠ 0) :
    (∃ x y : K, a * x ^ 2 + b * y ^ 2 = t) ↔
      binaryNormSymbol K (-b / a) (t / a) = 1 := by
  rw [binaryNormSymbol_eq_one]
  constructor <;> rintro ⟨x, y, h⟩ <;> refine ⟨x, y, ?_⟩
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h

theorem binary_rep_of_ternary {K : Type*} [Field K] [CharZero K]
    (a b t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      a * x ^ 2 + b * y ^ 2 + -t * z ^ 2 = 0) :
    ∃ x y : K, a * x ^ 2 + b * y ^ 2 = t := by
  apply (binary_rep_iff_norm a b t ha).mpr
  apply (binaryNormSymbol_eq_one_iff_ternary _ _ (div_ne_zero (neg_ne_zero.mpr hb) ha)).mpr
  obtain ⟨x, y, z, hn, he⟩ := h
  refine ⟨x, y, z, hn, ?_⟩
  field_simp
  linear_combination he

theorem binary_rep_square {K : Type*} [Field K] (a b s t : K) (hs : s ≠ 0)
    (h : ∃ x y : K, a * x ^ 2 + b * y ^ 2 = s) (hst : IsSquare (t / s)) :
    ∃ x y : K, a * x ^ 2 + b * y ^ 2 = t := by
  obtain ⟨x, y, he⟩ := h
  obtain ⟨r, hr⟩ := hst
  have ht : t = r ^ 2 * s := by rw [← div_eq_iff hs, hr, pow_two]
  refine ⟨r * x, r * y, ?_⟩
  rw [ht, ← he]
  ring

theorem real_square_of_same_sign (s t : ℝ) (_hs : s ≠ 0)
    (sign : ℝ) (hsg : sign = 1 ∨ sign = -1)
    (hsign : 0 < sign * s) (ht : 0 < sign * t) : IsSquare (t / s) := by
  have h : 0 ≤ t / s := by
    rcases hsg with rfl | rfl
    · simp only [one_mul] at hsign ht
      exact (div_pos ht hsign).le
    · simp only [neg_one_mul, neg_pos] at hsign ht
      exact (div_pos_of_neg_of_neg ht hsign).le
  exact ⟨Real.sqrt (t / s), by rw [← pow_two, Real.sq_sqrt h]⟩

theorem rational_unit_places {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    ∃ S : Finset Nat.Primes, (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ S ∧
      ∀ p : Nat.Primes, p ∉ S → p.val ≠ 2 ∧ ∀ i, ‖(a i : ℚ_[p.val])‖ = 1 := by
  classical
  let B := (∑ i, ((a i).num.natAbs + (a i).den)) + 3
  refine ⟨(Finset.range B).subtype Nat.Prime, ?_, ?_⟩
  · change (⟨2, Nat.prime_two⟩ : {p : ℕ // p.Prime}) ∈ (Finset.range B).subtype Nat.Prime
    rw [Finset.mem_subtype, Finset.mem_range]
    dsimp [B]
    omega
  · intro p hp
    change (p : {p : ℕ // p.Prime}) ∉ (Finset.range B).subtype Nat.Prime at hp
    have hB : B ≤ p.val := Nat.le_of_not_lt (fun h => hp (Finset.mem_subtype.mpr (Finset.mem_range.mpr h)))
    refine ⟨by dsimp [B] at hB; omega, fun i => ?_⟩
    have hi : (a i).num.natAbs + (a i).den ≤ ∑ j, ((a j).num.natAbs + (a j).den) :=
      Finset.single_le_sum (f := fun j => (a j).num.natAbs + (a j).den) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    apply rational_padic_unit_of_large p.val (a i) (ha i) <;> dsimp [B] at hB <;> omega

theorem binary_rep_padic_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b t : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ht : ‖t‖ = 1) :
    ∃ x y : ℚ_[p], a * x ^ 2 + b * y ^ 2 = t := by
  apply (binary_rep_iff_norm a b t (by intro h; simp [h] at ha)).mpr
  exact binaryNormSymbol_padic_units p hp _ _
    (by rw [norm_div, norm_neg, ha, hb, div_self one_ne_zero])
    (by rw [norm_div, ht, ha, div_self one_ne_zero])

theorem binary_rep_missing_prime (a b t : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (ell : Nat.Primes) (hr : ∃ x y : ℝ, (a : ℝ) * x ^ 2 + b * y ^ 2 = t)
    (hf : ∀ p : Nat.Primes, p ≠ ell →
      ∃ x y : ℚ_[p.val], (a : ℚ_[p.val]) * x ^ 2 + b * y ^ 2 = t) :
    ∃ x y : ℚ_[ell.val], (a : ℚ_[ell.val]) * x ^ 2 + b * y ^ 2 = t := by
  have trans (K : Type) [Field K] [CharZero K]
      (h : ∃ x y : K, (a : K) * x ^ 2 + b * y ^ 2 = t) :
      ∃ x y z : K, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        x ^ 2 - ((-b / a : ℚ) : K) * y ^ 2 = ((t / a : ℚ) : K) * z ^ 2 := by
    apply (binaryNormSymbol_eq_one_iff_ternary _ _
      (Rat.cast_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hb) ha))).mp
    push_cast
    exact (binary_rep_iff_norm (a : K) b t (Rat.cast_ne_zero.mpr ha)).mp h
  have h := ternary_missing_prime (-b / a) (t / a)
    (div_ne_zero (neg_ne_zero.mpr hb) ha) (div_ne_zero ht ha) ell
    (trans ℝ hr) (fun p hp => trans ℚ_[p.val] (hf p hp))
  apply (binary_rep_iff_norm (a : ℚ_[ell.val]) b t (Rat.cast_ne_zero.mpr ha)).mpr
  have h' := (binaryNormSymbol_eq_one_iff_ternary _ _
    (Rat.cast_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hb) ha))).mpr h
  simpa only [Rat.cast_div, Rat.cast_neg] using h'

theorem binary_rep_local_global (a b t : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hr : ∃ x y : ℝ, (a : ℝ) * x ^ 2 + b * y ^ 2 = t)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x y : ℚ_[p],
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 = t) :
    ∃ x y : ℚ, a * x ^ 2 + b * y ^ 2 = t := by
  apply binary_rep_of_ternary a b t ha hb
  apply (ternary_local_global a b (-t) ha hb (neg_ne_zero.mpr ht)).mpr
  constructor
  · obtain ⟨x, y, h⟩ := hr
    refine ⟨x, y, 1, by simp, ?_⟩
    push_cast
    linear_combination h
  · intro p _
    obtain ⟨x, y, h⟩ := hf p
    refine ⟨x, y, 1, by simp, ?_⟩
    push_cast
    linear_combination h

theorem diagonal_rep_square {K : Type*} [Field K] {n : ℕ} (a : Fin n → K)
    (s t : K) (hs : s ≠ 0) (h : ∃ x : Fin n → K, ∑ i, a i * x i ^ 2 = s)
    (hst : IsSquare (t / s)) : ∃ x : Fin n → K, ∑ i, a i * x i ^ 2 = t := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨r, hr⟩ := hst
  have ht : t = r ^ 2 * s := by rw [← div_eq_iff hs, hr, pow_two]
  refine ⟨fun i => r * x i, ?_⟩
  calc
    _ = r ^ 2 * ∑ i, a i * x i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = t := by rw [hx, ht]

theorem select_common_value {m n : ℕ} (a : Fin m → ℚ) (b : Fin n → ℚ)
    (S : Finset Nat.Primes) (h2 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ S)
    (hr : ∃ s : ℝ, s ≠ 0 ∧
      (∃ x : Fin m → ℝ, ∑ i, (a i : ℝ) * x i ^ 2 = s) ∧
      (∃ y : Fin n → ℝ, ∑ i, (b i : ℝ) * y i ^ 2 = s))
    (hf : ∀ p : Nat.Primes, ∃ s : ℚ_[p.val], s ≠ 0 ∧
      (∃ x : Fin m → ℚ_[p.val], ∑ i, (a i : ℚ_[p.val]) * x i ^ 2 = s) ∧
      (∃ y : Fin n → ℚ_[p.val], ∑ i, (b i : ℚ_[p.val]) * y i ^ 2 = s)) :
    ∃ (t : ℚ) (ell : Nat.Primes), t ≠ 0 ∧ ell ∉ S ∧ ell.val ≠ 2 ∧
      (∃ x : Fin m → ℝ, ∑ i, (a i : ℝ) * x i ^ 2 = t) ∧
      (∃ y : Fin n → ℝ, ∑ i, (b i : ℝ) * y i ^ 2 = t) ∧
      (∀ p ∈ S, (∃ x : Fin m → ℚ_[p.val], ∑ i, (a i : ℚ_[p.val]) * x i ^ 2 = t) ∧
        (∃ y : Fin n → ℚ_[p.val], ∑ i, (b i : ℚ_[p.val]) * y i ^ 2 = t)) ∧
      (∀ p : Nat.Primes, p ∉ S → p ≠ ell → padicValRat p.val t = 0) := by
  classical
  obtain ⟨s, hs, hsa, hsb⟩ := hr
  choose target ht hta htb using hf
  let sign : ℝ := if 0 < s then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by simp only [sign]; split_ifs <;> simp
  have hss : 0 < sign * s := by
    dsimp [sign]
    split_ifs with h
    · simpa using h
    · simp only [neg_one_mul, neg_pos]
      exact lt_of_le_of_ne (le_of_not_gt h) hs
  obtain ⟨t, ell, ht0, hst, hell, hell2, hsq, hval⟩ :=
    prime_squareClass_selector S h2 target (fun p _ => ht p) sign hsign
  have hsqR := real_square_of_same_sign s (t : ℝ) hs sign hsign hss hst
  refine ⟨t, ell, ht0, hell, hell2,
    diagonal_rep_square _ s _ hs hsa hsqR,
    diagonal_rep_square _ s _ hs hsb hsqR, ?_, hval⟩
  intro p hp
  exact ⟨diagonal_rep_square _ _ _ (ht p) (hta p) (hsq p hp),
    diagonal_rep_square _ _ _ (ht p) (htb p) (hsq p hp)⟩

theorem common_value_four {K : Type*} [Field K] [CharZero K]
    (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0)
    (h : ∃ x : Fin 4 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) :
    ∃ t : K, t ≠ 0 ∧
      (∃ x : Fin 2 → K, ∑ i, (![a 0, a 1] : Fin 2 → K) i * x i ^ 2 = t) ∧
      (∃ y : Fin 2 → K, ∑ i, (![-a 2, -a 3] : Fin 2 → K) i * y i ^ 2 = t) := by
  obtain ⟨v, hv, he⟩ := h
  apply diagonal_common_value ![a 0, a 1] ![-a 2, -a 3]
    (by intro i; fin_cases i <;> simpa using ha _)
    (by intro i; fin_cases i <;> simpa using ha _) ![v 0, v 1] ![v 2, v 3]
  · by_contra hn
    push Not at hn
    apply hv
    have h0 := congrFun hn.1 0
    have h1 := congrFun hn.1 1
    have h2 := congrFun hn.2 0
    have h3 := congrFun hn.2 1
    funext i
    fin_cases i <;> simpa using (by assumption)
  · simp only [Fin.sum_univ_succ] at he ⊢
    simp at he ⊢
    linear_combination he

theorem binary_rep_selected (a b t : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (S : Finset Nat.Primes) (ell : Nat.Primes)
    (hunit : ∀ p : Nat.Primes, p ∉ S → p.val ≠ 2 ∧
      ‖(a : ℚ_[p.val])‖ = 1 ∧ ‖(b : ℚ_[p.val])‖ = 1)
    (hr : ∃ x y : ℝ, (a : ℝ) * x ^ 2 + b * y ^ 2 = t)
    (hf : ∀ p ∈ S, ∃ x y : ℚ_[p.val], (a : ℚ_[p.val]) * x ^ 2 + b * y ^ 2 = t)
    (hval : ∀ p : Nat.Primes, p ∉ S → p ≠ ell → padicValRat p.val t = 0) :
    ∃ x y : ℚ, a * x ^ 2 + b * y ^ 2 = t := by
  have hf' (p : Nat.Primes) (hp : p ≠ ell) :
      ∃ x y : ℚ_[p.val], (a : ℚ_[p.val]) * x ^ 2 + b * y ^ 2 = t := by
    by_cases hS : p ∈ S
    · exact hf p hS
    · have hu := hunit p hS
      apply binary_rep_padic_units p.val hu.1 _ _ _ hu.2.1 hu.2.2
      rw [Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr ht),
        Padic.valuation_ratCast, hval p hS hp]
      simp
  have hell := binary_rep_missing_prime a b t ha hb ht ell hr hf'
  apply binary_rep_local_global a b t ha hb ht hr
  intro p hp
  let P : Nat.Primes := ⟨p, hp.out⟩
  by_cases h : P = ell
  · subst ell
    exact hell
  · exact hf' P h

theorem four_local_global_sum (a : Fin 4 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hr : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, (a i : ℝ) * x i ^ 2 = 0)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 4 → ℚ_[p],
      x ≠ 0 ∧ ∑ i, (a i : ℚ_[p]) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  obtain ⟨S, h2, hS⟩ := rational_unit_places a ha
  have common (K : Type) [Field K] [CharZero K]
      (h : ∃ x : Fin 4 → K, x ≠ 0 ∧ ∑ i, (a i : K) * x i ^ 2 = 0) :
      ∃ s : K, s ≠ 0 ∧
        (∃ x : Fin 2 → K, ∑ i, ((![a 0, a 1] : Fin 2 → ℚ) i : K) * x i ^ 2 = s) ∧
        (∃ y : Fin 2 → K, ∑ i, ((![-a 2, -a 3] : Fin 2 → ℚ) i : K) * y i ^ 2 = s) := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Rat.cast_neg] using
      common_value_four (fun i => (a i : K)) (fun i => Rat.cast_ne_zero.mpr (ha i)) h
  obtain ⟨t, ell, ht, hell, hell2, hrA, hrB, hfAB, hval⟩ :=
    select_common_value ![a 0, a 1] ![-a 2, -a 3] S h2
      (common ℝ hr) (fun p => common ℚ_[p.val] (hf p.val))
  have unpack (K : Type) [Field K] [CharZero K] (c d : ℚ)
      (h : ∃ x : Fin 2 → K, ∑ i, ((![c, d] : Fin 2 → ℚ) i : K) * x i ^ 2 = t) :
      ∃ x y : K, (c : K) * x ^ 2 + d * y ^ 2 = t := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x 0, x 1, by simpa [Fin.sum_univ_two] using hx⟩
  obtain ⟨x, y, hxy⟩ := binary_rep_selected (a 0) (a 1) t (ha 0) (ha 1) ht S ell
    (fun p hp => ⟨(hS p hp).1, (hS p hp).2 0, (hS p hp).2 1⟩)
    (unpack ℝ _ _ hrA) (fun p hp => unpack ℚ_[p.val] _ _ (hfAB p hp).1) hval
  obtain ⟨z, w, hzw⟩ := binary_rep_selected (-a 2) (-a 3) t
    (neg_ne_zero.mpr (ha 2)) (neg_ne_zero.mpr (ha 3)) ht S ell
    (fun p hp => ⟨(hS p hp).1, by simpa using (hS p hp).2 2,
      by simpa using (hS p hp).2 3⟩)
    (unpack ℝ _ _ hrB) (fun p hp => unpack ℚ_[p.val] _ _ (hfAB p hp).2) hval
  refine ⟨![x, y, z, w], ?_, ?_⟩
  · intro h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp at hx hy
    apply ht
    simpa [hx, hy] using hxy.symm
  · simp [Fin.sum_univ_succ]
    linear_combination hxy - hzw

/-- Local isotropy implies rational isotropy for a regular diagonal in four variables.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, Theorem 8. -/
theorem four_local_global (a : Fin 4 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hr : ∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      QuadraticMap.weightedSumSquares ℝ (fun i => (a i : ℝ)) x = 0)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin 4 → ℚ_[p], x ≠ 0 ∧
      QuadraticMap.weightedSumSquares ℚ_[p] (fun i => (a i : ℚ_[p])) x = 0) :
    ∃ x : Fin 4 → ℚ, x ≠ 0 ∧ QuadraticMap.weightedSumSquares ℚ a x = 0 := by
  simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using
    four_local_global_sum a ha
      (by simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using hr)
      (fun p _ => by simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using hf p)

end HodgeLean.Foundations.MeyerRational
