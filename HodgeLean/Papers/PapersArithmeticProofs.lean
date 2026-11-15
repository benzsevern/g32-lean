import HodgeLean.Papers.PapersArithmeticDefs

set_option maxHeartbeats 400000

/-! # Proof obligations for the compact paper results, batch 1

The `_aux` theorems that `PapersArithmetic.lean` (frozen) restates. See
`docs/specs/PapersArithmetic.md`.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Papers

open Polynomial Matrix ComplexConjugate

/-! ## Item 3: G32 Proposition 6.3, the printed matrix over ℚ(ω) -/

theorem omega_im_ne_zero (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ω.im ≠ 0 := by
  intro h
  have hre := congrArg Complex.re hω
  simp [pow_two, h] at hre
  nlinarith [sq_nonneg (ω.re + 1/2)]

theorem conj_omega (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : conj ω = -1 - ω := by
  have hc : conj ω ^ 2 + conj ω + 1 = 0 := by
    have := congrArg conj hω; simpa using this
  have hne : conj ω ≠ ω := by
    intro h; exact omega_im_ne_zero ω hω (by simpa using Complex.conj_eq_iff_im.mp h)
  have : (conj ω - ω) * (conj ω + ω + 1) = 0 := by linear_combination hc - hω
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

theorem omega_ne_rat (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (q : ℚ) : ω ≠ q := by
  intro h; exact omega_im_ne_zero ω hω (by simp [h])

theorem papers_g32_h0_isHermitian_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).IsHermitian := by
  have hc := conj_omega ω hω
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32H0, Matrix.conjTranspose_apply, hc] <;> ring_nf

theorem papers_g32_charpoly_factor_aux :
    g32Charpoly = (X ^ 2 - C (2/9)) * (X ^ 4 - C (4/3) * X ^ 3 - C (8/3) * X ^ 2 + C (11/9) * X
      + C (1/9)) := by
  apply Polynomial.funext
  intro x
  simp [g32Charpoly]
  ring

theorem papers_g32_h0_charpoly_aux
    {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).charpoly = g32Charpoly.map (algebraMap ℚ K) := by
  have : Infinite K := CharZero.infinite K
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, Polynomial.eval_map, ← Polynomial.aeval_def]
  simp only [g32Charpoly, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    eq_ratCast, Rat.cast_div, Rat.cast_ofNat]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, g32H0, Fin.succAbove]
  linear_combination (ω^4/81 + 2*ω^3/81 + 4*ω^2*x^2/9 - 4*ω^2*x/81 - ω^2/27 + 4*ω*x^2/9 -
    4*ω*x/81 - 4*ω/81 + 28*x^4/9 - 16*x^3/27 - 26*x^2/27 + 5*x/27 + 4/81) * hω

theorem papers_g32_h0_det_aux {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω).det = -2/81 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, g32H0, Fin.succAbove]
  linear_combination (ω^4/81 + 2*ω^3/81 - ω^2/27 - 4*ω/81 + 4/81) * hω

theorem exists_isRoot_Ioo (p : ℝ[X]) {a b : ℝ} (hab : a ≤ b) (h : p.eval a * p.eval b < 0) :
    ∃ x ∈ Set.Ioo a b, p.IsRoot x := by
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 from fun h0 => by simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by nlinarith
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab p.continuousOn ⟨ha, hb⟩
    exact ⟨x, hx, hx0⟩
  · have hb : p.eval b < 0 := by nlinarith
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hab p.continuousOn ⟨hb, ha⟩
    exact ⟨x, hx, hx0⟩

theorem roots_counts_of_six (p : ℝ[X]) (hp : p ≠ 0) (hdeg : p.natDegree ≤ 6)
    {x₁ x₂ x₃ x₄ x₅ x₆ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) (h₃ : x₃ < 0) (h₄ : 0 < x₄)
    (h₄₅ : x₄ < x₅) (h₅₆ : x₅ < x₆) (r₁ : p.IsRoot x₁) (r₂ : p.IsRoot x₂) (r₃ : p.IsRoot x₃)
    (r₄ : p.IsRoot x₄) (r₅ : p.IsRoot x₅) (r₆ : p.IsRoot x₆) :
    p.roots.card = 6 ∧ (p.roots.filter (0 < ·)).card = 3 ∧ (p.roots.filter (· < 0)).card = 3 := by
  set s : Multiset ℝ := {x₁, x₂, x₃, x₄, x₅, x₆} with hs
  have hnd : s.Nodup := by
    simp only [hs, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      intro h <;> linarith
  have hle : s ≤ p.roots := by
    refine (Multiset.le_iff_subset hnd).2 fun x hx => ?_
    simp only [hs, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rw [mem_roots hp]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard : Multiset.card p.roots ≤ Multiset.card s := by
    simpa [hs] using (p.card_roots').trans hdeg
  rw [← Multiset.eq_of_le_of_card_le hle hcard]
  simp only [hs, Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  simp [show x₁ < 0 by linarith, show x₂ < 0 by linarith, h₃, h₄, show 0 < x₅ by linarith,
    show 0 < x₆ by linarith, not_lt.mpr (show x₁ ≤ 0 by linarith),
    not_lt.mpr (show x₂ ≤ 0 by linarith), not_lt.mpr h₃.le, not_lt.mpr h₄.le,
    not_lt.mpr (show 0 ≤ x₅ by linarith), not_lt.mpr (show 0 ≤ x₆ by linarith)]

theorem g32_eval (x : ℝ) : (g32Charpoly.map (algebraMap ℚ ℝ)).eval x =
    x ^ 6 - 4/3 * x ^ 5 - 26/9 * x ^ 4 + 41/27 * x ^ 3 + 19/27 * x ^ 2 - 22/81 * x - 2/81 := by
  simp [g32Charpoly]

theorem papers_g32_charpoly_realRoots_aux :
    (realRoots g32Charpoly).card = 6 ∧ posRealRootCount g32Charpoly = 3 ∧
      negRealRootCount g32Charpoly = 3 := by
  set p := g32Charpoly.map (algebraMap ℚ ℝ) with hp
  have hne : p ≠ 0 := fun h => by
    have := g32_eval 0
    rw [← hp, h] at this
    norm_num at this
  have hdeg : p.natDegree ≤ 6 :=
    natDegree_map_le.trans (by unfold g32Charpoly; compute_degree!)
  obtain ⟨x₁, hx₁, r₁⟩ := exists_isRoot_Ioo p (a := -2) (b := -1) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  obtain ⟨x₂, hx₂, r₂⟩ := exists_isRoot_Ioo p (a := -1) (b := -1/4) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  obtain ⟨x₃, hx₃, r₃⟩ := exists_isRoot_Ioo p (a := -1/4) (b := 0) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  obtain ⟨x₄, hx₄, r₄⟩ := exists_isRoot_Ioo p (a := 2/5) (b := 59/125) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  obtain ⟨x₅, hx₅, r₅⟩ := exists_isRoot_Ioo p (a := 59/125) (b := 1/2) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  obtain ⟨x₆, hx₆, r₆⟩ := exists_isRoot_Ioo p (a := 1/2) (b := 3) (by norm_num)
    (by rw [g32_eval, g32_eval]; norm_num)
  simp only [Set.mem_Ioo] at hx₁ hx₂ hx₃ hx₄ hx₅ hx₆
  exact roots_counts_of_six p hne hdeg (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) r₁ r₂ r₃ r₄ r₅ r₆

theorem eigenvalue_counts (A : Matrix (Fin 6) (Fin 6) ℂ) (hA : A.IsHermitian) (p : ℚ[X])
    (hchar : A.charpoly = p.map (algebraMap ℚ ℂ)) (hcard : (realRoots p).card = 6) :
    (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card = posRealRootCount p ∧
      (Finset.univ.filter fun i => hA.eigenvalues i < 0).card = negRealRootCount p := by
  set pR := p.map (algebraMap ℚ ℝ) with hpR
  have hmap : p.map (algebraMap ℚ ℂ) = pR.map (algebraMap ℝ ℂ) := by
    rw [hpR, Polynomial.map_map]; congr 1
  have hdegR : pR.natDegree = 6 := by
    have h1 : A.charpoly.natDegree = 6 := by simp [Matrix.charpoly_natDegree_eq_dim]
    rw [hchar, hmap, natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective] at h1
    exact h1
  have hroots : pR.roots.map (algebraMap ℝ ℂ) = A.charpoly.roots := by
    rw [hchar, hmap]
    exact roots_map_of_injective_of_card_eq_natDegree (algebraMap ℝ ℂ).injective
      (by rw [hdegR]; exact hcard)
  rw [hA.roots_charpoly_eq_eigenvalues] at hroots
  have heig : (Finset.univ.val.map hA.eigenvalues) = realRoots p := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Multiset.map_map]
    exact hroots.symm
  constructor
  · rw [posRealRootCount, ← heig, Multiset.filter_map, Multiset.card_map]; rfl
  · rw [negRealRootCount, ← heig, Multiset.filter_map, Multiset.card_map]; rfl

theorem papers_g32_h0_signature_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (Finset.univ.filter fun i =>
        0 < (papers_g32_h0_isHermitian_aux ω hω).eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i =>
        (papers_g32_h0_isHermitian_aux ω hω).eigenvalues i < 0).card = 3 := by
  have := eigenvalue_counts _ (papers_g32_h0_isHermitian_aux ω hω) g32Charpoly
    (papers_g32_h0_charpoly_aux ω hω) papers_g32_charpoly_realRoots_aux.1
  rw [this.1, this.2, papers_g32_charpoly_realRoots_aux.2.1, papers_g32_charpoly_realRoots_aux.2.2]
  exact ⟨rfl, rfl⟩

theorem papers_g32_det_norm_aux :
    (-2/81 : ℚ) = -2 * normOmega (1/9) 0 ∧ SameNormClass 3 (-2/81) (-2) :=
  ⟨by norm_num [normOmega], 1/9, 0, by norm_num, by norm_num⟩

theorem papers_g32_h0_det_perturbed_aux
    {K : Type*} [Field K] [CharZero K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    (g32H0 ω + Matrix.single 2 2 (1/3)).det = -1/27 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, g32H0, Fin.succAbove, Matrix.single_apply]
  linear_combination (ω^4/81 + 2*ω^3/81 - 4*ω^2/81 - 5*ω/81 + 7/81) * hω

/-! ## Item 4: QI Proposition 8.2 and TT Section 11, the printed matrix over ℚ(i) -/

theorem papers_qi_h0_isHermitian_aux :
    (qiH0 Complex.I).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qiH0, Matrix.conjTranspose_apply] <;> ring_nf

theorem papers_qi_h0_det_aux {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι).det = -3 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, qiH0, Fin.succAbove]
  linear_combination (ι^4/4 - 11*ι^2/4) * hι

/-- The characteristic polynomial of QI's `h_0`, computed here (QI does not print it). -/
noncomputable def qiCharpoly : ℚ[X] :=
  X ^ 6 + X ^ 5 - C (79/2) * X ^ 4 - C 49 * X ^ 3 + C (243/2) * X ^ 2 - C 22 * X - C 3

theorem qi_h0_charpoly {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι).charpoly = qiCharpoly.map (algebraMap ℚ K) := by
  have : Infinite K := CharZero.infinite K
  apply Polynomial.funext
  intro x
  rw [Matrix.eval_charpoly, Polynomial.eval_map, ← Polynomial.aeval_def]
  simp only [qiCharpoly, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    eq_ratCast, Rat.cast_div, Rat.cast_ofNat]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, qiH0, Fin.succAbove]
  linear_combination (ι^4/4 + 95*ι^2*x^2/4 - 31*ι^2*x/2 - 11*ι^2/4 + 81*x^4/4 + 59*x^3 -
    98*x^2 + 19*x/2) * hι

theorem qi_eval (x : ℝ) : (qiCharpoly.map (algebraMap ℚ ℝ)).eval x =
    x ^ 6 + x ^ 5 - 79/2 * x ^ 4 - 49 * x ^ 3 + 243/2 * x ^ 2 - 22 * x - 3 := by
  simp [qiCharpoly]

theorem qi_charpoly_realRoots : (realRoots qiCharpoly).card = 6 ∧
    posRealRootCount qiCharpoly = 3 ∧ negRealRootCount qiCharpoly = 3 := by
  set p := qiCharpoly.map (algebraMap ℚ ℝ) with hp
  have hne : p ≠ 0 := fun h => by
    have := qi_eval 0
    rw [← hp, h] at this
    norm_num at this
  have hdeg : p.natDegree ≤ 6 :=
    natDegree_map_le.trans (by unfold qiCharpoly; compute_degree!)
  obtain ⟨x₁, hx₁, r₁⟩ := exists_isRoot_Ioo p (a := -6) (b := -4) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  obtain ⟨x₂, hx₂, r₂⟩ := exists_isRoot_Ioo p (a := -4) (b := -1) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  obtain ⟨x₃, hx₃, r₃⟩ := exists_isRoot_Ioo p (a := -1) (b := 0) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  obtain ⟨x₄, hx₄, r₄⟩ := exists_isRoot_Ioo p (a := 0) (b := 1/2) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  obtain ⟨x₅, hx₅, r₅⟩ := exists_isRoot_Ioo p (a := 1/2) (b := 2) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  obtain ⟨x₆, hx₆, r₆⟩ := exists_isRoot_Ioo p (a := 2) (b := 7) (by norm_num)
    (by rw [qi_eval, qi_eval]; norm_num)
  simp only [Set.mem_Ioo] at hx₁ hx₂ hx₃ hx₄ hx₅ hx₆
  exact roots_counts_of_six p hne hdeg (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) r₁ r₂ r₃ r₄ r₅ r₆

theorem papers_qi_h0_signature_aux :
    (Finset.univ.filter fun i => 0 < papers_qi_h0_isHermitian_aux.eigenvalues i).card = 3 ∧
      (Finset.univ.filter fun i => papers_qi_h0_isHermitian_aux.eigenvalues i < 0).card = 3 := by
  have := eigenvalue_counts _ papers_qi_h0_isHermitian_aux qiCharpoly
    (qi_h0_charpoly Complex.I Complex.I_sq) qi_charpoly_realRoots.1
  rw [this.1, this.2, qi_charpoly_realRoots.2.1, qi_charpoly_realRoots.2.2]
  exact ⟨rfl, rfl⟩

theorem even_padicValNat_three_sq_add_sq (x y : ℕ) : Even (padicValNat 3 (x ^ 2 + y ^ 2)) := by
  by_cases h3 : 3 ∣ x ^ 2 + y ^ 2
  · by_cases h0 : x ^ 2 + y ^ 2 = 0
    · simp [h0]
    exact Nat.eq_sq_add_sq_iff.mp ⟨x, y, rfl⟩ 3
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h0⟩) (by norm_num)
  · simp [padicValNat.eq_zero_of_not_dvd h3]

theorem papers_normGaussian_padicValRat_even_aux (a b : ℚ) (h : normGaussian a b ≠ 0) :
    Even (padicValRat 3 (normGaussian a b)) := by
  set X : ℤ := a.num * b.den
  set Y : ℤ := b.num * a.den
  set n : ℕ := a.den * b.den
  have hn : (n : ℚ) ≠ 0 := by positivity
  have hkey : normGaussian a b = ((X.natAbs ^ 2 + Y.natAbs ^ 2 : ℕ) : ℚ) / ((n ^ 2 : ℕ) : ℚ) := by
    have ha : a = (a.num : ℚ) / a.den := (Rat.num_div_den a).symm
    have hb : b = (b.num : ℚ) / b.den := (Rat.num_div_den b).symm
    push_cast
    simp only [Nat.cast_natAbs, Int.cast_abs, X, Y, n, normGaussian]
    rw [ha, hb]
    push_cast
    field_simp
    simp only [mul_pow, sq_abs, Rat.num_div_den]
    ring
  rw [hkey] at h ⊢
  have hN : ((X.natAbs ^ 2 + Y.natAbs ^ 2 : ℕ) : ℚ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at h; exact h rfl
  rw [padicValRat.div hN (by positivity), padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.pow n 2]
  obtain ⟨k, hk⟩ := even_padicValNat_three_sq_add_sq X.natAbs Y.natAbs
  exact ⟨k - padicValNat 3 n, by push_cast [hk]; ring⟩

/-- A rational of 3-adic valuation `1` is not `−1` times a norm from `ℚ(i)`. -/
theorem not_sameNormClass_neg_one_of_padicValRat_one (d : ℚ) (hd : padicValRat 3 d = 1) :
    ¬ SameNormClass 1 d (-1) := by
  rintro ⟨x, y, hN, h⟩
  have h3 : normGaussian x y = -d := by simp only [normGaussian]; linarith
  have := papers_normGaussian_padicValRat_even_aux x y (by simpa [normGaussian] using hN)
  rw [h3, padicValRat.neg, hd] at this
  exact Int.not_even_one this

theorem papers_qi_disc_not_split_aux :
    ¬ SameNormClass 1 (-3) (-1) := by
  have h3 : padicValRat 3 3 = 1 := padicValRat.self (by norm_num)
  exact not_sameNormClass_neg_one_of_padicValRat_one (-3) (by rw [padicValRat.neg, h3])

theorem papers_tt_dets_norm_aux :
    (-24 : ℚ) / (-3) = normGaussian 2 2 ∧ (-6/25 : ℚ) / (-3) = normGaussian (1/5) (1/5) ∧
      (-3/2 : ℚ) / (-3) = normGaussian (1/2) (1/2) ∧ (-6 : ℚ) / (-3) = normGaussian 1 1 := by
  norm_num [normGaussian]

theorem papers_tt_dets_padicValRat_aux :
    padicValRat 3 (-24) = 1 ∧ padicValRat 3 (-6/25) = 1 ∧ padicValRat 3 (-3/2) = 1 ∧
      padicValRat 3 (-6) = 1 := by
  have v6 : padicValRat 3 6 = 1 := by
    rw [show (6 : ℚ) = ((3 * 2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]; rfl
  have v24 : padicValRat 3 24 = 1 := by
    rw [show (24 : ℚ) = ((3 * 8 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 8)]; rfl
  have v25 : padicValRat 3 25 = 0 := by
    rw [show (25 : ℚ) = ((25 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 25)]; rfl
  have v2 : padicValRat 3 2 = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]; rfl
  have v3 : padicValRat 3 3 = 1 := padicValRat.self (by norm_num)
  refine ⟨by rw [padicValRat.neg, v24], ?_, ?_, by rw [padicValRat.neg, v6]⟩
  · rw [neg_div, padicValRat.neg, padicValRat.div (by norm_num) (by norm_num), v6, v25]; rfl
  · rw [neg_div, padicValRat.neg, padicValRat.div (by norm_num) (by norm_num), v3, v2]; rfl

theorem papers_tt_dets_not_split_aux :
    ∀ d ∈ ([-24, -6/25, -3/2, -6] : List ℚ), ¬ SameNormClass 1 d (-1) := by
  obtain ⟨h1, h2, h3, h4⟩ := papers_tt_dets_padicValRat_aux
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    exact not_sameNormClass_neg_one_of_padicValRat_one _ ‹_›

theorem papers_qi_h0_det_perturbed_aux
    {K : Type*} [Field K] [CharZero K] (ι : K) (hι : ι ^ 2 = -1) :
    (qiH0 ι + Matrix.single 0 0 1).det = -2 ∧ SameNormClass 1 (-2) (-1) := by
  refine ⟨?_, 1, 1, by norm_num, by norm_num⟩
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, qiH0, Fin.succAbove, Matrix.single_apply]
  linear_combination (ι^4/4 - ι^2/4 - 1) * hι

/-! ## Item 7: multiplicities and Hodge numbers from the local monodromy -/

theorem papers_defect_identity_aux (d : ℤ) (cs : List ℤ) :
    ((cs.length : ℤ) - 2) * d - (cs.map fun c => d - c).sum = -2 * d + cs.sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; push_cast; linarith

theorem papers_g32_multiplicity_aux :
    defectMultiplicity 4 g32Angles = -8 + 12 + 2 ∧ defectMultiplicity 4 g32Angles = 6 := by
  norm_num [defectMultiplicity, g32Angles, rankDefect]

theorem papers_g32_hodge_aux :
    holomorphicMultiplicity 4 g32Angles = 6 * (2/3) + 6 * (1/3) + 1 - 4 ∧
      holomorphicMultiplicity 4 g32Angles = 3 ∧
      (defectMultiplicity 4 g32Angles : ℚ) - holomorphicMultiplicity 4 g32Angles = 3 := by
  norm_num [holomorphicMultiplicity, defectMultiplicity, g32Angles, rankDefect, age, invAngles]

theorem papers_g32_genus_aux :
    riemannHurwitzEuler 155520 g32BranchOrders = 155520 * (-2 + 12 * (2/3) + 1/2) ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 1010880 ∧
      riemannHurwitzEuler 155520 g32BranchOrders = 2 * 505441 - 2 := by
  norm_num [riemannHurwitzEuler, g32BranchOrders]

theorem papers_g34_multiplicity_hodge_aux :
    defectMultiplicity 6 g34Angles = -12 + 20 ∧ defectMultiplicity 6 g34Angles = 8 ∧
      holomorphicMultiplicity 6 g34Angles = 20 * (1/2) - 6 ∧
      holomorphicMultiplicity 6 g34Angles = 4 ∧
      (defectMultiplicity 6 g34Angles : ℚ) - holomorphicMultiplicity 6 g34Angles = 4 := by
  norm_num [holomorphicMultiplicity, defectMultiplicity, g34Angles, rankDefect, age, invAngles]

theorem papers_qi_points_aux :
    rankDefect qiAnglesIX1 = 4 ∧ age qiAnglesIX1 = 2 ∧ rankDefect qiAnglesIX2 = 8 ∧
      age qiAnglesIX2 = 4 := by
  norm_num [rankDefect, age, qiAnglesIX1, qiAnglesIX2]

theorem papers_qi_multiplicity_hodge_aux :
    defectMultiplicity 8 qiAngles = -16 + 10 + 4 + 8 ∧ defectMultiplicity 8 qiAngles = 6 ∧
      holomorphicMultiplicity 8 qiAngles = (22 - 11) - 8 ∧
      holomorphicMultiplicity 8 qiAngles = 3 ∧
      (defectMultiplicity 8 qiAngles : ℚ) - holomorphicMultiplicity 8 qiAngles = 3 := by
  norm_num [holomorphicMultiplicity, defectMultiplicity, qiAngles, qiAnglesIX1, qiAnglesIX2,
    rankDefect, age, invAngles]

/-! ## Item 8: admissibility (G32 Table 1) and slot arithmetic (QI Proposition 8.4, Example 8.5) -/

theorem papers_g32_table_index_aux :
    g32WitnessTable.map (·.i) = List.range' 1 51 ∧
      (g32WitnessTable.map fun r => r.n.natAbs).sum = 56 := by
  decide

theorem papers_g32_table_m_aux :
    ∀ r ∈ g32WitnessTable, r.m ∈ [3, 6, 12, 15] := by
  decide

theorem papers_g32_table_h_aux :
    ∀ r ∈ g32WitnessTable, (r.h : ℤ) = 2 * r.q - 2 + r.s := by
  decide

theorem papers_g32_table_s_aux :
    ∀ r ∈ g32WitnessTable, (r.exps.map Prod.snd).sum = r.s ∧ ∀ p ∈ r.exps, 0 < p.1 ∧ p.1 < r.m := by
  decide

theorem papers_g32_table_h_pos_even_aux :
    ∀ r ∈ g32WitnessTable, 0 < r.h ∧ Even r.h := by
  decide

/-- The three exponent shapes of G32 Table 1: none, `a^k (m−a)^k` (or any `a^k b^k` with
`a + b ≡ 0`), and `a^{2j}` with `2a ≡ 0`. -/
def simpleShape (m : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | [(a, k)] => (a + a) % m == 0 && k % 2 == 0
  | [(a, k), (b, l)] => k == l && (a + b) % m == 0
  | _ => false

theorem flatMap_replicate_pair_perm (a b : ℕ) : ∀ k : ℕ,
    ((List.replicate k (a, b)).flatMap fun p => [p.1, p.2]).Perm
      (List.replicate k a ++ List.replicate k b)
  | 0 => by simp
  | k + 1 => by
    simp only [List.replicate_succ, List.flatMap_cons, List.cons_append, List.nil_append]
    refine List.Perm.cons _ ?_
    exact ((flatMap_replicate_pair_perm a b k).cons b).trans List.perm_middle.symm

theorem isSimpleExps_of_simpleShape (m : ℕ) (e : List (ℕ × ℕ)) (h : simpleShape m e = true) :
    IsSimpleExps m (expandExps e) := by
  match e, h with
  | [], _ => exact ⟨[], by simp [expandExps], by simp⟩
  | [(a, k)], h =>
    simp only [simpleShape, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨j, hj⟩ : ∃ j, k = j + j := ⟨k / 2, by omega⟩
    refine ⟨List.replicate j (a, a), ?_, by simp [h.1]⟩
    subst hj
    have e : expandExps [(a, j + j)] = List.replicate j a ++ List.replicate j a := by
      simp [expandExps]
    rw [e]
    exact flatMap_replicate_pair_perm a a j
  | [(a, k), (b, l)], h =>
    simp only [simpleShape, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hab⟩ := h
    refine ⟨List.replicate k (a, b), ?_, by simp [hab]⟩
    simpa [expandExps] using flatMap_replicate_pair_perm a b k
  | _ :: _ :: _ :: _, h => simp [simpleShape] at h

theorem papers_g32_table_simple_aux :
    ∀ r ∈ g32WitnessTable, IsSimpleExps r.m (expandExps r.exps) := by
  have h : ∀ r ∈ g32WitnessTable, simpleShape r.m r.exps = true := by decide
  exact fun r hr => isSimpleExps_of_simpleShape _ _ (h r hr)

theorem papers_g32_table_d_aux :
    ∀ r ∈ g32WitnessTable, r.d = if r.exps = [] then none else some (gcdExps r.m r.exps) := by
  decide

theorem papers_g32_table_kind_aux :
    ∀ r ∈ g32WitnessTable, (r.kind = .U ↔ r.s = 0) ∧
      (r.kind = .Sstar ↔ 0 < r.s ∧ 4 ∣ r.m ∧ ∀ p ∈ r.exps, 2 * p.1 = r.m) := by
  decide

theorem papers_not_simple_aux :
    ¬ IsSimpleExps 3 [1, 1] := by
  rintro ⟨L, hp, hL⟩
  match L, hp, hL with
  | [], hp, _ => simpa using hp.length_eq
  | [p], hp, hL =>
    have h1 : p.1 = 1 := by simpa using hp.subset (List.mem_cons_self ..)
    have h2 : p.2 = 1 := by simpa using hp.subset (by simp)
    simp [h1, h2] at hL
  | _ :: _ :: _, hp, _ => simpa using hp.length_eq

theorem papers_qi_slots_admissible_aux :
    ∀ row ∈ qiSlotTable, 1 ≤ row.genus ∧ ∀ sl ∈ row.slots, (sl.e = 4 ∨ sl.e = 12) ∧ 20 ≤ sl.s ∧
      sl.e' * sl.d = sl.e ∧ sl.e' ∣ 12 ∧ (sl.e' = 4 ∨ sl.e' = 12) := by
  decide

theorem papers_qi_slots_count_aux :
    qiSlotTable.map (fun r => r.slots.length) = [2, 4, 45] := by
  decide

theorem papers_qi_w3_h_aux :
    ∀ p ∈ qiW3SH, p.2 = 2 * 1730347 - 2 + p.1 := by
  decide

theorem papers_qi_ex85_h_aux :
    ∀ sl ∈ qiExample85, sl.h = 2 * 3259 - 2 + sl.s := by
  decide

theorem papers_qi_ex85_balance_aux :
    sumImbalance (qiExample85.map (·.imbalance)) = [0, 0, 0, 0] := by
  decide

theorem papers_qi_ex85_numerology_aux :
    (6622 + 6626 : ℤ) = 13248 ∧ (6622 - 6626 : ℤ) = -4 ∧ (3270 + 3266 : ℤ) = 6536 ∧
      (3270 - 3266 : ℤ) = 4 ∧ (6622 + 3270 : ℤ) = 9892 ∧ (6626 + 3266 : ℤ) = 9892 ∧
      (13248 + 6536 : ℤ) = 19784 ∧ (6732 - 2 : ℤ) = 6730 ∧ (20 - 2 : ℤ) = 18 ∧
      (3363 + 11 : ℤ) = 3374 ∧ (3367 + 7 : ℤ) = 3374 ∧ (6730 + 18 : ℤ) = 2 * 3374 ∧
      (3374 + 2 * 3259 : ℤ) = 9892 ∧ (2 * 9892 : ℤ) = 19784 := by
  decide

/-! ## Item 14: G34 Lemma 10.1 and Proposition 10.2, the arithmetic core -/

theorem papers_eebar_det_aux (D c m : ℚ) (hc : c ≠ 0) :
    !![c, 0; 0, -(c * m)].det = -c ^ 2 * m ∧ SameNormClass D (-c ^ 2 * m) (-m) :=
  ⟨by rw [Matrix.det_fin_two_of]; ring, c, 0, by simpa using hc, by ring⟩

theorem papers_sameNormClass_mul_aux
    (D a a' b b' : ℚ) (ha : SameNormClass D a a') (hb : SameNormClass D b b') :
    SameNormClass D (a * b) (a' * b') := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨u, v, huv, rfl⟩ := hb
  refine ⟨x * u - D * y * v, x * v + y * u, ?_, ?_⟩
  · have e : (x * u - D * y * v) ^ 2 + D * (x * v + y * u) ^ 2 =
        (x ^ 2 + D * y ^ 2) * (u ^ 2 + D * v ^ 2) := by ring
    rw [e]; exact mul_ne_zero hxy huv
  · ring

theorem papers_compensation_class_aux
    (D t m₁ : ℚ) (k n : ℕ) (hk : 1 ≤ k)
    (ht : t ≠ 0)     (hm : SameNormClass D m₁ ((-1) ^ (k + n) / t)) :
    SameNormClass D (t * (-m₁) * (-1) ^ (k - 1)) ((-1) ^ n) := by
  obtain ⟨x, y, hN, rfl⟩ := hm
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨x, y, hN, ?_⟩
  have e : (-1 : ℚ) ^ (j + 1 + n) * (-1) ^ j = -(-1) ^ n := by
    rw [← pow_add, show j + 1 + n + j = 2 * j + n + 1 by ring, pow_succ, pow_add, pow_mul]
    norm_num
  simp only [Nat.add_sub_cancel]
  linear_combination (-(x ^ 2 + D * y ^ 2) * (t / t)) * e +
    ((-1) ^ n * (x ^ 2 + D * y ^ 2)) * div_self ht

theorem papers_compensation_positive_aux (t : ℚ) (ht : t < 0) (n : ℕ) (hn : 3 ≤ n) :
    0 < (-1 : ℚ) ^ ((n - 3) + n) / t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 3 + (m + 3) = 2 * (m + 1) + 1 by omega, pow_succ, pow_mul]
  norm_num
  exact div_pos_of_neg_of_neg (by norm_num) ht

theorem papers_positive_class_nat_rep_aux (D q : ℚ) (hq : 0 < q) :
    ∃ m : ℕ, 0 < m ∧ SameNormClass D m q := by
  have hnum := Rat.num_pos.mpr hq
  refine ⟨q.num.toNat * q.den, Nat.mul_pos (by omega) q.den_pos, q.den, 0, by simp, ?_⟩
  have h1 : ((q.num.toNat : ℕ) : ℚ) = q.num := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  calc ((q.num.toNat * q.den : ℕ) : ℚ) = q.num * q.den := by push_cast [h1]; ring
    _ = q * q.den * q.den := by rw [Rat.mul_den_eq_num]
    _ = q * ((q.den : ℚ) ^ 2 + D * 0 ^ 2) := by ring

theorem papers_compensation_det_aux (c α : ℂ) :
    !![c, conj c; c * conj α ^ 2, conj (c * conj α ^ 2)].det =
      (Complex.normSq c : ℂ) * (α ^ 2 - conj α ^ 2) := by
  rw [Matrix.det_fin_two_of, ← Complex.mul_conj]
  simp only [map_mul, map_pow, Complex.conj_conj]
  ring

theorem papers_compensation_det_ne_zero_iff_aux
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (a b : ℚ) (c : ℂ) (hc : c ≠ 0) :
    !![c, conj c; c * conj ((a : ℂ) + b * ω) ^ 2, conj (c * conj ((a : ℂ) + b * ω) ^ 2)].det ≠ 0 ↔
      ∀ q : ℚ, ((a : ℂ) + b * ω) ^ 2 ≠ q := by
  rw [papers_compensation_det_aux]
  have hcω := conj_omega ω hω
  have hsq : ((a : ℂ) + b * ω) ^ 2 =
      ((a ^ 2 - b ^ 2 : ℚ) : ℂ) + ((2 * a * b - b ^ 2 : ℚ) : ℂ) * ω := by
    push_cast; linear_combination (b : ℂ) ^ 2 * hω
  have hdiff : ((a : ℂ) + b * ω) ^ 2 - conj ((a : ℂ) + b * ω) ^ 2 =
      ((2 * a * b - b ^ 2 : ℚ) : ℂ) * (2 * ω + 1) := by
    simp only [map_add, map_mul, hcω]
    rw [show ((a : ℚ) : ℂ) = ((a : ℝ) : ℂ) by simp, show ((b : ℚ) : ℂ) = ((b : ℝ) : ℂ) by simp,
      Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast; ring
  have h2 : (2 * ω + 1) ≠ 0 := by
    intro h; apply omega_im_ne_zero ω hω
    have := congrArg Complex.im h; simp at this; linarith
  have hn : (Complex.normSq c : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.mpr hc).ne'
  rw [hdiff, hsq]
  constructor
  · intro h q hq
    have hk : (2 * a * b - b ^ 2 : ℚ) ≠ 0 := by
      intro h0; apply h; rw [h0]; simp
    apply omega_ne_rat ω hω ((q - (a ^ 2 - b ^ 2)) / (2 * a * b - b ^ 2))
    rw [Rat.cast_div, eq_div_iff (by exact_mod_cast hk)]
    push_cast at hq ⊢
    linear_combination hq
  · intro h hz
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact hn h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · apply h (a ^ 2 - b ^ 2); rw [h1]; simp
    · exact h2 h1

theorem papers_compensation_example_aux (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (1 + ω) ^ 2 = ω ∧ ∀ q : ℚ, ω ≠ q := ⟨by linear_combination hω, omega_ne_rat ω hω⟩

end HodgeLean.Papers
