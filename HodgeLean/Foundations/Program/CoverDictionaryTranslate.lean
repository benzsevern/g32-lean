import HodgeLean.Foundations.Program.CoverDictionaryCriteria

/-! # B6-5 stage 5d, stage four: the order conditions of the dictionary spaces

General statements in one complex variable. If `e d = m` then `⌊Re d⌋ = m / e` and
`⌊Re (−d)⌋ = (−m) / e` (`caf_floor_div`). At a moving pole, with exponents `0, 0, 0, λ`,
`0 < λ < 1`, the r-condition is holomorphy of `r` (`caf_moving_r_iff`) and the q-condition is a
simple pole whose pairing with the kernel of the residue is holomorphic (`caf_moving_q_iff`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- **Floors of exponents** with integer multiples. -/
theorem caf_floor_div (e : ℕ) (he : 0 < e) (d : ℂ) (m : ℤ) (h : (e : ℂ) * d = m) :
    ⌊d.re⌋ = m / (e : ℤ) ∧ ⌊(-d).re⌋ = (-m) / (e : ℤ) := by
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hd : d = (m : ℂ) / e := by rw [← h]; field_simp
  have hre : d.re = (m : ℝ) / e := by
    rw [hd]
    simp [Complex.div_re, Complex.normSq]
    field_simp
  have key : ∀ n : ℤ, ⌊(n : ℝ) / e⌋ = n / (e : ℤ) := by
    intro n
    have : (n : ℝ) / e = (((n : ℚ) / e : ℚ) : ℝ) := by push_cast; rfl
    rw [this, Rat.floor_cast, Rat.floor_intCast_div_natCast]
  constructor
  · rw [hre]; exact key m
  · rw [Complex.neg_re, hre, ← neg_div, show -(m : ℝ) = ((-m : ℤ) : ℝ) by push_cast; ring]
    exact key (-m)

/-- The exponent quotients at a moving pole: `0` for r, and `0, 0, 0, −1` for q. -/
theorem caf_moving_quotients (e : ℕ) (he : 0 < e) (q : ℚ) (hq : q = 1 / 3 ∨ q = 2 / 3)
    (m : Fin 4 → ℤ) (hm : ∀ i, (e : ℂ) * (![0, 0, 0, (q : ℂ)] : Fin 4 → ℂ) i = m i) :
    (∀ i, m i / (e : ℤ) = 0) ∧ ∀ i, (-m i) / (e : ℤ) = (![0, 0, 0, -1] : Fin 4 → ℤ) i := by
  have hfl := fun i ↦ caf_floor_div e he _ (m i) (hm i)
  have h0 : (0 : ℚ) < q ∧ q < 1 := by rcases hq with rfl | rfl <;> norm_num
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast h0.1
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast h0.2
  have hfq : ⌊((q : ℂ)).re⌋ = 0 := by
    rw [show ((q : ℂ)).re = (q : ℝ) by simp, Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  have hfq' : ⌊(-(q : ℂ)).re⌋ = -1 := by
    rw [show (-(q : ℂ)).re = -(q : ℝ) by simp, Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  constructor
  · intro i
    rw [← (hfl i).1]
    fin_cases i
    · simp
    · simp
    · simp
    · exact hfq
  · intro i
    rw [← (hfl i).2]
    fin_cases i
    · simp
    · simp
    · simp
    · exact hfq'

/-- **The r-condition at a moving pole** is holomorphy. -/
theorem caf_moving_r_iff (M : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (t₀ : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun σ ↦ M σ i j) t₀) (hMd : (M t₀).det ≠ 0)
    (R : ℂ → Fin 4 → ℂ) (hR : ∀ j, MeromorphicAt (fun σ ↦ R σ j) t₀) :
    (∀ i, (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ ((M σ)⁻¹ *ᵥ R σ) i) t₀) ↔
      ∀ i, (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ R σ i) t₀ := by
  obtain ⟨hMi, -⟩ := caf_inv_entries_analyticAt M t₀ hM hMd
  refine caf_order_matrix_iff (fun σ ↦ (M σ)⁻¹) R t₀ hMi ?_ hR 0
  rw [Matrix.det_nonsing_inv]
  exact (isUnit_iff_ne_zero.mpr hMd).ringInverse.ne_zero

/-- Entries of products of analytic matrices are analytic. -/
theorem caf_matrix_mul_analyticAt (A B : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (z : ℂ)
    (hA : ∀ i j, AnalyticAt ℂ (fun σ ↦ A σ i j) z) (hB : ∀ i j, AnalyticAt ℂ (fun σ ↦ B σ i j) z)
    (i j : Fin 4) : AnalyticAt ℂ (fun σ ↦ (A σ * B σ) i j) z := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun k _ ↦ (hA i k).mul (hB k j)

/-- **The q-condition at a moving pole.** Let `A Pm = Pm diag(0, 0, 0, λ)` with `λ ≠ 0` and `Pm`
invertible, `L` analytic with `L(t₀) = 1`. The components of `(L Pm)ᵀ Q` have orders at least
`0, 0, 0, −1` exactly when `Q` has at most a simple pole and its pairing with the kernel of `A`
is holomorphic. -/
theorem caf_moving_q_iff (L : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (t₀ : ℂ)
    (hL : ∀ i j, AnalyticAt ℂ (fun σ ↦ L σ i j) t₀) (hL1 : L t₀ = 1)
    (Pm A : Matrix (Fin 4) (Fin 4) ℂ) (hPm : IsUnit Pm.det) (lam : ℂ) (hlam : lam ≠ 0)
    (hAP : A * Pm = Pm * diagonal ![0, 0, 0, lam])
    (Q : ℂ → Fin 4 → ℂ) (hQ : ∀ j, MeromorphicAt (fun σ ↦ Q σ j) t₀) :
    (∀ i, (((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun σ ↦ ((L σ * Pm)ᵀ *ᵥ Q σ) i) t₀) ↔
      (∀ i, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ Q σ i) t₀) ∧
      ∀ v, A *ᵥ v = 0 → (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ v ⬝ᵥ Q σ) t₀ := by
  set n : Fin 4 → ℤ := ![0, 0, 0, -1]
  have hn : ∀ i j, i ≠ j → n i ≤ n j + 1 := by
    intro i j _; fin_cases i <;> fin_cases j <;> simp [n]
  have hn1 : ∀ i, (-1 : ℤ) ≤ n i := by intro i; fin_cases i <;> simp [n]
  have hn0 : ∀ i : Fin 4, i ≠ 3 → n i = 0 := by intro i hi; fin_cases i <;> simp_all [n]
  have hPt : IsUnit Pmᵀ.det := by rw [Matrix.det_transpose]; exact hPm
  set U : ℂ → Fin 4 → ℂ := fun σ ↦ Pmᵀ *ᵥ Q σ
  have hU : ∀ j, MeromorphicAt (fun σ ↦ U σ j) t₀ := fun j ↦
    caf_meromorphic_mulVec (fun _ ↦ Pmᵀ) Q t₀ (fun _ _ ↦ MeromorphicAt.const _ _) hQ j
  set N : ℂ → Matrix (Fin 4) (Fin 4) ℂ := fun σ ↦ Pmᵀ * (L σ)ᵀ * Pmᵀ⁻¹
  have hN : ∀ i j, AnalyticAt ℂ (fun σ ↦ N σ i j) t₀ :=
    caf_matrix_mul_analyticAt _ (fun _ ↦ Pmᵀ⁻¹) t₀
      (caf_matrix_mul_analyticAt (fun _ ↦ Pmᵀ) (fun σ ↦ (L σ)ᵀ) t₀
        (fun _ _ ↦ analyticAt_const) (fun i j ↦ hL j i)) (fun _ _ ↦ analyticAt_const)
  have hN1 : N t₀ = 1 := by
    simp only [N, hL1, Matrix.transpose_one, mul_one]
    exact Matrix.mul_nonsing_inv _ hPt
  have hW : ∀ σ, (L σ * Pm)ᵀ *ᵥ Q σ = N σ *ᵥ U σ := by
    intro σ
    simp only [N, U, Matrix.mulVec_mulVec, Matrix.transpose_mul, mul_assoc,
      Matrix.nonsing_inv_mul _ hPt, mul_one]
  -- the kernel of `A` is spanned by the first three columns of `Pm`
  have hker : ∀ v, A *ᵥ v = 0 → (Pm⁻¹ *ᵥ v) 3 = 0 := by
    intro v hv
    have hv' : v = Pm *ᵥ (Pm⁻¹ *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPm, Matrix.one_mulVec]
    have h1 : Pm *ᵥ (diagonal ![0, 0, 0, lam] *ᵥ (Pm⁻¹ *ᵥ v)) = 0 := by
      rw [Matrix.mulVec_mulVec (M := Pm), ← hAP, ← Matrix.mulVec_mulVec, ← hv', hv]
    have h2 : diagonal ![0, 0, 0, lam] *ᵥ (Pm⁻¹ *ᵥ v) = 0 := by
      have := congrArg (fun w ↦ Pm⁻¹ *ᵥ w) h1
      simp only [Matrix.mulVec_zero] at this
      rwa [Matrix.mulVec_mulVec (M := Pm⁻¹) (N := Pm), Matrix.nonsing_inv_mul _ hPm,
        Matrix.one_mulVec] at this
    have h3 := congrFun h2 3
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at h3
    exact (mul_eq_zero.mp h3).resolve_left (by simpa using hlam)
  have hcol : ∀ i : Fin 4, i ≠ 3 → A *ᵥ (fun j ↦ Pm j i) = 0 := by
    intro i hi
    have hc : (fun j ↦ Pm j i) = Pm *ᵥ Pi.single i 1 := by
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hd : diagonal ![0, 0, 0, lam] *ᵥ Pi.single i 1 = 0 := by
      funext k
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply, Pi.single_apply]
      split_ifs with hk
      · subst hk; fin_cases k <;> simp_all
      · simp
    rw [hc, Matrix.mulVec_mulVec, hAP, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_zero]
  constructor
  · intro h
    -- the orders of `U = N⁻¹ W`
    obtain ⟨hNi, hNev⟩ := caf_inv_entries_analyticAt N t₀ hN (by rw [hN1, det_one]; exact one_ne_zero)
    have hNi1 : (N t₀)⁻¹ = 1 := by rw [hN1, inv_one]
    have hWm : ∀ j, MeromorphicAt (fun σ ↦ ((L σ * Pm)ᵀ *ᵥ Q σ) j) t₀ := fun j ↦ by
      simp only [hW]
      exact caf_meromorphic_mulVec N U t₀ (fun i j ↦ (hN i j).meromorphicAt) hU j
    have hUo : ∀ i, (n i : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ U σ i) t₀ := by
      intro i
      have := caf_order_unipotent (fun σ ↦ (N σ)⁻¹) (fun σ ↦ (L σ * Pm)ᵀ *ᵥ Q σ) t₀ hNi hNi1
        hWm n hn h i
      rwa [meromorphicOrderAt_congr (f₂ := fun σ ↦ U σ i)] at this
      filter_upwards [nhdsWithin_le_nhds hNev] with σ hσ
      rw [hW, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hσ),
        Matrix.one_mulVec]
    refine ⟨?_, ?_⟩
    · have key := (caf_order_matrix_iff (fun _ ↦ Pmᵀ⁻¹) U t₀ (fun _ _ ↦ analyticAt_const)
        (by rw [Matrix.det_nonsing_inv]; exact hPt.ringInverse.ne_zero) hU (-1)).mpr
        (fun i ↦ le_trans (by
          rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl]
          exact WithTop.coe_le_coe.mpr (hn1 i)) (hUo i))
      intro i
      have := key i
      simpa [U, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPt] using this
    · intro v hv
      set w := Pm⁻¹ *ᵥ v
      have hw3 : w 3 = 0 := hker v hv
      have hvw : ∀ σ, v ⬝ᵥ Q σ = ∑ i, w i * U σ i := by
        intro σ
        have : v = Pm *ᵥ w := by
          simp [w, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPm]
        rw [this, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
        simp only [U, Matrix.mulVec_transpose, dotProduct]
      simp only [hvw]
      refine (caf_order_sum_ge Finset.univ (fun i σ ↦ w i * U σ i) t₀
        (fun i _ ↦ (MeromorphicAt.const _ _).mul (hU i)) 0 fun i _ ↦ ?_).2
      by_cases hi : i = 3
      · subst hi
        simp [hw3, meromorphicOrderAt_const]
      · rw [show (fun σ ↦ w i * U σ i) = (fun _ ↦ w i) * fun σ ↦ U σ i from rfl,
          meromorphicOrderAt_mul (MeromorphicAt.const _ _) (hU i), meromorphicOrderAt_const]
        split_ifs
        · simp
        · rw [zero_add]
          have := hUo i
          rwa [hn0 i hi] at this
  · rintro ⟨h1, h2⟩ i
    have hUo : ∀ j, (n j : WithTop ℤ) ≤ meromorphicOrderAt (fun σ ↦ U σ j) t₀ := by
      intro j
      by_cases hj : j = 3
      · subst hj
        have := (caf_order_matrix_iff (fun _ ↦ Pmᵀ) Q t₀ (fun _ _ ↦ analyticAt_const)
          hPt.ne_zero hQ (-1)).mpr h1 3
        simpa [n] using this
      · rw [hn0 j hj]
        have := h2 (fun k ↦ Pm k j) (hcol j hj)
        refine le_of_le_of_eq this ?_
        congr 1
    have := caf_order_unipotent N U t₀ hN hN1 hU n hn hUo i
    simpa only [hW] using this

end HodgeLean.Foundations.Program
