import HodgeLean.Foundations.Program.KernelFramesFamilyResonance

/-! # B6-5 stage 5d, family part: order conditions of analytic normal-form gauges

Matrices of power series vanishing off the resonant positions preserve the floor conditions and
are stable under products and inverses. For an analytic normal-form gauge `H` at a fixed pole,
the Taylor matrix of `(P H)⁻¹` is a graded change of the r-coefficient series and that of
`(P H)ᵀ` a graded change of the q-coefficient series, so the meromorphic order conditions of the
dictionary are the formal floor conditions of the zero-resonance gauge (`b65q_gauge_cond`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped LaurentSeries RatFunc Topology Nat
namespace HodgeLean.Foundations.Program

local notation "𝕄" => Matrix (Fin 4) (Fin 4) (PowerSeries ℂ)

/-- A matrix of power series vanishing off the positions `λ_i − λ_j = n`. -/
def b65q_graded (lam : Fin 4 → ℂ) (W : 𝕄) : Prop :=
  ∀ (n : ℕ) (i j : Fin 4), (n : ℂ) - lam i + lam j ≠ 0 → PowerSeries.coeff n (W i j) = 0

theorem b65q_graded_mul {lam : Fin 4 → ℂ} {W W' : 𝕄} (hW : b65q_graded lam W)
    (hW' : b65q_graded lam W') : b65q_graded lam (W * W') := by
  intro n i j hn
  simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun l _ ↦ Finset.sum_eq_zero fun p hp ↦ ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : (p.1 : ℂ) - lam i + lam l = 0
  · have h2 : (p.2 : ℂ) - lam l + lam j ≠ 0 := by
      intro h2; apply hn
      rw [← hp']; push_cast; linear_combination h1 + h2
    rw [hW' _ _ _ h2, mul_zero]
  · rw [hW _ _ _ h1, zero_mul]

theorem b65q_graded_inv {lam : Fin 4 → ℂ} {W V : 𝕄} (hW : b65q_graded lam W)
    (h0 : ∀ i j, PowerSeries.coeff 0 (W i j) = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j)
    (hWV : W * V = 1) : b65q_graded lam V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hn
    have hc := congrArg (fun M : 𝕄 ↦ PowerSeries.coeff n (M i j)) hWV
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
    have hterm : ∀ l, ∑ a ∈ Finset.range (n + 1),
        PowerSeries.coeff a (W i l) * PowerSeries.coeff (n - a) (V l j) =
        (1 : Matrix (Fin 4) (Fin 4) ℂ) i l * PowerSeries.coeff n (V l j) := by
      intro l
      rw [Finset.sum_range_succ', h0, Nat.sub_zero]
      rw [Finset.sum_eq_zero fun a ha ↦ ?_, zero_add]
      have ha' := Finset.mem_range.mp ha
      by_cases h1 : ((a + 1 : ℕ) : ℂ) - lam i + lam l = 0
      · have h2 : ((n - (a + 1) : ℕ) : ℂ) - lam l + lam j ≠ 0 := by
          intro h2; apply hn
          rw [Nat.cast_sub (by omega)] at h2
          linear_combination h1 + h2
        rw [ih _ (by omega) _ _ h2, mul_zero]
      · rw [hW _ _ _ h1, zero_mul]
    simp only [hterm, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at hc
    rw [hc]
    rcases n with _ | n
    · have hij : i ≠ j := by intro h; subst h; apply hn; simp
      simp [hij]
    · split_ifs <;> simp [PowerSeries.coeff_one]

theorem b65q_graded_transpose {lam : Fin 4 → ℂ} {W : 𝕄} (hW : b65q_graded lam W) :
    b65q_graded (fun i ↦ -lam i) Wᵀ := by
  intro n i j hn
  rw [Matrix.transpose_apply]
  exact hW n j i (by intro h; apply hn; linear_combination h)

/-- **Graded matrices preserve compatible floor conditions.** -/
theorem b65q_graded_ge {lam : Fin 4 → ℂ} {W : 𝕄} (hW : b65q_graded lam W) (f : Fin 4 → ℤ)
    (hf : ∀ (n : ℕ) (i j : Fin 4), (n : ℂ) = lam i - lam j → f i = f j + n)
    (y : Fin 4 → LaurentSeries ℂ) (hy : ∀ j, b65q_ge (y j) (f j)) (i : Fin 4) :
    b65q_ge (∑ j, HahnSeries.ofPowerSeries ℤ ℂ (W i j) * y j) (f i) := by
  refine b65q_ge_sum _ fun j _ ↦ ?_
  by_cases h : ∃ n : ℕ, (n : ℂ) = lam i - lam j
  · obtain ⟨n, hn⟩ := h
    have hWn : b65q_ge (HahnSeries.ofPowerSeries ℤ ℂ (W i j)) n := by
      rw [b65q_ge_iff]
      intro m hm
      rw [b65q_ofPS_coeff]
      split_ifs with h0
      · apply hW
        intro h1
        have : ((m.toNat : ℕ) : ℂ) = n := by linear_combination h1 - hn
        have : m.toNat = n := by exact_mod_cast this
        omega
      · rfl
    have := b65q_ge_mul hWn (hy j)
    rw [hf n i j hn]
    exact b65q_ge_mono this (by omega)
  · simp only [not_exists] at h
    have hz : W i j = 0 := by
      ext m
      rw [hW m i j (fun h1 ↦ h m (by linear_combination h1)), map_zero]
    rw [hz, map_zero, zero_mul]
    exact b65q_ge_zero _

/-- The Taylor matrix of a matrix-valued function. -/
def b65q_TMat (F : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ) : 𝕄 :=
  Matrix.of fun i j ↦ b65q_T (fun s ↦ F s i j) a

theorem b65q_TMat_mul {F G : ℂ → Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun s ↦ F s i j) a) (hG : ∀ i j, AnalyticAt ℂ (fun s ↦ G s i j) a) :
    b65q_TMat (fun s ↦ F s * G s) a = b65q_TMat F a * b65q_TMat G a := by
  ext i j : 1
  simp only [b65q_TMat, Matrix.of_apply, Matrix.mul_apply]
  rw [b65q_T_sum (f := fun (l : Fin 4) s ↦ F s i l * G s l j) Finset.univ
    fun l _ ↦ (hF i l).mul (hG l j)]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [b65q_T_mul (f := fun s ↦ F s i l) (g := fun s ↦ G s l j) (hF i l) (hG l j)]

theorem b65q_TMat_const (M : Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ) :
    b65q_TMat (fun _ ↦ M) a = b65q_cst M := by
  ext i j : 1; simp [b65q_TMat, b65q_cst, b65q_T_const]

theorem b65q_TMat_congr {F G : ℂ → Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ} (h : F =ᶠ[𝓝 a] G) :
    b65q_TMat F a = b65q_TMat G a := by
  ext i j : 1
  simp only [b65q_TMat, Matrix.of_apply]
  rw [b65q_T_congr (h.mono fun s hs ↦ by rw [hs])]

theorem b65q_TMat_eq_MPS (H : ℂ → Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ) :
    b65q_TMat H a = b65q_MPS (b65q_TM H a) := by
  ext i j n; simp [b65q_TMat, b65q_MPS, b65q_TM]

theorem b65q_anAt_det {F : ℂ → Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun s ↦ F s i j) a) : AnalyticAt ℂ (fun s ↦ (F s).det) a := by
  simp only [Matrix.det_apply']
  exact b65q_anAt_sum _ fun σ _ ↦ analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ hF _ _)

theorem b65q_anAt_inv {F : ℂ → Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun s ↦ F s i j) a) (hd : (F a).det ≠ 0) (i j : Fin 4) :
    AnalyticAt ℂ (fun s ↦ (F s)⁻¹ i j) a := by
  have : (fun s ↦ (F s)⁻¹ i j) = fun s ↦ ((F s).det)⁻¹ * (F s).adjugate i j := by
    funext s; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  refine ((b65q_anAt_det hF).inv hd).mul ?_
  simp only [Matrix.adjugate_apply]
  refine b65q_anAt_det (F := fun s ↦ (F s).updateRow j (Pi.single i 1)) fun p q ↦ ?_
  by_cases h : p = j
  · subst h; simpa using analyticAt_const
  · simpa [Matrix.updateRow_ne h] using hF p q

theorem b65q_TMat_inv {F : ℂ → Matrix (Fin 4) (Fin 4) ℂ} {a : ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun s ↦ F s i j) a) (hd : (F a).det ≠ 0) :
    b65q_TMat F a * b65q_TMat (fun s ↦ (F s)⁻¹) a = 1 := by
  rw [← b65q_TMat_mul hF (b65q_anAt_inv hF hd)]
  have hnear : ∀ᶠ s in 𝓝 a, (F s).det ≠ 0 := (b65q_anAt_det hF).continuousAt.eventually_ne hd
  rw [b65q_TMat_congr (G := fun _ ↦ 1) (hnear.mono fun s hs ↦ by
    simp only; exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)), b65q_TMat_const]
  simp [b65q_cst]

/-- **Order conditions for a graded change of coefficient series.** -/
theorem b65q_cond_iff {a : ℂ} {Fm : ℂ → Matrix (Fin 4) (Fin 4) ℂ}
    (hFan : ∀ i j, AnalyticAt ℂ (fun s ↦ Fm s i j) a) {lam : Fin 4 → ℂ} {W W' K : 𝕄}
    (hW : b65q_graded lam W) (hW' : b65q_graded lam W') (hWW' : W' * W = 1)
    (hT : b65q_TMat Fm a = W * K) (f : Fin 4 → ℤ)
    (hf : ∀ (n : ℕ) (i j : Fin 4), (n : ℂ) = lam i - lam j → f i = f j + n)
    (v : Fin 4 → RatFunc ℂ) :
    (∀ j, (f j : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ (Fm s *ᵥ fun i ↦ b65q_eval (v i) s) j) a) ↔
      ∀ j, b65q_ge (∑ i, HahnSeries.ofPowerSeries ℤ ℂ (K j i) * b65q_L a (v i)) (f j) := by
  set y : Fin 4 → LaurentSeries ℂ := fun l ↦ ∑ i, HahnSeries.ofPowerSeries ℤ ℂ (K l i) *
    b65q_L a (v i)
  have hord : ∀ j, meromorphicOrderAt (fun s ↦ (Fm s *ᵥ fun i ↦ b65q_eval (v i) s) j) a =
      (∑ l, HahnSeries.ofPowerSeries ℤ ℂ (W j l) * y l).orderTop := by
    intro j
    have := b65q_bridge Finset.univ a (fun i s ↦ Fm s j i) (fun i _ ↦ hFan j i) v
    simp only [Matrix.mulVec, dotProduct]
    rw [this]
    congr 1
    have hT' : ∀ i, b65q_T (fun s ↦ Fm s j i) a = (W * K) j i := fun i ↦ by
      rw [← hT]; rfl
    simp only [hT', Matrix.mul_apply, map_sum, map_mul, y, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  constructor
  · intro h j
    have hWy : ∀ m, b65q_ge (∑ l, HahnSeries.ofPowerSeries ℤ ℂ (W m l) * y l) (f m) := by
      intro m; rw [b65q_ge, ← hord m]; exact h m
    have := b65q_graded_ge hW' f hf _ hWy j
    convert this using 1
    simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hWW', Matrix.one_apply]
    simp [apply_ite (HahnSeries.ofPowerSeries ℤ ℂ)]
    rfl
  · intro h j
    rw [hord j]
    exact b65q_graded_ge hW f hf y h j

theorem b65q_gauge_rec (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4) (n : ℕ) (i j : Fin 4)
    (h : (n : ℂ) + b65p_exponents k j - b65p_exponents k i ≠ 0) :
    (n : ℂ) * b65q_gauge t A P k n i j =
      (diagonal (b65p_exponents k) * b65q_gauge t A P k n -
        b65q_gauge t A P k n * diagonal (b65p_exponents k) +
        ∑ l ∈ Finset.range n, (P⁻¹ * b65q_taylor t A k l * P) *
          b65q_gauge t A P k (n - 1 - l)) i j := by
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases n with _ | N
  · have hij : i ≠ j := by intro hij; subst hij; apply h; simp
    simp [b65q_gauge_zero_coeff, Matrix.one_apply, hij]
  · have hg : b65q_gauge t A P k (N + 1) i j =
        (∑ l ∈ Finset.range (N + 1), (P⁻¹ * b65q_taylor t A k l * P) *
          b65q_gauge t A P k (N - l)) i j /
          (((N + 1 : ℕ) : ℂ) + b65p_exponents k j - b65p_exponents k i) := by
      have hs : ∑ l ∈ Finset.range (N + 1), (P⁻¹ * b65q_taylor t A k l * P) *
          b65q_gaugeUpTo t A P k N (N - l) = ∑ l ∈ Finset.range (N + 1),
            (P⁻¹ * b65q_taylor t A k l * P) * b65q_gauge t A P k (N - l) :=
        Finset.sum_congr rfl fun l _ ↦ by rw [b65q_gaugeUpTo_stable t A P k (Nat.sub_le N l)]
      rw [b65q_gauge, b65q_gaugeUpTo, Function.update_self, Matrix.of_apply, if_neg h, hs]
    rw [hg, show N + 1 - 1 = N from rfl]
    field_simp
    ring

theorem b65q_MPS_mul_cst (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_MPS (fun n ↦ K n * M) = b65q_MPS K * b65q_cst M := by
  ext i j n
  simp [b65q_MPS, b65q_cst, Matrix.mul_apply, PowerSeries.coeff_mul_C]

theorem b65q_MPS_cst_mul (M : Matrix (Fin 4) (Fin 4) ℂ) (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_MPS (fun n ↦ M * K n) = b65q_cst M * b65q_MPS K := by
  ext i j n
  simp [b65q_MPS, b65q_cst, Matrix.mul_apply, PowerSeries.coeff_C_mul]

theorem b65q_MPS_transpose (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_MPS (fun n ↦ (K n)ᵀ) = (b65q_MPS K)ᵀ := by
  ext i j n; simp [b65q_MPS]

/-- **The order conditions of an analytic normal-form gauge.** For an analytic solution `H` of
the normal-form equation at the fixed pole `k`, the order conditions on `(P H)⁻¹ r` and
`(P H)ᵀ q` are the formal conditions on the coefficient series of the zero-resonance gauge. -/
theorem b65q_gauge_cond (t : Fin 4 ⊕ Fin 12 → ℂ) (A : Fin 4 ⊕ Fin 12 → Matrix (Fin 4) (Fin 4) ℂ)
    (P : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (k : Fin 4)
    (hne : ∀ q, q ≠ Sum.inl k → t (Sum.inl k) ≠ t q) (hPk : IsUnit (P k))
    (H : ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (hH : ∀ i j, AnalyticAt ℂ (fun s ↦ H s i j) (t (Sum.inl k))) (hH0 : H (t (Sum.inl k)) = 1)
    (hode : ∀ᶠ s in 𝓝 (t (Sum.inl k)), ∀ i j : Fin 4,
      (s - t (Sum.inl k)) * deriv (fun s ↦ H s i j) s =
        (diagonal (b65p_exponents k) * H s - H s * diagonal (b65p_exponents k) +
          (s - t (Sum.inl k)) • ((P k)⁻¹ * b65q_regular t A k s * P k * H s)) i j) :
    (∀ f : Fin 4 → ℤ, (∀ (n : ℕ) (i j : Fin 4),
        (n : ℂ) = b65p_exponents k i - b65p_exponents k j → f i = f j + n) →
      ∀ r : Fin 4 → RatFunc ℂ,
        (∀ j, (f j : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s ↦ ((P k * H s)⁻¹ *ᵥ fun i ↦ b65q_eval (r i) s) j) (t (Sum.inl k))) ↔
        ∀ j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_rCoeff t A P k) r j) (f j)) ∧
    (∀ f : Fin 4 → ℤ, (∀ (n : ℕ) (i j : Fin 4),
        (n : ℂ) = -b65p_exponents k i - -b65p_exponents k j → f i = f j + n) →
      ∀ q : Fin 4 → RatFunc ℂ,
        (∀ j, (f j : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s ↦ ((P k * H s)ᵀ *ᵥ fun i ↦ b65q_eval (q i) s) j) (t (Sum.inl k))) ↔
        ∀ j, b65q_ge (b65q_KL (t (Sum.inl k)) (b65q_qCoeff t A P k) q j) (f j)) := by
  set a := t (Sum.inl k) with ha
  set Ĥ := b65q_TM H a
  have hĤ0 : Ĥ 0 = 1 := by
    ext i j
    simp only [Ĥ, b65q_TM, Matrix.of_apply, b65q_T_coeff, iteratedDeriv_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, hH0]
  have hĤ : ∀ (n : ℕ) (i j : Fin 4), (n : ℂ) * Ĥ n i j =
      (diagonal (b65p_exponents k) * Ĥ n - Ĥ n * diagonal (b65p_exponents k) +
        ∑ l ∈ Finset.range n, ((P k)⁻¹ * b65q_taylor t A k l * P k) * Ĥ (n - 1 - l)) i j :=
    b65q_gauge_taylor t A (P k) k (b65p_exponents k) hne H hH hode
  set H₀ := b65q_gauge t A (P k) k
  have hH₀0 : H₀ 0 = 1 := b65q_gauge_zero_coeff t A (P k) k
  set Y := b65q_MPS H₀
  set Y' := b65q_MPS (b65q_seriesInv H₀)
  set Hm := b65q_MPS Ĥ
  set Hm' := b65q_MPS (b65q_seriesInv Ĥ)
  set U := Y' * Hm
  set V := Hm' * Y
  have hYY' : Y * Y' = 1 := b65q_MPS_seriesInv H₀ hH₀0
  have hY'Y : Y' * Y = 1 := mul_eq_one_comm.mp hYY'
  have hHH' : Hm * Hm' = 1 := b65q_MPS_seriesInv Ĥ hĤ0
  have hUV : U * V = 1 := by
    simp only [U, V]
    rw [show Y' * Hm * (Hm' * Y) = Y' * (Hm * Hm') * Y by noncomm_ring, hHH', mul_one, hY'Y]
  have hVU : V * U = 1 := mul_eq_one_comm.mp hUV
  have hU : b65q_graded (b65p_exponents k) U :=
    b65q_resonance (b65p_exponents k) (fun l ↦ (P k)⁻¹ * b65q_taylor t A k l * P k) H₀ Ĥ
      hH₀0 hĤ0 (fun n i j h ↦ b65q_gauge_rec t A (P k) k n i j h) hĤ
  have hU0 : ∀ i j, PowerSeries.coeff 0 (U i j) = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := by
    intro i j
    simp only [U, Y', Hm, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul]
    simp [b65q_MPS, b65q_seriesInv, b65q_seriesInvUpTo, hĤ0, Matrix.one_apply]
  have hV : b65q_graded (b65p_exponents k) V := b65q_graded_inv hU hU0 hUV
  have hHm : Hm = Y * U := by simp only [U]; rw [← mul_assoc, hYY', one_mul]
  have hFan : ∀ i j, AnalyticAt ℂ (fun s ↦ (P k * H s) i j) a := by
    intro i j
    simp only [Matrix.mul_apply]
    exact b65q_anAt_sum _ fun l _ ↦ analyticAt_const.mul (hH l j)
  have hTF : b65q_TMat (fun s ↦ P k * H s) a = b65q_cst (P k) * Y * U := by
    rw [b65q_TMat_mul (F := fun _ ↦ P k) (fun _ _ ↦ analyticAt_const) hH, b65q_TMat_const,
      b65q_TMat_eq_MPS, mul_assoc, ← hHm]
  have hPdet : (P k).det ≠ 0 := ((isUnit_iff_isUnit_det _).mp hPk).ne_zero
  have hdet : (P k * H a).det ≠ 0 := by rw [hH0, mul_one]; exact hPdet
  have hcstP : b65q_cst (P k) * b65q_cst (P k)⁻¹ = 1 := by
    rw [← b65q_cst_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hPdet)]
    simp [b65q_cst]
  have hTinv : b65q_TMat (fun s ↦ (P k * H s)⁻¹) a = V * b65q_MPS (b65q_rCoeff t A P k) := by
    have h1 := b65q_TMat_inv hFan hdet
    have hZ : b65q_TMat (fun s ↦ P k * H s) a * (V * (Y' * b65q_cst (P k)⁻¹)) = 1 := by
      rw [hTF, show b65q_cst (P k) * Y * U * (V * (Y' * b65q_cst (P k)⁻¹)) =
        b65q_cst (P k) * Y * (U * V) * Y' * b65q_cst (P k)⁻¹ by noncomm_ring, hUV, mul_one,
        mul_assoc (b65q_cst (P k)), hYY', mul_one, hcstP]
    have hL : (V * (Y' * b65q_cst (P k)⁻¹)) * b65q_TMat (fun s ↦ P k * H s) a = 1 :=
      mul_eq_one_comm.mp hZ
    have : b65q_TMat (fun s ↦ (P k * H s)⁻¹) a = V * (Y' * b65q_cst (P k)⁻¹) := by
      calc b65q_TMat (fun s ↦ (P k * H s)⁻¹) a =
          ((V * (Y' * b65q_cst (P k)⁻¹)) * b65q_TMat (fun s ↦ P k * H s) a) *
            b65q_TMat (fun s ↦ (P k * H s)⁻¹) a := by rw [hL, one_mul]
        _ = V * (Y' * b65q_cst (P k)⁻¹) := by rw [mul_assoc, h1, mul_one]
    rw [this, ← b65q_MPS_mul_cst]
    rfl
  have hTtr : b65q_TMat (fun s ↦ (P k * H s)ᵀ) a = Uᵀ * b65q_MPS (b65q_qCoeff t A P k) := by
    have : b65q_TMat (fun s ↦ (P k * H s)ᵀ) a = (b65q_TMat (fun s ↦ P k * H s) a)ᵀ := by
      ext i j : 1; simp [b65q_TMat]
    rw [this, hTF, Matrix.transpose_mul]
    congr 1
    rw [show b65q_qCoeff t A P k = fun n ↦ (P k * H₀ n)ᵀ from rfl, b65q_MPS_transpose,
      b65q_MPS_cst_mul]
  refine ⟨fun f hf r ↦ ?_, fun f hf q ↦ ?_⟩
  · exact b65q_cond_iff (fun i j ↦ b65q_anAt_inv hFan hdet i j) hV hU hUV hTinv f hf r
  · have hVt : Vᵀ * Uᵀ = 1 := by rw [← Matrix.transpose_mul, hUV, Matrix.transpose_one]
    exact b65q_cond_iff (fun i j ↦ by simpa using hFan j i) (b65q_graded_transpose hU)
      (b65q_graded_transpose hV) hVt hTtr f hf q

end HodgeLean.Foundations.Program
