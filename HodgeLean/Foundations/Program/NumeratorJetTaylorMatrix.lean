import HodgeLean.Foundations.Program.KernelFramesFamilyGauge
import HodgeLean.Foundations.Program.NumeratorJetConvolution

/-! # Taylor coefficients of matrix-valued analytic germs at the centre -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology Nat
namespace HodgeLean.Foundations.Program

variable {l m n : Type*}

/-- Matrix of order-`k` Taylor coefficients at `0` of a matrix-valued function. -/
def b65e_TC (F : ℂ → Matrix m n ℂ) (k : ℕ) : Matrix m n ℂ :=
  Matrix.of fun i j ↦ PowerSeries.coeff k (b65q_T (fun θ ↦ F θ i j) 0)

/-- A power series at the centre computes the Taylor coefficients. -/
theorem b65e_T_coeff_of_series {f : ℂ → ℂ} {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (k : ℕ) :
    PowerSeries.coeff k (b65q_T f 0) = P.coeff k := by
  rw [b65q_T_coeff, ← b65e_factorial_mul_coeff hP k]
  have h : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Taylor coefficients depend only on the germ at the centre. -/
theorem b65e_TC_congr {F G : ℂ → Matrix m n ℂ} (h : F =ᶠ[𝓝 0] G) (k : ℕ) :
    b65e_TC F k = b65e_TC G k := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply]
  rw [b65q_T_congr (h.mono fun θ hθ ↦ by rw [hθ])]

/-- Taylor coefficients of a constant matrix. -/
theorem b65e_TC_const (M : Matrix m n ℂ) (k : ℕ) :
    b65e_TC (fun _ ↦ M) k = if k = 0 then M else 0 := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, b65q_T_const, PowerSeries.coeff_C]
  split_ifs <;> simp

/-- Taylor coefficients are additive on analytic germs. -/
theorem b65e_TC_add {F G : ℂ → Matrix m n ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0)
    (hG : ∀ i j, AnalyticAt ℂ (fun θ ↦ G θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ F θ + G θ) k = b65e_TC F k + b65e_TC G k := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.add_apply]
  rw [b65q_T_add (hF i j) (hG i j), map_add]

/-- Taylor coefficients commute with negation. -/
theorem b65e_TC_neg (F : ℂ → Matrix m n ℂ) (k : ℕ) :
    b65e_TC (fun θ ↦ -F θ) k = -b65e_TC F k := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.neg_apply, b65q_T_coeff]
  rw [show (fun θ ↦ -F θ i j) = -fun θ ↦ F θ i j from rfl, iteratedDeriv_neg, neg_div]

/-- Taylor coefficients are subtractive on analytic germs. -/
theorem b65e_TC_sub {F G : ℂ → Matrix m n ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0)
    (hG : ∀ i j, AnalyticAt ℂ (fun θ ↦ G θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ F θ - G θ) k = b65e_TC F k - b65e_TC G k := by
  have hG' : ∀ i j, AnalyticAt ℂ (fun θ ↦ (-G θ) i j) 0 := fun i j ↦ (hG i j).neg
  simp only [sub_eq_add_neg]
  rw [b65e_TC_add hF hG', b65e_TC_neg]

/-- Taylor coefficients of a matrix product are the finite convolution of coefficients. -/
theorem b65e_TC_mul [Fintype n] {F : ℂ → Matrix l n ℂ} {G : ℂ → Matrix n m ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0)
    (hG : ∀ i j, AnalyticAt ℂ (fun θ ↦ G θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ F θ * G θ) k =
      ∑ a ∈ Finset.range (k + 1), b65e_TC F a * b65e_TC G (k - a) := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply]
  have hs : b65q_T (fun θ ↦ ∑ t, F θ i t * G θ t j) 0 =
      ∑ t, b65q_T (fun θ ↦ F θ i t * G θ t j) 0 :=
    b65q_T_sum Finset.univ fun t _ ↦ (hF i t).mul (hG t j)
  rw [hs, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [b65q_T_mul (hF i t) (hG t j), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Taylor coefficients of a scalar multiple by a constant. -/
theorem b65e_TC_smul (c : ℂ) {F : ℂ → Matrix m n ℂ}
    (hF : ∀ i j, AnalyticAt ℂ (fun θ ↦ F θ i j) 0) (k : ℕ) :
    b65e_TC (fun θ ↦ c • F θ) k = c • b65e_TC F k := by
  ext i j
  simp only [b65e_TC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [b65q_T_const_mul c (hF i j), PowerSeries.coeff_C_mul]

/-- Taylor coefficients commute with transposition. -/
theorem b65e_TC_transpose (F : ℂ → Matrix m n ℂ) (k : ℕ) :
    b65e_TC (fun θ ↦ (F θ)ᵀ) k = (b65e_TC F k)ᵀ := by
  ext i j
  rfl

/-- Taylor coefficients commute with taking submatrices. -/
theorem b65e_TC_submatrix {m' n' : Type*} (F : ℂ → Matrix m n ℂ) (r : m' → m) (c : n' → n)
    (k : ℕ) :
    b65e_TC (fun θ ↦ (F θ).submatrix r c) k = (b65e_TC F k).submatrix r c := by
  ext i j
  rfl

/-- The order-zero Taylor coefficient is the value at the centre. -/
theorem b65e_TC_zero (F : ℂ → Matrix m n ℂ) : b65e_TC F 0 = F 0 := by
  ext i j
  simp [b65e_TC, b65q_T_coeff]

/-- A convolution equation with left-invertible leading coefficient has unique solutions. -/
theorem b65e_conv_unique [Fintype l] [Fintype n] [DecidableEq n] (L : ℕ → Matrix l n ℂ)
    (C : Matrix n l ℂ) (hC : C * L 0 = 1) (X Y : ℕ → Matrix n m ℂ) (N : ℕ)
    (h : ∀ k < N, ∑ a ∈ Finset.range (k + 1), L a * X (k - a) =
      ∑ a ∈ Finset.range (k + 1), L a * Y (k - a)) :
    ∀ k < N, X k = Y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hk' := h k hk
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hk'
    have hs : ∑ a ∈ Finset.range k, L (a + 1) * X (k - (a + 1)) =
        ∑ a ∈ Finset.range k, L (a + 1) * Y (k - (a + 1)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have := Finset.mem_range.mp ha
      rw [ih (k - (a + 1)) (by omega) (by omega)]
    rw [hs, add_left_cancel_iff] at hk'
    simp only [Nat.sub_zero] at hk'
    calc
      X k = C * L 0 * X k := by rw [hC, Matrix.one_mul]
      _ = C * L 0 * Y k := by rw [Matrix.mul_assoc, hk', ← Matrix.mul_assoc]
      _ = Y k := by rw [hC, Matrix.one_mul]

end HodgeLean.Foundations.Program
