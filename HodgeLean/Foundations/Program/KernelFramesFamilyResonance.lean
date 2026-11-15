import HodgeLean.Foundations.Program.KernelFramesFamilyGauge

/-! # B6-5 stage 5d, family part: resonant freedom of normal-form gauges

Matrices of power series with the Euler operator; the defect of the normal-form equation is
multiplicative up to `D(U) = X dU/dX − [Λ, U]` (`b65q_defect_mul`). If one sequence solves the
recursion and the zero-resonance gauge solves it at the nonresonant entries, then the zero-
resonance gauge solves it everywhere and their quotient vanishes off the resonant positions
`λ_i − λ_j = n` (`b65q_resonance`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Polynomial Matrix Filter
open scoped LaurentSeries RatFunc Topology Nat
namespace HodgeLean.Foundations.Program

local notation "𝕄" => Matrix (Fin 4) (Fin 4) (PowerSeries ℂ)

/-- The matrix of power series of a sequence of matrices. -/
def b65q_MPS (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) : 𝕄 :=
  Matrix.of fun i j ↦ PowerSeries.mk fun n ↦ K n i j

theorem b65q_MPS_apply (K : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    b65q_MPS K i j = b65q_Kps K i j := rfl

theorem b65q_MPS_mul (K K' : ℕ → Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_MPS K * b65q_MPS K' =
      b65q_MPS fun n ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, K p.1 * K' p.2 := by
  ext i j n
  simp only [b65q_MPS, Matrix.mul_apply, Matrix.of_apply, map_sum, PowerSeries.coeff_mul,
    PowerSeries.coeff_mk, Matrix.sum_apply]
  rw [Finset.sum_comm]

theorem b65q_MPS_seriesInv (H : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (h0 : H 0 = 1) :
    b65q_MPS H * b65q_MPS (b65q_seriesInv H) = 1 := by
  rw [b65q_MPS_mul]
  ext i j n
  simp only [b65q_MPS, Matrix.of_apply, PowerSeries.coeff_mk, b65q_seriesInv_mul H h0,
    Matrix.one_apply]
  split_ifs with h1 h2 h2 <;> simp [h1, h2, PowerSeries.coeff_one, Matrix.one_apply]

/-- The constant matrix of power series. -/
def b65q_cst (M : Matrix (Fin 4) (Fin 4) ℂ) : 𝕄 := M.map PowerSeries.C

theorem b65q_cst_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    b65q_cst (M * N) = b65q_cst M * b65q_cst N := by
  simp [b65q_cst, Matrix.map_mul]

/-- The Euler operator `X d/dX`, entrywise. -/
def b65q_δ (M : 𝕄) : 𝕄 := Matrix.of fun i j ↦ PowerSeries.X * PowerSeries.derivative (R := ℂ) (M i j)

theorem b65q_δ_mul (M N : 𝕄) : b65q_δ (M * N) = b65q_δ M * N + M * b65q_δ N := by
  ext i j
  simp only [b65q_δ, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

theorem b65q_δ_coeff (M : 𝕄) (n : ℕ) (i j : Fin 4) :
    PowerSeries.coeff n (b65q_δ M i j) = (n : ℂ) * PowerSeries.coeff n (M i j) := by
  simp only [b65q_δ, Matrix.of_apply]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast; ring

/-- The defect of the normal-form equation, `X d/dX 𝐗 − [Λ, 𝐗] − X 𝐆 𝐗`. -/
def b65q_defect (lam : Fin 4 → ℂ) (G : 𝕄) (M : 𝕄) : 𝕄 :=
  b65q_δ M - (b65q_cst (diagonal lam) * M - M * b65q_cst (diagonal lam)) -
    ((PowerSeries.X : PowerSeries ℂ) • (1 : 𝕄)) * (G * M)

/-- The Euler operator minus the commutator with `Λ`. -/
def b65q_D (lam : Fin 4 → ℂ) (M : 𝕄) : 𝕄 :=
  b65q_δ M - (b65q_cst (diagonal lam) * M - M * b65q_cst (diagonal lam))

theorem b65q_defect_mul (lam : Fin 4 → ℂ) (G Y U : 𝕄) :
    b65q_defect lam G (Y * U) = b65q_defect lam G Y * U + Y * b65q_D lam U := by
  simp only [b65q_defect, b65q_D, b65q_δ_mul]
  noncomm_ring

theorem b65q_D_coeff (lam : Fin 4 → ℂ) (U : 𝕄) (n : ℕ) (i j : Fin 4) :
    PowerSeries.coeff n (b65q_D lam U i j) =
      ((n : ℂ) - lam i + lam j) * PowerSeries.coeff n (U i j) := by
  simp only [b65q_D, Matrix.sub_apply, map_sub, b65q_δ_coeff, b65q_cst, Matrix.mul_apply,
    Matrix.map_apply, Matrix.diagonal_apply]
  simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C]
  ring

theorem b65q_defect_coeff (lam : Fin 4 → ℂ) (G X : ℕ → Matrix (Fin 4) (Fin 4) ℂ) (n : ℕ)
    (i j : Fin 4) :
    PowerSeries.coeff n (b65q_defect lam (b65q_MPS G) (b65q_MPS X) i j) =
      (n : ℂ) * X n i j - (diagonal lam * X n - X n * diagonal lam +
        ∑ l ∈ Finset.range n, G l * X (n - 1 - l)) i j := by
  have hD := b65q_D_coeff lam (b65q_MPS X) n i j
  have hsplit : b65q_defect lam (b65q_MPS G) (b65q_MPS X) = b65q_D lam (b65q_MPS X) -
      ((PowerSeries.X : PowerSeries ℂ) • (1 : 𝕄)) * (b65q_MPS G * b65q_MPS X) := by
    simp [b65q_defect, b65q_D]
  rw [hsplit, Matrix.sub_apply, map_sub, hD, Matrix.smul_mul, one_mul, Matrix.smul_apply,
    smul_eq_mul, b65q_MPS_mul]
  simp only [b65q_MPS, Matrix.of_apply, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sum_apply]
  rcases n with _ | n
  · simp; ring
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [show n + 1 - 1 = n from rfl]
    push_cast
    ring

theorem b65q_coeff_triple (A B C : 𝕄) (n : ℕ) (hB : ∀ m < n, ∀ i j, PowerSeries.coeff m (B i j) = 0)
    (i j : Fin 4) :
    PowerSeries.coeff n ((A * B * C) i j) = ∑ p, ∑ q, PowerSeries.coeff 0 (A i p) *
      PowerSeries.coeff n (B p q) * PowerSeries.coeff 0 (C q j) := by
  have hB' : ∀ p q, ∃ B' : PowerSeries ℂ, B p q = PowerSeries.X ^ n * B' := fun p q ↦
    PowerSeries.X_pow_dvd_iff.mpr fun m hm ↦ hB m hm p q
  choose B' hB' using hB'
  simp only [Matrix.mul_apply, Finset.sum_mul, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hB' p q, show A i p * (PowerSeries.X ^ n * B' p q) * C q j =
    PowerSeries.X ^ n * (A i p * B' p q * C q j) by ring]
  have := PowerSeries.coeff_X_pow_mul (A i p * B' p q * C q j) n 0
  rw [zero_add] at this
  rw [this, show (PowerSeries.coeff n) (PowerSeries.X ^ n * B' p q) = PowerSeries.coeff 0 (B' p q) by
    have := PowerSeries.coeff_X_pow_mul (B' p q) n 0; rwa [zero_add] at this]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]

/-- **Resonance.** If `Ĥ` solves the normal-form recursion and `H₀` solves it at the
nonresonant entries, then `H₀⁻¹ Ĥ` vanishes off the resonant positions `λ_i − λ_j = n`. -/
theorem b65q_resonance (lam : Fin 4 → ℂ) (G H₀ Ĥ : ℕ → Matrix (Fin 4) (Fin 4) ℂ)
    (h0 : H₀ 0 = 1) (hĤ0 : Ĥ 0 = 1)
    (hH₀ : ∀ (n : ℕ) (i j : Fin 4), ((n : ℂ) + lam j - lam i) ≠ 0 → (n : ℂ) * H₀ n i j =
      (diagonal lam * H₀ n - H₀ n * diagonal lam +
        ∑ l ∈ Finset.range n, G l * H₀ (n - 1 - l)) i j)
    (hĤ : ∀ (n : ℕ) (i j : Fin 4), (n : ℂ) * Ĥ n i j = (diagonal lam * Ĥ n - Ĥ n * diagonal lam +
        ∑ l ∈ Finset.range n, G l * Ĥ (n - 1 - l)) i j) :
    ∀ (n : ℕ) (i j : Fin 4), ((n : ℂ) - lam i + lam j) ≠ 0 →
      PowerSeries.coeff n ((b65q_MPS (b65q_seriesInv H₀) * b65q_MPS Ĥ) i j) = 0 := by
  set Y := b65q_MPS H₀
  set Y' := b65q_MPS (b65q_seriesInv H₀)
  set U := Y' * b65q_MPS Ĥ
  have hYY' : Y * Y' = 1 := b65q_MPS_seriesInv H₀ h0
  have hY'Y : Y' * Y = 1 := mul_eq_one_comm.mp hYY'
  have hH : b65q_MPS Ĥ = Y * U := by rw [← mul_assoc, hYY', one_mul]
  have hEH : b65q_defect lam (b65q_MPS G) (b65q_MPS Ĥ) = 0 := by
    ext i j n
    rw [b65q_defect_coeff, hĤ n i j, sub_self]; simp
  have hDU : b65q_D lam U = -(Y' * b65q_defect lam (b65q_MPS G) Y * U) := by
    have := b65q_defect_mul lam (b65q_MPS G) Y U
    rw [← hH, hEH] at this
    have h2 := congrArg (fun M ↦ Y' * M) this
    simp only [mul_zero, mul_add, ← mul_assoc, hY'Y, one_mul] at h2
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2.symm
  have hY'0 : ∀ i p, PowerSeries.coeff 0 (Y' i p) = (1 : Matrix (Fin 4) (Fin 4) ℂ) i p := by
    intro i p; simp [Y', b65q_MPS, b65q_seriesInv, b65q_seriesInvUpTo]
  have hU0 : ∀ q j, PowerSeries.coeff 0 (U q j) = (1 : Matrix (Fin 4) (Fin 4) ℂ) q j := by
    intro q j
    have := congrArg (fun M ↦ PowerSeries.coeff 0 (M q j)) (show U = Y' * b65q_MPS Ĥ from rfl)
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul] at this
    rw [this]
    simp [Y', b65q_MPS, b65q_seriesInv, b65q_seriesInvUpTo, hĤ0, Matrix.one_apply]
  have hE0 : ∀ n, ∀ i j, PowerSeries.coeff n (b65q_defect lam (b65q_MPS G) Y i j) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j
      by_cases hres : ((n : ℂ) + lam j - lam i) = 0
      · have h1 := congrArg (fun M ↦ PowerSeries.coeff n (M i j)) hDU
        simp only [Matrix.neg_apply, map_neg] at h1
        rw [b65q_D_coeff, show (n : ℂ) - lam i + lam j = 0 by linear_combination hres, zero_mul,
          b65q_coeff_triple _ _ _ n ih] at h1
        simp only [hY'0, hU0, Matrix.one_apply] at h1
        simpa [Finset.sum_ite_eq, Finset.sum_ite_eq'] using h1.symm
      · rw [b65q_defect_coeff, hH₀ n i j hres, sub_self]
  intro n i j hn
  have h1 := congrArg (fun M ↦ PowerSeries.coeff n (M i j)) hDU
  have hz : b65q_defect lam (b65q_MPS G) Y = 0 := by ext i j m; rw [hE0 m i j]; simp
  simp only [hz, mul_zero, zero_mul, neg_zero, Matrix.zero_apply, map_zero] at h1
  rw [b65q_D_coeff] at h1
  exact (mul_eq_zero.mp h1).resolve_left hn

end HodgeLean.Foundations.Program
