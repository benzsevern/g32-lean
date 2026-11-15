import HodgeLean.Papers.PapersG32RankProofs

/-! # The G32 rank certificate (FROZEN SPEC)

This file checks exact data exported from the certificate accompanying G32 v0.16. It does not
identify that data with the codifferential in the paper.
-/

namespace HodgeLean.Papers

open scoped Polynomial

/-- **The constant jet has rank five.** This checks the exact matrix data with a five-row
factorization and a nonsingular five-by-five minor.
Source: G32 v0.16, Proposition 5.9 and the appendix "The rank certificate". -/
theorem papers_g32_rank_constant : papers8_M0.rank = 5 :=
  papers_g32_rank_constant_aux

/-- **The omitted-column minor starts in degree seven with the printed coefficient.**
Checks: G32 v0.16, Proposition 5.9.
Source: G32 v0.16, Proposition 5.9 and the appendix "The rank certificate". -/
theorem papers_g32_minor_order_seven :
    (∀ k < 7, papers8_A.det.coeff k = 0) ∧
      papers8_A.det.coeff 7 =
        -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72 :=
  papers_g32_minor_order_seven_aux

/-- The omitted-column polynomial determinant is nonzero.
Source: G32 v0.16, Proposition 5.9. -/
theorem papers_g32_minor_ne_zero : papers8_A.det ≠ 0 :=
  papers_g32_minor_ne_zero_aux

/-- The exported polynomial matrix has full row rank over the rational-function field.
Source: G32 v0.16, Proposition 5.9. -/
theorem papers_g32_rank_ratFunc :
    (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = 9 :=
  papers_g32_rank_ratFunc_aux

/-- Any rational power-series matrix with the same first eight coefficients has omitted-column
minor of order seven.
Source: G32 v0.16, Proposition 5.9. -/
theorem papers_g32_powerSeries_order
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) = PowerSeries.coeff k (papers8_Mseries i j)) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  papers_g32_powerSeries_order_aux B hB

/-- The complex scalar extension of any matching jet has omitted-column minor of order seven.
Source: G32 v0.16, Proposition 5.9. -/
theorem papers_g32_powerSeries_order_complex
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℂ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) =
        algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j))) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  papers_g32_powerSeries_order_complex_aux B hB

example : PowerSeries.order (papers8_Mseries.submatrix id Fin.succ).det = 7 := by
  apply papers_g32_powerSeries_order papers8_Mseries
  intros
  rfl

example : PowerSeries.order
    ((papers8_Mseries.map (PowerSeries.map (algebraMap ℚ ℂ))).submatrix id Fin.succ).det = 7 := by
  apply papers_g32_powerSeries_order_complex
  intros
  simp

example : papers8_M0.rank ≠ 9 := by
  rw [papers_g32_rank_constant]
  decide

example : papers8_A.det.coeff 0 = 0 := by
  exact papers_g32_minor_order_seven.1 0 (by decide)

example : papers8_A.det ≠ 0 := papers_g32_minor_ne_zero

example : (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = 9 :=
  papers_g32_rank_ratFunc

example : papers_g32_rank_constant = papers_g32_rank_constant := rfl

example : papers_g32_minor_order_seven = papers_g32_minor_order_seven := rfl

example : papers_g32_minor_ne_zero = papers_g32_minor_ne_zero := rfl

example : papers_g32_rank_ratFunc = papers_g32_rank_ratFunc := rfl

example : papers_g32_powerSeries_order = papers_g32_powerSeries_order := rfl

example : papers_g32_powerSeries_order_complex = papers_g32_powerSeries_order_complex := rfl

example : papers8_Mpoly = papers8_Mpoly := rfl
example : papers8_A = papers8_A := rfl
example : papers8_Acoeff = papers8_Acoeff := rfl
example : papers8_polyOfCoeffs = papers8_polyOfCoeffs := rfl
example : papers8_L = papers8_L := rfl
example : papers8_R = papers8_R := rfl
example : papers8_P = papers8_P := rfl
example : papers8_Q = papers8_Q := rfl
example : papers8_D = papers8_D := rfl
example : papers8_Mseries = papers8_Mseries := rfl

example : ¬ PowerSeries.order
    ((0 : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ)).submatrix id Fin.succ).det = 7 := by
  simp

example (A : Matrix (Fin 1) (Fin 1) ℚ[X]) :
    ∀ k : ℕ, k ≤ 7 →
      A.det.coeff k = (∏ i : Fin 1, A i i).coeff k := by
  intro k hk
  simpa using papers8_triangular_bridge_aux (1 : Matrix (Fin 1) (Fin 1) ℚ[X]) A 1 A 7
    (by simp) (by simp) (by simp) (by simp) k hk

example : ∀ k : ℕ, k ≤ 7 →
    (1 : Matrix (Fin 2) (Fin 2) ℚ[X]).det.coeff k =
      (∏ i : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℚ[X]) i i).coeff k := by
  intro k hk
  simpa using papers8_triangular_bridge_aux
    (1 : Matrix (Fin 2) (Fin 2) ℚ[X]) (1 : Matrix (Fin 2) (Fin 2) ℚ[X])
    (1 : Matrix (Fin 2) (Fin 2) ℚ[X]) (1 : Matrix (Fin 2) (Fin 2) ℚ[X]) 7
    (by simp) (by simp) (by simp) (by simp) k hk

end HodgeLean.Papers
