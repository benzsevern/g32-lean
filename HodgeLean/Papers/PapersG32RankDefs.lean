import HodgeLean.Papers.PapersG32RankData

namespace HodgeLean.Papers

open scoped Polynomial

noncomputable section

/-- The polynomial matrix formed from all thirteen exported jets.
Source: G32 v0.16, Proposition 5.9 and the appendix "The rank certificate". -/
def papers8_Mpoly : Matrix (Fin 9) (Fin 10) ℚ[X] :=
  fun i j => ∑ n : Fin 13, Polynomial.C ((![papers8_M0, papers8_M1, papers8_M2, papers8_M3,
    papers8_M4, papers8_M5, papers8_M6, papers8_M7, papers8_M8, papers8_M9, papers8_M10,
    papers8_M11, papers8_M12] : Fin 13 → Matrix (Fin 9) (Fin 10) ℚ) n i j) *
      Polynomial.X ^ (n : ℕ)

/-- The nine-by-nine polynomial submatrix obtained by omitting column zero.
Source: G32 v0.16, Proposition 5.9. -/
def papers8_A : Matrix (Fin 9) (Fin 9) ℚ[X] :=
  papers8_Mpoly.submatrix id Fin.succ

/-- A rational coefficient matrix of the omitted-column jet.
Source: G32 v0.16, Proposition 5.9 and the exported certificate data. -/
def papers8_Acoeff (n : Fin 8) : Matrix (Fin 9) (Fin 9) ℚ :=
  ((![papers8_M0, papers8_M1, papers8_M2, papers8_M3, papers8_M4, papers8_M5,
    papers8_M6, papers8_M7] : Fin 8 → Matrix (Fin 9) (Fin 10) ℚ) n).submatrix id Fin.succ

/-- Forms a polynomial matrix from eight rational coefficient matrices.
Source: certificate encoding utility for the exported G32 jets. -/
def papers8_polyOfCoeffs (C : Fin 8 → Matrix (Fin 9) (Fin 9) ℚ) :
    Matrix (Fin 9) (Fin 9) ℚ[X] :=
  fun i j => ∑ n : Fin 8, Polynomial.monomial (n : ℕ) (C n i j)

/-- The unit lower-triangular factor of the left elimination transformation.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
def papers8_L : Matrix (Fin 9) (Fin 9) ℚ[X] :=
  papers8_polyOfCoeffs (![papers8_L0, papers8_L1, papers8_L2, papers8_L3,
    papers8_L4, papers8_L5, papers8_L6, papers8_L7])

/-- The determinant-one signed permutation factor of the left elimination transformation.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
def papers8_R : Matrix (Fin 9) (Fin 9) ℚ[X] :=
  papers8_polyOfCoeffs (![papers8_R0, papers8_R1, papers8_R2, papers8_R3,
    papers8_R4, papers8_R5, papers8_R6, papers8_R7])

/-- The left transformation in the determinant-preserving truncated elimination.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
def papers8_P : Matrix (Fin 9) (Fin 9) ℚ[X] := papers8_L * papers8_R

/-- The right transformation in the determinant-preserving truncated elimination.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
def papers8_Q : Matrix (Fin 9) (Fin 9) ℚ[X] :=
  papers8_polyOfCoeffs (![papers8_Q0, papers8_Q1, papers8_Q2, papers8_Q3,
    papers8_Q4, papers8_Q5, papers8_Q6, papers8_Q7])

/-- The diagonal result of the determinant-preserving truncated elimination.
Source: exact elimination of the exported G32 jets by `gen_g32_rank_lean.py`. -/
def papers8_D : Matrix (Fin 9) (Fin 9) ℚ[X] :=
  papers8_polyOfCoeffs (![papers8_D0, papers8_D1, papers8_D2, papers8_D3,
    papers8_D4, papers8_D5, papers8_D6, papers8_D7])

/-- The first eight exported coefficients as rational formal power series.
Source: G32 v0.16, Proposition 5.9 and the exported certificate data. -/
def papers8_Mseries : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ) :=
  fun i j => ∑ n : Fin 8, PowerSeries.monomial (n : ℕ)
    ((![papers8_M0, papers8_M1, papers8_M2, papers8_M3, papers8_M4, papers8_M5,
      papers8_M6, papers8_M7] : Fin 8 → Matrix (Fin 9) (Fin 10) ℚ) n i j)

end

end HodgeLean.Papers
