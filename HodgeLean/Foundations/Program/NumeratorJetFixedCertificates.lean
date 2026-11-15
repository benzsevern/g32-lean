import HodgeLean.Foundations.Program.NumeratorJetFixedField

/-! # Stored residue arrays in the rational fixed-pole field -/

noncomputable section
open Matrix Polynomial
namespace HodgeLean.Foundations.Program

/-- Stored fixed-pole coefficients extended periodically for natural indexing. -/
def b65e_storedFixedQ (n : ℕ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ :=
  b65e_fixedJet (Fin.ofNat 8 n)

/-- Stored moving-pole coefficients as rational polynomials. -/
def b65e_storedMovingQ (n : ℕ) (e : Fin 2) (i j : Fin 4) : ℚ[X] :=
  ∑ c : Fin 6, C (b65e_movingJet (Fin.ofNat 8 n) e c i j) * X ^ (c : ℕ)

/-- The polynomial encoding evaluates to the frozen residue array through order seven. -/
theorem b65e_storedResidue_eval (p : Fin 12 → ℂ) (n : Fin 8) :
    b65e_polynomialResidue p b65e_storedFixedQ b65e_storedMovingQ n =
      b65e_residueJet p n := by
  funext q i j
  cases q with
  | inl k =>
    simp only [b65e_polynomialResidue, b65e_storedFixedQ, b65e_residueJet,
      Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  | inr x =>
    simp only [b65e_polynomialResidue, b65e_storedMovingQ, b65e_residueJet,
      eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom,
      Fin.ofNat_eq_cast, Fin.cast_val_eq_self, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring


end HodgeLean.Foundations.Program
