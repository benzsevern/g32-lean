import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Tactic

/-! # Integral diagonal data for rational isotropy

The definitions contain coefficient data and quadratic maps.
-/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

/-- The rational quadratic form with the supplied integer diagonal coefficients.
Source: Serre, *A Course in Arithmetic*, Chapter IV, §1.1 (diagonal forms). -/
def integralDiagonal (n : ℕ) (a : Fin n → ℤ) : QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ (fun i => (a i : ℚ))

example : integralDiagonal 2 ![1, -1] ![2, 3] = -5 := by
  norm_num [integralDiagonal, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]

end HodgeLean.Foundations.MeyerRational
