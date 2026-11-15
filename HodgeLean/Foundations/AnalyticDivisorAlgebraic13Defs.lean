import HodgeLean.Foundations.AnalyticDivisorAlgebraic12

/-! # Definitions for re-centred Weierstrass preparation

This file supplies coordinate notation used by the stage-thirteen statements. The preparation
and clean-locus assertions remain theorems. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic13

/-- The first `n` coordinates of a point in `n+1` variables.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 2. -/
def gaga13_basePoint {n : ℕ} (p : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun j ↦ p j.castSucc

example (p : Fin 1 → ℂ) : gaga13_basePoint p = (0 : Fin 0 → ℂ) := by
  funext j
  exact Fin.elim0 j

end HodgeLean.Foundations.AnalyticDivisorAlgebraic13
