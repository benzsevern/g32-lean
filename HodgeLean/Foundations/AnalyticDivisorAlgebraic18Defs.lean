import HodgeLean.Foundations.AnalyticDivisorAlgebraic17

/-! # Hypersurface Nullstellensatz: concrete equations

These functions are data used by the stage-eighteen checks.  None packages a frozen proposition.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic18

/-- The first coordinate on `ℂ²`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, I.A, §2. -/
def gaga18_axis (z : Fin 2 → ℂ) : ℂ := z 0

/-- The normal-crossing equation on `ℂ²`.
Source: Gunning--Rossi, II.E, examples following Definition 1. -/
def gaga18_crossing (z : Fin 2 → ℂ) : ℂ := z 0 * z 1

/-- The irreducible cusp equation on `ℂ²`.
Source: Gunning--Rossi, III.A, examples following Theorem 1. -/
def gaga18_cusp (z : Fin 2 → ℂ) : ℂ := z 1 ^ 2 - z 0 ^ 3

/-- A node equation which factors analytically at the origin.
Source: Gunning--Rossi, II.B, Theorem 2 (Weierstrass preparation). -/
def gaga18_node (z : Fin 2 → ℂ) : ℂ := z 1 ^ 2 - z 0 ^ 2 * (1 + z 0)

/-- A concrete analytic unit at the origin.
Source: Gunning--Rossi, II.A, local-ring units. -/
def gaga18_unit (z : Fin 2 → ℂ) : ℂ := 1 + z 0

example (z : Fin 2 → ℂ) : gaga18_axis z = z 0 := rfl
example (z : Fin 2 → ℂ) : gaga18_crossing z = z 0 * z 1 := rfl
example (z : Fin 2 → ℂ) : gaga18_cusp z = z 1 ^ 2 - z 0 ^ 3 := rfl
example (z : Fin 2 → ℂ) : gaga18_node z = z 1 ^ 2 - z 0 ^ 2 * (1 + z 0) := rfl
example : gaga18_unit 0 = 1 := by simp [gaga18_unit]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic18
