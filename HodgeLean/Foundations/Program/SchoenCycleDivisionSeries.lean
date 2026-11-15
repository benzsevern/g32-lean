module

public import HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Monomial realization of coefficient data -/
public section
noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program
/-- Monomial sum of a coefficient family; convergence is a separate input.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Chapter II, §B. -/
def s2e_divSeries (d : ℕ) (F : MvPowerSeries (Fin d) ℂ) (z : Fin d → ℂ) : ℂ :=
  ∑' a, MvPowerSeries.coeff a F * ∏ i, z i ^ a i
example (d : ℕ) : s2e_divSeries d 0 = 0 := by
  funext z
  simp [s2e_divSeries]
end HodgeLean.Foundations.Program
