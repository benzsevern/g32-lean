module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Weighted coefficient operations for convergent division
These are coefficient operations, with convergence specified by explicit summability.
HC no distance; AV milestone no distance.
-/
public section
noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Monomial weight on a polydisc with specified radii.
Source: Serre, GAGA, §1, no. 4, printed p. 6; coefficient majorants. -/
def s2e_divWeight (d : ℕ) (r : Fin (d + 1) → ℝ) (a : Fin (d + 1) →₀ ℕ) : ℝ :=
  ∏ i, r i ^ a i
example (d : ℕ) (r : Fin (d + 1) → ℝ) : s2e_divWeight d r 0 = 1 := by
  simp [s2e_divWeight]

/-- Weighted absolute coefficient sum, used only with summability inputs.
Source: Serre, GAGA, §1, no. 4, printed p. 6; coefficient majorants. -/
def s2e_divNorm (d : ℕ) (r : Fin (d + 1) → ℝ)
    (f : MvPowerSeries (Fin (d + 1)) ℂ) : ℝ :=
  ∑' a, ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a
example (d : ℕ) (r : Fin (d + 1) → ℝ) : s2e_divNorm d r 0 = 0 := by
  simp [s2e_divNorm]

/-- Division by a pure power of the last variable, discarding the lower terms.
Source: Serre, GAGA, §1, no. 4, printed p. 6; convergent division construction. -/
def s2e_divShift (d k : ℕ) (f : MvPowerSeries (Fin (d + 1)) ℂ) :
    MvPowerSeries (Fin (d + 1)) ℂ :=
  fun a => MvPowerSeries.coeff (a + Finsupp.single (Fin.last d) k) f
example (d k : ℕ) : s2e_divShift d k 0 = 0 := rfl

/-- The terms below the divisor degree in the last variable.
Source: Serre, GAGA, §1, no. 4, printed p. 6; convergent division construction. -/
def s2e_divRemainder (d k : ℕ) (f : MvPowerSeries (Fin (d + 1)) ℂ) :
    MvPowerSeries (Fin (d + 1)) ℂ :=
  fun a => if a (Fin.last d) < k then MvPowerSeries.coeff a f else 0
example (d : ℕ) (f : MvPowerSeries (Fin (d + 1)) ℂ) :
    s2e_divRemainder d 0 f = 0 := by
  funext a
  simp [s2e_divRemainder]
  rfl

/-- Error iteration for division by the last-variable power plus an error series.
Source: Serre, GAGA, §1, no. 4, printed p. 6; geometric-series division. -/
def s2e_divError (d k : ℕ) (e f : MvPowerSeries (Fin (d + 1)) ℂ) :
    MvPowerSeries (Fin (d + 1)) ℂ := -(e * s2e_divShift d k f)
example (d k : ℕ) (f : MvPowerSeries (Fin (d + 1)) ℂ) :
    s2e_divError d k 0 f = 0 := by
  simp [s2e_divError]

end HodgeLean.Foundations.Program
