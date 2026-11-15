import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-! # Definitions for the analytic divisor spec, fourth stage (Weierstrass preparation)

Two plain definitions on `ℂⁿ × ℂ = (Fin n → ℂ) × ℂ` and on `ℂ`: the monic polynomial
`w ^ d + ∑_{j < d} a_j(z) w ^ j` in the last variable with coefficient functions `a_j`, and the
number of zeros, counted with multiplicity, of a one-variable function in an open disc. No
analyticity, vanishing of the coefficients at a point, or finiteness is built in; those are
hypotheses of the statements of `HodgeLean.Foundations.AnalyticDivisorAlgebraic4`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Metric

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic4

/-- The monic polynomial of degree `d` in the last variable `w` with coefficient functions
`a j` of `z ∈ ℂⁿ`: `(z, w) ↦ w ^ d + ∑_{j < d} a_j(z) w ^ j`. When every `a j` is analytic at `0`
and vanishes there, this is a *Weierstrass polynomial* at `0`; those conditions are hypotheses of
the statements, not part of the definition.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B,
Definition 2 (Weierstrass polynomial); Hörmander, *An Introduction to Complex Analysis in Several
Variables*, §6.1. -/
def monicInLast {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (p : (Fin n → ℂ) × ℂ) : ℂ :=
  p.2 ^ d + ∑ j : Fin d, a j p.1 * p.2 ^ (j : ℕ)

example {n : ℕ} (a : Fin 0 → (Fin n → ℂ) → ℂ) (p : (Fin n → ℂ) × ℂ) : monicInLast a p = 1 := by
  simp [monicInLast]

/-- The number of zeros of `g : ℂ → ℂ` in the open disc `ball c r`, counted with multiplicity:
`∑ᶠ a ∈ ball c r, analyticOrderNatAt g a`. A point where `g` is not analytic, or vanishes
identically nearby, contributes `0` (`analyticOrderNatAt` is `0` there), and the finite sum is `0`
when infinitely many terms are nonzero; the statements only use it where `g` is analytic near the
closed disc and nonvanishing on its boundary circle, so that both cases are excluded.

Source: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §5.2 (the argument principle, zeros counted
with their orders); Mathlib's `analyticOrderNatAt`. -/
def zeroCount (g : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ (a : ℂ) (_ : a ∈ ball c r), analyticOrderNatAt g a

example (g : ℂ → ℂ) (c : ℂ) : zeroCount g c 0 = 0 := by
  simp [zeroCount]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic4
