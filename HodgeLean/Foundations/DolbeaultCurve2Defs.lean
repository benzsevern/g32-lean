import HodgeLean.Foundations.DolbeaultCurveDefs
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # The Wirtinger derivative `∂/∂z̄` and the Cauchy transform on `ℂ` (FROZEN DEFINITIONS)

The one-variable objects of the `∂̄`-Poincaré lemma: the Wirtinger derivative
`∂f/∂z̄ = (∂f/∂x + i ∂f/∂y) / 2` of a function `f : ℂ → ℂ`, defined through the conjugate-linear part
`antiLinearPart` of its real derivative (as `∂̄` on `X(ℂ)` is in `DolbeaultCurveDefs.lean`), and the
Cauchy transform `T g (z) = (1/π) ∫ g(w) / (z − w) dA(w)` for the Lebesgue measure on `ℂ`.
-/

noncomputable section
open MeasureTheory

namespace HodgeLean.Foundations

/-- The Wirtinger derivative `∂f/∂z̄ (z) = (∂f/∂x + i ∂f/∂y) / 2` of `f : ℂ → ℂ` at `z`: the value at
`1` of the conjugate-linear part of the real derivative of `f` at `z`. With this normalization
`∂z̄/∂z̄ = 1`, and `f` is holomorphic near `z` when it is real-differentiable there with vanishing
Wirtinger derivative.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
North-Holland (1990), §1.1 (the operators `∂/∂z` and `∂/∂z̄`); Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 0 §1. -/
def wirtingerDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  antiLinearPart (fderiv ℝ f z) 1

/-- Constants have zero Wirtinger derivative. -/
example (c z : ℂ) : wirtingerDbar (fun _ => c) z = 0 := by
  simp [wirtingerDbar]

/-- The Cauchy transform `T g (z) = (1/π) ∫ g(w) / (z − w) dA(w)` of `g : ℂ → ℂ`, for the Lebesgue
measure `dA` on `ℂ` (`volume`). For `g` smooth with compact support it solves `∂f/∂z̄ = g`. In
Hörmander's notation this is `(1/2πi) ∫∫ g(w) / (w − z) dw ∧ dw̄`, since `dw ∧ dw̄ = −2i dA`.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.2.2;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the `∂̄`-Poincaré lemma in one
variable). -/
def cauchyTransform (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ w, g w / (z - w)

/-- The Cauchy transform of zero is zero. -/
example (z : ℂ) : cauchyTransform (fun _ => 0) z = 0 := by
  simp [cauchyTransform]

end HodgeLean.Foundations
