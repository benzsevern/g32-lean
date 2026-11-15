import HodgeLean.Foundations.DolbeaultCurve2
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

/-! # Coordinate operators for several-variable ∂̄

Forms are families `Fin n → (Fin n → ℂ) → ℂ`. Closedness is always an explicit
coordinate identity in theorem binders. No solvability predicate is introduced.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations

/-- The conjugate coordinate derivative, with normalization ∂z̄/∂z̄ = 1.
Source: Hörmander, *An Introduction to Complex Analysis in Several Variables*,
3rd ed., §1.1 (Wirtinger operators). -/
def dbar_coord (n : ℕ) (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) +
    Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2

example (n : ℕ) (j : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    dbar_coord n j (fun _ ↦ c) z = 0 := by simp [dbar_coord]

/-- The Cauchy transform in one coordinate, leaving the other coordinates as parameters.
Source: Hörmander, 3rd ed., Theorem 1.2.2 and §2.3; the existing `cauchyTransform`.
-/
def dbar_transform (n : ℕ) (j : Fin n) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ℂ :=
  cauchyTransform (fun w ↦ f (Function.update z j w)) (z j)

example (n : ℕ) (j : Fin n) (z : Fin n → ℂ) :
    dbar_transform n j (fun _ ↦ 0) z = 0 := by
  simp [dbar_transform, cauchyTransform]

/-- Choose the chart anchored at the evaluation point to define the glued coefficients.
Compatibility is a separate assertion; the formula itself is defined for arbitrary functions.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Chapter VIII,
the Dolbeault construction of Cousin I. -/
def dbar_glued (n : ℕ) (c : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (j : Fin n) (z : Fin n → ℂ) : ℂ := dbar_coord n j (c z) z

example (n : ℕ) (j : Fin n) (z : Fin n → ℂ) :
    dbar_glued n (fun _ _ ↦ 0) j z = 0 := by simp [dbar_glued, dbar_coord]

end HodgeLean.Foundations
