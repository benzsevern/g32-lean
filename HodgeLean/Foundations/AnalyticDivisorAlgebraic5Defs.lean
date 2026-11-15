import HodgeLean.Foundations.AnalyticDivisorAlgebraic4Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Analytic.Basic

/-! # Definitions for the analytic divisor spec, fifth stage (germs and reduced equations)

Three plain definitions on `ℂⁿ × ℂ = (Fin n → ℂ) × ℂ`: the polynomial in `w` obtained by freezing
`z` in `monicInLast a (z, w) = w ^ d + ∑_{j < d} a_j(z) w ^ j`, its discriminant as a function of
`z` (Mathlib's `Polynomial.discr`), and square-freeness of a function at a point (no factorization
`g ^ 2 * h` with `g` analytic and vanishing at the point, `h` analytic). No analyticity of the
coefficients and no vanishing at a point is built in; those are hypotheses of the statements of
`HodgeLean.Foundations.AnalyticDivisorAlgebraic5`. HC no distance; AV milestone no distance.
-/

noncomputable section

open Filter Topology Polynomial

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic5

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4

/-- The polynomial `X ^ d + ∑_{j < d} a_j(z) X ^ j ∈ ℂ[X]` at a fixed `z ∈ ℂⁿ`: evaluation at `w`
gives `monicInLast a (z, w)`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B,
Definition 2 (Weierstrass polynomial, viewed in `ℂ{z}[w]`); Mathlib's `Polynomial`. -/
def monicPoly {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ[X] :=
  X ^ d + ∑ j : Fin d, C (a j z) * X ^ (j : ℕ)

example {n : ℕ} (a : Fin 0 → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : monicPoly a z = 1 := by
  simp [monicPoly]

/-- The discriminant of the monic polynomial `monicPoly a z`, as a function of `z`. It vanishes
exactly when `w ↦ monicInLast a (z, w)` has a multiple root; its zero set is the discriminant
locus of the Weierstrass polynomial.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A (the
discriminant of a Weierstrass polynomial); Lang, *Algebra*, rev. 3rd ed., Ch. IV, §6
(discriminant); Mathlib's `Polynomial.discr`. -/
def weierstrassDiscr {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  (monicPoly a z).discr

example {n : ℕ} (a : Fin 0 → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : weierstrassDiscr a z = 1 := by
  have h : monicPoly a z = C 1 := by simp [monicPoly]
  rw [weierstrassDiscr, h, discr_C]

/-- `f` is *square-free at `y`*: there is no factorization `f = g ^ 2 * h` near `y` with `g` and
`h` analytic at `y` and `g y = 0`. For `f` analytic at `y` this says that the germ of `f` at `y`
has no repeated non-unit factor; a locally zero `f` is not square-free (take `g = 0`).

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B (unique
factorization of germs) and Ch. III, §A (reduced Weierstrass polynomials); Chirka, *Complex
Analytic Sets*, §2.3 (reduced local equation of a hypersurface). -/
def IsSquareFreeAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (y : E) :
    Prop :=
  ∀ g h : E → ℂ, AnalyticAt ℂ g y → AnalyticAt ℂ h y → g y = 0 →
    ¬ f =ᶠ[𝓝 y] fun p => g p ^ 2 * h p

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (y : E) :
    IsSquareFreeAt (fun _ : E => (1 : ℂ)) y := by
  intro g h _ _ hg0 H
  have := H.self_of_nhds
  simp [hg0] at this

end HodgeLean.Foundations.AnalyticDivisorAlgebraic5
