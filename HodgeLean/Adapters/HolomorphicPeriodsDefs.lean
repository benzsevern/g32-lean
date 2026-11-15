import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Convex.PathConnected

/-! # A non-closed real `1`-form on `ℂ` and two paths with the same endpoints

The data of the falsification check of `HodgeLean.Adapters.HolomorphicPeriods`: the real `1`-form
`x dy` on `ℂ = ℝ²`, which is not closed, and the two staircase paths from `0` to `1 + i`, through
`1` and through `i`. They are homotopic (as all paths in `ℂ` with the same endpoints are), but the
integrals of `x dy` along them differ.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Adapters

/-- The real `1`-form `x dy` on `ℂ`, with complex values: `v ↦ (re z) · (im v)` at `z`.
Source: Spivak, *Calculus on Manifolds*, Ch. 4 (`x dy`, the standard non-closed form on `ℝ²`,
`d(x dy) = dx ∧ dy`). -/
def reDImForm (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (z.re : ℂ) • (Complex.ofRealCLM.comp Complex.imCLM)

example (z v : ℂ) : reDImForm z v = (z.re : ℂ) * (v.im : ℂ) := rfl

/-- The staircase path from `0` to `1 + i` through `1`: the segment `[0, 1]`, then `[1, 1 + i]`.
Source: Mathlib's `Path.segment` and `Path.trans`. -/
def rightUpPath : Path (0 : ℂ) (1 + Complex.I) :=
  (Path.segment (0 : ℂ) 1).trans (Path.segment (1 : ℂ) (1 + Complex.I))

example : rightUpPath = (Path.segment (0 : ℂ) 1).trans (Path.segment (1 : ℂ) (1 + Complex.I)) :=
  rfl

/-- The staircase path from `0` to `1 + i` through `i`: the segment `[0, i]`, then `[i, 1 + i]`.
Source: Mathlib's `Path.segment` and `Path.trans`. -/
def upRightPath : Path (0 : ℂ) (1 + Complex.I) :=
  (Path.segment (0 : ℂ) Complex.I).trans (Path.segment Complex.I (1 + Complex.I))

example : upRightPath =
    (Path.segment (0 : ℂ) Complex.I).trans (Path.segment Complex.I (1 + Complex.I)) := rfl

end HodgeLean.Adapters
