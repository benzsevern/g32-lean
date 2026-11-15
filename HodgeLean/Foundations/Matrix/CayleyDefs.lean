import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! # Matrix Cayley formula

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.MatrixCayley
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rational matrix Cayley identity.
Source: Weyl, The Classical Groups, Chapter II, §10;
`docs/specs/HeckeSpreading.md`, S1; `Program.hk_cayley`. -/
def cayley {K : Type*} [CommRing K] (X : Matrix n n K) : Matrix n n K :=
  (1 - X) * (1 + X)⁻¹

example {K : Type*} [Field K] : cayley (0 : Matrix n n K) = 1 := by
  simp [cayley]

end HodgeLean.Foundations.MatrixCayley
