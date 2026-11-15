import HodgeLean.Foundations.Program.PeriodCoordinates
import HodgeLean.Foundations.Program.PeriodFunctionIntegrated

/-! # Frame derivative data
Finite matrix blocks carry the norms; no lattice norm is chosen.
HC no distance; AV milestone no distance.
-/
noncomputable section
open scoped TensorProduct Matrix Topology
open HodgeLean.Papers Filter Set
namespace HodgeLean.Foundations.Program

/-- Directional variation of the matrix graph chart from its two block derivatives.
Source: Griffiths–Harris, Principles of Algebraic Geometry, Ch. 1, §5, graph charts. -/
def b66_graphVariation (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t h : Fin 10 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (fderiv ℂ (fun x => b64_tailBlock (u x)) t h -
    g32m_toMat (b64_graphCoord (u t)) *
      fderiv ℂ (fun x => b64_headBlock (u x)) t h) * (b64_headBlock (u t))⁻¹

example (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice) (t : Fin 10 → ℂ) :
    b66_graphVariation u t 0 = 0 := by
  simp [b66_graphVariation]

/-- Nine by ten coordinate array of block variation in standard input columns.
Source: Mathlib `LinearMap.toMatrix'`; G32 `g32r_PeriodMap.codiff`. -/
def b66_variationMatrix (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t : Fin 10 → ℂ) : Matrix (Fin 9) (Fin 10) ℂ :=
  fun i j => b60c_matrixCoordinates (b66_graphVariation u t (Pi.single j 1)) i

example (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice) (t : Fin 10 → ℂ)
    (i : Fin 9) (j : Fin 10) :
    b66_variationMatrix u t i j =
      b60c_matrixCoordinates (b66_graphVariation u t (Pi.single j 1)) i := rfl

end HodgeLean.Foundations.Program
