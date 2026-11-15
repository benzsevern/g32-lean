import HodgeLean.Foundations.Program.G32Native.PairedConormalLinearFormCoefficients
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The literal homogeneous coefficient matrix of the relation -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open MvPolynomial Matrix
namespace HodgeLean.Foundations.Program.G32Native

/-- The relation matrix with exact first row X₀ and the original variable coefficients of every other row. -/
def conormalRelationMatrix {K : Type*} [CommRing K] (k : ℕ)
    (p : Fin k → homogeneousSubmodule (Fin (k + 1)) K 1) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) K :=
  Matrix.of fun i => Fin.cases (Pi.single 0 1)
    (fun t => conormalLinearFormCoefficient k (p t)) i

/-- The actual first coefficient row evaluates to exactly the distinguished homogeneous coordinate. -/
theorem conormal_relation_matrix_mulVec_zero {K : Type*} [CommRing K] (k : ℕ)
    (p : Fin k → homogeneousSubmodule (Fin (k + 1)) K 1) (v : Fin (k + 1) → K) :
    (conormalRelationMatrix k p).mulVec v 0 = v 0 := by
  change (Pi.single 0 (1 : K) : Fin (k + 1) → K) ⬝ᵥ v = v 0
  rw [single_dotProduct, one_mul]

/-- Every successor coefficient row evaluates to the same original homogeneous polynomial row. -/
theorem conormal_relation_matrix_mulVec_succ {K : Type*} [CommRing K] (k : ℕ)
    (p : Fin k → homogeneousSubmodule (Fin (k + 1)) K 1) (v : Fin (k + 1) → K)
    (t : Fin k) :
    (conormalRelationMatrix k p).mulVec v t.succ = eval v (p t).val := by
  change (∑ j, conormalLinearFormCoefficient k (p t) j * v j) = _
  exact (conormal_linear_form_eval k (p t) v).symm

end HodgeLean.Foundations.Program.G32Native
