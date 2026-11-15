import HodgeLean.Foundations.Program.UniversalFamilyB60cProjection
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsotropic

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- Flatten a three-by-three matrix to the fixed nine period coordinates. -/
def b60c_matrixCoordinates (A : Matrix (Fin 3) (Fin 3) ℂ) : Fin 9 → ℂ :=
  fun k => A ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).1
    ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k).2

/-- Flattening uses exactly the coordinate convention of the period domain. -/
theorem b60c_toMat_matrixCoordinates (A : Matrix (Fin 3) (Fin 3) ℂ) :
    g32m_toMat (b60c_matrixCoordinates A) = A := by
  ext i j
  simp [b60c_matrixCoordinates, g32m_toMat]

#print axioms b60c_toMat_matrixCoordinates

end HodgeLean.Foundations.Program
