import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelModel
import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation

/-! # The specified ordered real coordinates of the normal conjugation map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The even real coordinate is the real part of the specified complex coordinate. -/
theorem normalRealCoordinates_even (k : ℕ) (z : Fin k → ℂ) (j : Fin k) :
    Complex.piCoordCLE k z (finProdFinEquiv (j, (0 : Fin 2))) = (z j).re := by
  change (Complex.piBasisOneI k).repr z (finProdFinEquiv (j, (0 : Fin 2))) = _
  simp [Complex.piBasisOneI, Module.Basis.smulTower'_repr, Complex.coe_basisOneI_repr]

#print axioms normalRealCoordinates_even

/-- The odd real coordinate is the imaginary part of the specified complex coordinate. -/
theorem normalRealCoordinates_odd (k : ℕ) (z : Fin k → ℂ) (j : Fin k) :
    Complex.piCoordCLE k z (finProdFinEquiv (j, (1 : Fin 2))) = (z j).im := by
  change (Complex.piBasisOneI k).repr z (finProdFinEquiv (j, (1 : Fin 2))) = _
  simp [Complex.piBasisOneI, Module.Basis.smulTower'_repr, Complex.coe_basisOneI_repr]

#print axioms normalRealCoordinates_odd

/-- Multiplying conjugation by `I` exchanges the two specified real coordinates in every complex coordinate. -/
theorem normalRealCoordinates_rotated_conjugation (k : ℕ) (z : Fin k → ℂ)
    (j : Fin k) (r : Fin 2) :
    Complex.piCoordCLE k (fun a => Complex.I * normalConjugation k z a)
        (finProdFinEquiv (j, r)) =
      Complex.piCoordCLE k z (finProdFinEquiv (j, Equiv.swap (0 : Fin 2) 1 r)) := by
  fin_cases r <;> simp [normalRealCoordinates_even, normalRealCoordinates_odd,
    normalConjugation, Complex.mul_re, Complex.mul_im]

#print axioms normalRealCoordinates_rotated_conjugation
end HodgeLean.Foundations.Program.G32Native.EulerModel
