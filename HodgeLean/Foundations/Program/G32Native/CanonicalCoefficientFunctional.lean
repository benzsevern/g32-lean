import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs

/-! # Scalar functionals in the retained Abel coefficient space -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Literal evaluation against one retained original form coefficient vector. -/
def canonicalCoefficientFunctional (G : CanonicalAbelGeometry) (a : Fin (G.k + 1) → ℂ) :
    (Fin (G.k + 1) → ℂ) →L[ℂ] ℂ :=
  ((Module.Dual.eval ℂ (Fin (G.k + 1) → ℂ) a).comp (coefficientDual G.k)).toContinuousLinearMap

/-- The scalar functional retains the exact ordered coefficient pairing. -/
theorem canonicalCoefficientFunctional_apply (G : CanonicalAbelGeometry)
    (a v : Fin (G.k + 1) → ℂ) :
    canonicalCoefficientFunctional G a v = coefficientDual G.k v a := rfl

/-- An annihilating original covector gives a zero scalar derivative of the original Abel lift. -/
theorem canonical_covector_scalar_derivative_zero (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q) (a : Fin (G.k + 1) → ℂ)
    (hF : DifferentiableAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hzero : ∀ v, canonicalAbelDifferential G F x v a = 0) :
    fderiv ℂ (canonicalCoefficientFunctional G a ∘ F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)) = 0 := by
  rw [fderiv_comp _ (canonicalCoefficientFunctional G a).differentiableAt hF]
  simp only [ContinuousLinearMap.fderiv]
  ext v
  exact hzero v

#print axioms canonicalCoefficientFunctional
#print axioms canonicalCoefficientFunctional_apply
#print axioms canonical_covector_scalar_derivative_zero
end HodgeLean.Foundations.Program.G32Native
