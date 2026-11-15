import HodgeLean.Foundations.HermitianForm

/-! # Rational trace data for Hermitian classification

Actual bilinear and quadratic forms over ℚ, with K = ℚ(√−3).
-/

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm

/-- Rational trace pairing, with the factor two of the field trace.
Source: `HermitianForm.reBilin`; Tr_{ℚ(√−3)/ℚ}(z) = 2 re(z). -/
def traceBilin (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) : LinearMap.BilinForm ℚ W :=
  (2 : ℚ) • reBilin h

example : traceBilin (Fin 6 → QuadraticAlgebra ℚ (-3) 0)
    (diagForm ![1, 1, 1, -1, -1, -2]) 0 0 = 0 := by
  simp only [map_zero, LinearMap.zero_apply]

/-- Rational trace quadratic form x ↦ Tr(h(x,x)).
Source: `HermitianForm.hermQuadForm`; Tr_{ℚ(√−3)/ℚ}(z) = 2 re(z). -/
def traceQuad (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) : QuadraticForm ℚ W :=
  (traceBilin W h).toQuadraticMap

example : traceQuad (Fin 6 → QuadraticAlgebra ℚ (-3) 0)
    (diagForm ![1, 1, 1, -1, -1, -2]) 0 = 0 := by
  simp only [QuadraticMap.map_zero]

end HodgeLean.Foundations.HermitianClass
