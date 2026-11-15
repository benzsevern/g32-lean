import HodgeLean.Foundations.HermitianClass
import HodgeLean.Foundations.MeyerRationalS9

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm

/-- Rational trace isotropy supplies Hermitian isotropy on the same vector.
Source: Serre, *A Course in Arithmetic*, Chapter IV, p. 43, Corollary 2. -/
theorem hermClass_isotropic (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional ℚ W] [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hrank : 3 ≤ Module.finrank (QuadraticAlgebra ℚ (-3) 0) W)
    (hp : ∃ x, 0 < traceQuad W h x) (hm : ∃ x, traceQuad W h x < 0) :
    ∃ x, x ≠ 0 ∧ h x x = 0 := by
  have htrace := hermClass_trace_regular W h hh hn
  have hdim : 5 ≤ Module.finrank ℚ W := by
    rw [← Module.finrank_mul_finrank ℚ (QuadraticAlgebra ℚ (-3) 0) W,
      QuadraticAlgebra.finrank_eq_two]
    omega
  have hassoc : (traceQuad W h).associated.SeparatingLeft := by
    have heq : (traceQuad W h).associated = traceBilin W h := by
      exact QuadraticMap.associated_left_inverse ℚ htrace.1.eq
    rw [heq]
    exact htrace.2.1
  obtain ⟨x, hx, hqx⟩ := meyer_isotropic W (traceQuad W h) hassoc hdim hp hm
  exact ⟨x, hx, (hermClass_trace_zero W h hh x).1 hqx⟩

#print axioms hermClass_isotropic

end HodgeLean.Foundations.HermitianClass
