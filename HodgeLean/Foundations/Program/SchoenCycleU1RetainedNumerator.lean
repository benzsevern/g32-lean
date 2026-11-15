import HodgeLean.Foundations.Program.SchoenCycleU1RegularPolynomialNumerator
import HodgeLean.Foundations.Program.SchoenCycleU1DivisorEvaluation

/-! # Actual retained root polynomials in analytic numerators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Along an actual retained quotient point, the regular polynomial numerator
is exactly the coordinate root product, with every tuple multiplicity retained.
Source: Hartshorne, Algebraic Geometry, II.2, evaluation and pullback of sections;
ACGH, Geometry of Algebraic Curves I, Chapter I, divisor coordinates. -/
theorem s2e_u1_regularPolynomialNumerator_retained_tuple
    (Z B : Over (Spec ↧ℂ)) (N : ℕ) (γ : g3_power Z N ⟶ B)
    (U : Z.left.Opens) (V : B.left.Opens)
    (hVU : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (s : Γ(Z.left, U))
    (Q : Polynomial Γ(B.left, V))
    (hQ : Q.map (γ.left.app V).hom = ∏ i : Fin N,
      (Polynomial.X - Polynomial.C (s2e_u1_coordinateSection Z B N γ U V hVU s i)))
    (b : ℂ → ComplexPoint B) (g : ℂ → ℂ) (t z : ℂ)
    (ht : (b t).underlying ∈ V) (x : Fin N → ComplexPoint Z)
    (hbt : b t = Point.map γ (s2_lift N x)) :
    s2e_u1_regularPolynomialNumerator B V Q b g (t, z) =
      (∏ i : Fin N, (Polynomial.X - Polynomial.C (Point.evaluate U s (x i)))).eval (g z) := by
  letI := s2e_step1_sectionAlgebra B V
  have hx : (Point.map γ (s2_lift N x)).underlying ∈ V := by rwa [← hbt]
  have hv := s2e_u1_retained_divisor_polynomial_evaluation Z B N γ U V hVU s Q hQ
    (s2_lift N x) hx
  have hproj (i : Fin N) : Point.map (g3_proj Z N i) (s2_lift N x) = x i := by
    simp only [Point.map, s2_check_lift_proj]
  simp only [hproj] at hv
  have hpoly : (Q.map (s2e_step1_pointEvaluation B V (b t)
      (s2e_step1_point_preimage B (b t) V ht)).toRingHom) =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C (Point.evaluate U s (x i))) := by
    simpa only [← hbt] using hv
  rw [s2e_u1_regularPolynomialNumerator_evaluation B V Q b g t z ht, hpoly]

end HodgeLean.Foundations.Program
