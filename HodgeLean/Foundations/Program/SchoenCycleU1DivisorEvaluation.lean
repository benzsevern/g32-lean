import HodgeLean.Foundations.Program.SchoenCycleU1DivisorCoordinates
import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation

/-! # Evaluation of retained divisor polynomials -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A descended polynomial evaluates to the polynomial of the actual ordered
curve coordinates, with every repeated factor retained.
Source: Hartshorne, Algebraic Geometry, II.2, evaluation and pullback of sections;
ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric divisor coordinates. -/
theorem s2e_u1_retained_divisor_polynomial_evaluation
    (Z B : Over (Spec ↧ℂ)) (N : ℕ) (γ : g3_power Z N ⟶ B)
    (U : Z.left.Opens) (V : B.left.Opens)
    (hVU : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (t : Γ(Z.left, U))
    (Q : Polynomial Γ(B.left, V))
    (hQ : Q.map (γ.left.app V).hom = ∏ i : Fin N,
      (Polynomial.X - Polynomial.C (s2e_u1_coordinateSection Z B N γ U V hVU t i)))
    (x : ComplexPoint (g3_power Z N)) (hx : (Point.map γ x).underlying ∈ V) :
    letI := s2e_step1_sectionAlgebra B V
    Q.map (s2e_step1_pointEvaluation B V (Point.map γ x)
      (s2e_step1_point_preimage B (Point.map γ x) V hx)).toRingHom =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C
        (Point.evaluate U t (Point.map (g3_proj Z N i) x))) := by
  letI := s2e_step1_sectionAlgebra B V
  letI := s2e_step1_sectionAlgebra (g3_power Z N) (γ.left ⁻¹ᵁ V)
  have hx' : x.underlying ∈ γ.left ⁻¹ᵁ V := hx
  let e := s2e_step1_pointEvaluation (g3_power Z N) (γ.left ⁻¹ᵁ V) x
    (s2e_step1_point_preimage _ x _ hx')
  have he : e.toRingHom.comp (γ.left.app V).hom =
      (s2e_step1_pointEvaluation B V (Point.map γ x)
        (s2e_step1_point_preimage B (Point.map γ x) V hx)).toRingHom := by
    ext s
    change s2e_step1_pointEvaluation _ _ _ _ ((γ.left.app V).hom s) =
      s2e_step1_pointEvaluation _ _ _ _ s
    rw [s2e_u1_pointEvaluation_eq_evaluate _ _ _ hx',
      s2e_u1_pointEvaluation_eq_evaluate _ _ _ hx, Point.evaluate_map]
  rw [← he, ← Polynomial.map_map, hQ]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  change s2e_step1_pointEvaluation _ _ _ _
    (s2e_u1_coordinateSection Z B N γ U V hVU t i) = _
  rw [s2e_u1_pointEvaluation_eq_evaluate _ _ _ hx']
  unfold s2e_u1_coordinateSection
  rw [Point.evaluate_map]
  exact (Point.evaluate_res (show γ.left ⁻¹ᵁ V ≤
      (g3_proj Z N i).left ⁻¹ᵁ U from fun y hy =>
        (s2e_u1_mem_powerOpen Z N U y).mp (hVU hy) i)
    ((g3_proj Z N i).left.app U t) x hx').symm

end HodgeLean.Foundations.Program
