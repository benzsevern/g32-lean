import HodgeLean.Foundations.QuotientDuality.PersistencePolynomialFormula
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.RealCoordinates

/-! Boolean carriers for the actual finite complex polynomial equations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Foundations.Program HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_complex_equation_formula {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ f : s2v_t11b_Formula (n + n), IsClosed f.realize ∧
      ∀ z : Fin n → ℂ, z ∈ zeroSet p ↔ complexEuclideanCoordinates n z ∈ f.realize := by
  obtain ⟨a, b, hab⟩ := real_equations_in_euclidean_coordinates p
  refine ⟨.inter (persistenceFiniteEquationFormula a) (persistenceFiniteEquationFormula b),
    (persistence_finite_equation_formula_isClosed a).inter
      (persistence_finite_equation_formula_isClosed b), ?_⟩
  intro z
  change z ∈ zeroSet p ↔ _ ∧ _
  rw [persistence_finite_equation_formula_mem, persistence_finite_equation_formula_mem]
  exact hab z

end HodgeLean.Foundations.QuotientDuality
