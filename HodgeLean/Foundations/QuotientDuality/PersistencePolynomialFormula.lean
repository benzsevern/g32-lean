import HodgeLean.Foundations.Program.SchoenTowerT11bRefinement

/-! Literal Boolean formulas for finite real polynomial equations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The equation p = 0 expressed by its two nonnegative polynomial inequalities. -/
def persistencePolynomialEquationFormula {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    s2v_t11b_Formula n := .inter (.nonneg p) (.nonneg (-p))

lemma persistence_polynomial_equation_formula_mem {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (persistencePolynomialEquationFormula p).realize ↔ MvPolynomial.eval x p = 0 := by
  change (0 ≤ MvPolynomial.eval x p ∧ 0 ≤ MvPolynomial.eval x (-p)) ↔ _
  rw [map_neg, neg_nonneg]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by rw [h]; exact ⟨le_rfl, le_rfl⟩⟩

/-- The literal finite conjunction of the given polynomial equations. -/
def persistenceFiniteEquationFormula {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) :
    s2v_t11b_Formula n :=
  s2v_t11b_Formula.conjunction
    (Finset.univ.toList.map (fun j => persistencePolynomialEquationFormula (p j)))

lemma persistence_finite_equation_formula_mem {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (persistenceFiniteEquationFormula p).realize ↔ ∀ j, MvPolynomial.eval x (p j) = 0 := by
  rw [persistenceFiniteEquationFormula, s2v_t11b_realize_conjunction]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, persistence_polynomial_equation_formula_mem]

lemma persistence_finite_equation_formula_isClosed {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℝ) :
    IsClosed (persistenceFiniteEquationFormula p).realize := by
  have heq : (persistenceFiniteEquationFormula p).realize =
      ⋂ j, (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval x (p j)) ⁻¹' {0} := by
    ext x
    simp only [persistence_finite_equation_formula_mem, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_singleton.preimage
    ((p j).continuous_eval.comp (EuclideanSpace.equiv (Fin n) ℝ).continuous)

end HodgeLean.Foundations.QuotientDuality
