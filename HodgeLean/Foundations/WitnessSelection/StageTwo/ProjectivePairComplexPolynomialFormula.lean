import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairComplexPolynomialParts
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Boolean formulas for complex polynomial equations in real polynomial coordinates.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- One complex polynomial equation has an exact Boolean description in real coordinates.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_complex_polynomial_formula {ι : Type*} {n : ℕ}
    (p : MvPolynomial ι ℂ) (r s : ι → MvPolynomial (Fin n) ℝ) :
    ∃ f : s2v_t11b_Formula n, ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ f.realize ↔ MvPolynomial.eval (fun i =>
        (MvPolynomial.eval (fun j => x j) (r i) : ℂ) +
          (MvPolynomial.eval (fun j => x j) (s i) : ℂ) * Complex.I) p = 0 := by
  obtain ⟨R, S, hRS⟩ := s2e_pair_complex_polynomial_parts p r s
  refine ⟨.inter (s2v_t11b_zeroFormula R) (s2v_t11b_zeroFormula S), ?_⟩
  intro x
  change (x ∈ (s2v_t11b_zeroFormula R).realize ∧
    x ∈ (s2v_t11b_zeroFormula S).realize) ↔ _
  rw [s2v_t11b_realize_zeroFormula, s2v_t11b_realize_zeroFormula,
    ← (hRS (fun j => x j)).1, ← (hRS (fun j => x j)).2]
  exact ⟨fun h => Complex.ext h.1 h.2, fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩

end HodgeLean.WitnessSelection.StageTwo
