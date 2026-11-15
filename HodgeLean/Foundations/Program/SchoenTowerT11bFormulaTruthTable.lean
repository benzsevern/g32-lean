import HodgeLean.Foundations.Program.SchoenTowerT11bActiveBooleanCharts

/-! Finite truth-table presentations of actual Boolean polynomial formulas.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every actual Boolean polynomial formula is evaluated by a finite polynomial list and a Boolean truth table.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite atom presentation step. -/
theorem s2v_t11b_formula_truth_table {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ Q : Fin k → MvPolynomial (Fin n) ℝ, ∃ C : (Fin k → Bool) → Bool,
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ f.realize ↔
        C (fun i => decide (0 ≤ MvPolynomial.eval (fun v => x v) (Q i))) = true := by
  classical
  induction f with
  | nonneg q =>
    refine ⟨1, fun _ => q, fun b => b 0, ?_⟩
    intro x
    simp [s2v_t11b_Formula.realize]
  | compl f ih =>
    obtain ⟨k, Q, C, h⟩ := ih
    refine ⟨k, Q, fun b => !(C b), ?_⟩
    intro x
    change (¬x ∈ f.realize) ↔ _
    rw [h x]
    cases hC : C (fun i => decide (0 ≤ MvPolynomial.eval (fun v => x v) (Q i))) <;> simp [hC]
  | inter f g ihf ihg =>
    obtain ⟨k, Q, C, hQ⟩ := ihf
    obtain ⟨l, R, D, hR⟩ := ihg
    refine ⟨k + l, Fin.addCases Q R,
      fun b => C (fun i => b (i.castAdd l)) && D (fun i => b (i.natAdd k)), ?_⟩
    intro x
    change (x ∈ f.realize ∧ x ∈ g.realize) ↔ _
    simp only [hQ x, hR x, Fin.addCases_left, Fin.addCases_right, Bool.and_eq_true]

end HodgeLean.Foundations.Program
