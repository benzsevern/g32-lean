import HodgeLean.Foundations.Program.SchoenTowerT11bBoundary

/-! Boolean coordinate transport retains the exact transformed polynomial atom family. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_formula_transport {n : ℕ}
    (T : MvPolynomial (Fin n) ℝ ≃ₐ[ℝ] MvPolynomial (Fin n) ℝ)
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hh : ∀ x p, MvPolynomial.eval (fun i => h x i) p =
      MvPolynomial.eval (fun i => x i) (T p))
    (f : s2v_t11b_Formula n) :
    ∃ g : s2v_t11b_Formula n, g.realize = h ⁻¹' f.realize ∧
      g.atoms = f.atoms.image T := by
  classical
  induction f with
  | nonneg p =>
    refine ⟨.nonneg (T p), ?_, ?_⟩
    · ext x
      change (0 ≤ MvPolynomial.eval (fun i => x i) (T p)) ↔
        (0 ≤ MvPolynomial.eval (fun i => h x i) p)
      rw [hh]
    · simp only [s2v_t11b_Formula.atoms, Finset.image_singleton]
  | compl f ih =>
    obtain ⟨g, hg, ha⟩ := ih
    exact ⟨g.compl, by simp only [s2v_t11b_Formula.realize, hg, Set.preimage_compl], ha⟩
  | inter f g ihf ihg =>
    obtain ⟨f', hf, haf⟩ := ihf
    obtain ⟨g', hg, hag⟩ := ihg
    refine ⟨f'.inter g', ?_, ?_⟩
    · simp only [s2v_t11b_Formula.realize, hf, hg, Set.preimage_inter]
    · simp only [s2v_t11b_Formula.atoms, haf, hag, Finset.image_union]

end HodgeLean.Foundations.Program
