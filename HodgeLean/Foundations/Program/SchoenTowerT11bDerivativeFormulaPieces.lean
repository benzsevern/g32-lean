import HodgeLean.Foundations.Program.SchoenTowerT11bDerivativeSignIntervals

/-! Concrete derivative refinements with interval fibers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite polynomial atom family extends to a concrete derivative atom family whose every Boolean pattern has interval fibers.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, derivative atom refinement step. -/
theorem s2v_t11b_derivative_atom_refinement {n m : ℕ}
    (Q : Fin m → MvPolynomial (Fin (n + 1)) ℝ) :
    ∃ k : ℕ, ∃ A : Fin k → s2v_t11b_Formula (n + 1), ∃ j : Fin m → Fin k,
      (∀ i, A (j i) = .nonneg (Q i)) ∧
      ∀ s : Fin k → Bool, ∀ a : EuclideanSpace ℝ (Fin n),
        Set.OrdConnected {x : ℝ | WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈
          (s2v_t11b_refinementFormula A s).realize} := by
  classical
  let P : Fin m → Polynomial (MvPolynomial (Fin n) ℝ) := fun i => MvPolynomial.finSuccEquiv ℝ n (Q i)
  let J := (i : Fin m) × Fin ((P i).natDegree + 1)
  let E := Fintype.equivFin J
  let A : Fin (Fintype.card J) → s2v_t11b_Formula (n + 1) := fun q =>
    .nonneg ((MvPolynomial.finSuccEquiv ℝ n).symm
      ((Polynomial.derivative^[(E.symm q).2.val]) (P (E.symm q).1)))
  refine ⟨Fintype.card J, A, fun i => E ⟨i, 0⟩, ?_, ?_⟩
  · intro i
    change s2v_t11b_Formula.nonneg ((MvPolynomial.finSuccEquiv ℝ n).symm
      ((Polynomial.derivative^[(E.symm (E (⟨i, 0⟩ : J))).2.val])
        (P (E.symm (E (⟨i, 0⟩ : J))).1))) = _
    rw [E.symm_apply_apply]
    simp only [Fin.val_zero, Function.iterate_zero_apply, P, AlgEquiv.symm_apply_apply]
  · intro s a
    have hv : ∀ q x, WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈ (A q).realize ↔
        0 ≤ ((Polynomial.derivative^[(E.symm q).2.val]) (P (E.symm q).1)).eval₂
          (MvPolynomial.eval (fun v => a v)) x := by
      intro q x
      change (0 ≤ MvPolynomial.eval (Fin.cons x (fun v => a v)) _) ↔ _
      rw [← s2v_t11b_finSucc_family_eval, AlgEquiv.apply_symm_apply]
    have H := s2v_t11b_family_derivative_pattern_ordConnected P
      (MvPolynomial.eval (fun v => a v)) (fun i j => s (E ⟨i, j⟩))
    have he : {x : ℝ | WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈
        (s2v_t11b_refinementFormula A s).realize} =
        {x : ℝ | ∀ i j, s (E ⟨i, j⟩) = true ↔
          0 ≤ ((Polynomial.derivative^[j.val]) (P i)).eval₂ (MvPolynomial.eval (fun v => a v)) x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [s2v_t11b_realize_refinementFormula]
      constructor
      · intro hs i j
        have h := (hs (E ⟨i, j⟩)).trans (hv (E ⟨i, j⟩) x)
        rw [E.symm_apply_apply] at h
        exact h
      · intro hs q
        have h := hs (E.symm q).1 (E.symm q).2
        have h' : s q = true ↔
            0 ≤ ((Polynomial.derivative^[(E.symm q).2.val]) (P (E.symm q).1)).eval₂
              (MvPolynomial.eval (fun v => a v)) x := by
          change s (E (E.symm q)) = true ↔ _ at h
          rwa [E.apply_symm_apply] at h
        exact h'.trans (hv q x).symm
    rw [he]
    exact H

end HodgeLean.Foundations.Program
