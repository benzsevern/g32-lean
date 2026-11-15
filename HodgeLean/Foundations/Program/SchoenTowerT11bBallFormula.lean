import HodgeLean.Foundations.Program.SchoenTowerT11bRealImageFormula

/-! Concrete Boolean descriptions of Euclidean ball neighborhoods.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A positive-radius Euclidean ball has a concrete strict polynomial inequality description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, Euclidean ball description step. -/
theorem s2v_t11b_ball_formula {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) :
    ∃ f : s2v_t11b_Formula n, f.realize = Metric.ball a r := by
  refine ⟨.compl (.nonneg ((∑ i : Fin n, (MvPolynomial.X i - MvPolynomial.C (a i)) ^ 2) -
    MvPolynomial.C (r ^ 2))), ?_⟩
  ext x
  change (¬ 0 ≤ MvPolynomial.eval (fun i => x i) _) ↔ dist x a < r
  have he : MvPolynomial.eval (fun i => x i)
      ((∑ i : Fin n, (MvPolynomial.X i - MvPolynomial.C (a i)) ^ 2) -
        MvPolynomial.C (r ^ 2)) = dist x a ^ 2 - r ^ 2 := by
    simp only [map_sub, map_sum, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
      dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he, not_le, sub_lt_zero]
  exact sq_lt_sq₀ dist_nonneg hr.le

/-- A compact Euclidean subset inside an open set has a Boolean polynomial neighborhood inside that same open set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compact component selection by finite balls. -/
theorem s2v_t11b_compact_boolean_neighborhood {n : ℕ}
    (A O : Set (EuclideanSpace ℝ (Fin n))) (hA : IsCompact A)
    (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : s2v_t11b_Formula n, A ⊆ f.realize ∧ f.realize ⊆ O := by
  classical
  choose r hr hball using fun x : A => Metric.isOpen_iff.mp hO x.val (hAO x.property)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : A => Metric.ball x.val (r x))
    (fun _ => Metric.isOpen_ball) (fun x hx => Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  let E := (Fintype.equivFin t).symm
  choose c hc using fun i : Fin (Fintype.card t) =>
    s2v_t11b_ball_formula (E i).val.val (r (E i).val) (hr (E i).val)
  obtain ⟨f, hf⟩ := s2v_t11b_finite_union_formula c
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hf x).mpr
    refine ⟨E.symm ⟨a, ha⟩, ?_⟩
    rw [hc, E.apply_symm_apply]
    exact hxa
  · intro x hx
    obtain ⟨i, hi⟩ := (hf x).mp hx
    rw [hc] at hi
    exact hball (E i).val hi

/-- A nonnegative-radius Euclidean closed ball has an actual polynomial inequality description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, closed Euclidean ball description step. -/
theorem s2v_t11b_closedBall_formula {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ f : s2v_t11b_Formula n, f.realize = Metric.closedBall a r := by
  refine ⟨.nonneg (MvPolynomial.C (r ^ 2) -
    (∑ i : Fin n, (MvPolynomial.X i - MvPolynomial.C (a i)) ^ 2)), ?_⟩
  ext x
  change (0 ≤ MvPolynomial.eval (fun i => x i) _) ↔ dist x a ≤ r
  have he : MvPolynomial.eval (fun i => x i)
      (MvPolynomial.C (r ^ 2) - (∑ i : Fin n, (MvPolynomial.X i - MvPolynomial.C (a i)) ^ 2)) =
        r ^ 2 - dist x a ^ 2 := by
    simp only [map_sub, map_sum, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
      dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he, sub_nonneg]
  exact sq_le_sq₀ dist_nonneg hr

end HodgeLean.Foundations.Program
