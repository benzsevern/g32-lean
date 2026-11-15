import HodgeLean.Foundations.Program.SchoenTowerHardt2Distance

/-! Quantified polynomial operations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- One existential spatial coordinate has a Boolean parameter description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1. -/
theorem s2v_hardt2_projection_aux {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize := by
  exact s2v_hardt2_project_coordinate f

/-- One universally quantified spatial coordinate has a Boolean parameter description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, complement consequence. -/
theorem s2v_hardt2_universal_aux {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∀ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize := by
  exact s2v_hardt2_forall_coordinate f

/-- The metric approximation condition has an exact Boolean description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, closure consequence. -/
theorem s2v_hardt2_closure_formula_aux {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ d : s2v_t11b_Formula n, d.realize = closure f.realize ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ d.realize ↔
        ∀ ε : ℝ, 0 < ε → ∃ y ∈ f.realize,
          (∑ i : Fin n, (x i - y i)^2) < ε^2 := by
  obtain ⟨d, hd⟩ := s2v_hardt2_distance_exists f
  let pos : s2v_t11b_Formula (n + 1) := .compl (.nonneg (-MvPolynomial.X 0))
  let F := s2v_t11b_Formula.compl (.inter pos (.compl d))
  obtain ⟨g, hg⟩ := s2v_hardt2_forall_coordinate F
  have h (x : EuclideanSpace ℝ (Fin n)) : x ∈ g.realize ↔
      ∀ ε : ℝ, 0 < ε → ∃ y ∈ f.realize,
        (∑ i : Fin n, (x i - y i)^2) < ε^2 := by
    rw [hg]
    have hp (ε : ℝ) : WithLp.toLp 2 (Fin.cons ε (fun i => x i)) ∈ pos.realize ↔ 0 < ε := by
      simp [pos, s2v_t11b_Formula.realize]
    simp only [F, s2v_t11b_Formula.realize, Set.mem_compl_iff, Set.mem_inter_iff,
      not_and, not_not, hp, hd, Fin.cons_succ, Fin.cons_zero]
  refine ⟨g, ?_, h⟩
  ext x
  exact (h x).trans (s2v_hardt2_metric_encoding f.realize x).symm

end HodgeLean.Foundations.Program
