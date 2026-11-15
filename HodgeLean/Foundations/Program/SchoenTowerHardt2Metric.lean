import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Euclidean metric approximation retains the positive radius and squared coordinate sum.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, metric consequence. -/
theorem s2v_hardt2_metric_encoding {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ closure S ↔ ∀ ε : ℝ, 0 < ε → ∃ y ∈ S,
      (∑ i : Fin n, (x i - y i)^2) < ε^2 := by
  rw [Metric.mem_closure_iff]
  have hs (y : EuclideanSpace ℝ (Fin n)) :
      dist x y ^ 2 = ∑ i : Fin n, (x i - y i)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp only [Real.dist_eq, sq_abs]
  constructor
  · intro h ε hε
    obtain ⟨y, hy, hd⟩ := h ε hε
    refine ⟨y, hy, ?_⟩
    rw [← hs]
    exact (sq_lt_sq₀ dist_nonneg hε.le).mpr hd
  · intro h ε hε
    obtain ⟨y, hy, hd⟩ := h ε hε
    refine ⟨y, hy, ?_⟩
    rw [← hs] at hd
    exact (sq_lt_sq₀ dist_nonneg hε.le).mp hd

#print axioms s2v_hardt2_metric_encoding
end HodgeLean.Foundations.Program
