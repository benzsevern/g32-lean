import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Coordinate interchange for actual homeomorphism graphs. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_inverse_graph {n : ℕ}
    {A B : Set (EuclideanSpace ℝ (Fin n))} (h : A ≃ₜ B)
    (g : s2v_t11b_Formula (n + n))
    (hg : ∀ z, z ∈ g.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd n i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (z : EuclideanSpace ℝ (Fin (n + n))) :
    WithLp.toLp 2 (fun i =>
      Fin.addCases (fun j => z (Fin.natAdd n j))
        (fun j => z (Fin.castAdd n j)) i) ∈ g.realize ↔
      ∃ y : B, (∀ i, z (Fin.castAdd n i) = y.val i) ∧
        (∀ i, z (Fin.natAdd n i) = (h.symm y).val i) := by
  rw [hg]
  simp only [WithLp.ofLp_toLp, Fin.addCases_left, Fin.addCases_right]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨h x, hy, by simpa only [h.symm_apply_apply] using hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨h.symm y, hx, by simpa only [h.apply_symm_apply] using hy⟩

end HodgeLean.Foundations.Program
