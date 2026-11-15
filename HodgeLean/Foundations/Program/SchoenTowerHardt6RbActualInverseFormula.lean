import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Actual inverse graph formulas with independent input and output dimensions. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_actual_inverse_formula {n m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (B : Set (EuclideanSpace ℝ (Fin m)))
    (h : A ≃ₜ B) (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i)) :
    ∃ R : s2v_t11b_Formula (m + n), ∀ z, z ∈ R.realize ↔ ∃ y : B,
      (∀ i, z (Fin.castAdd n i) = y.val i) ∧
      (∀ i, z (Fin.natAdd m i) = (h.symm y).val i) := by
  let r : Fin (n + m) → Fin (m + n) :=
    Fin.addCases (Fin.natAdd m) (Fin.castAdd n)
  refine ⟨s2v_hardt1_rename r G, ?_⟩
  intro z
  rw [s2v_hardt1_realize_rename, hG]
  simp only [r, PiLp.toLp_apply, Fin.addCases_left, Fin.addCases_right]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨h x, hy, by simpa only [h.symm_apply_apply] using hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨h.symm y, hx, by simpa only [h.apply_symm_apply] using hy⟩

end HodgeLean.Foundations.Program
