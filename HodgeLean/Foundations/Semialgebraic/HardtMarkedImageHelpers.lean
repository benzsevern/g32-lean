import HodgeLean.Foundations.Semialgebraic.ScalarGraphHelpers

/-! Actual Boolean images of marked subsets under semialgebraic maps. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace Semialgebraic.ScalarTriangulation

/-- A marked source subset has an actual Boolean image under a map with an actual graph. -/
theorem actual_marked_image_formula {n k : ℕ} (f b : s2v_t11b_Formula n)
    (φ : f.realize → EuclideanSpace ℝ (Fin k)) (G : s2v_t11b_Formula (n + k))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : f.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = φ x i)) :
    ∃ P : s2v_t11b_Formula k, ∀ y, y ∈ P.realize ↔
      ∃ x : f.realize, φ x = y ∧ x.val ∈ b.realize := by
  let D := G.inter (b.subst (fun i => MvPolynomial.X (Fin.castAdd k i)))
  obtain ⟨P, hP⟩ := s2v_hardt_cad5_block_projection_formula D
  refine ⟨P, ?_⟩
  intro y
  rw [hP]
  constructor
  · rintro ⟨u, hu⟩
    change _ ∧ _ at hu
    obtain ⟨x, hx, hy⟩ := (hG _).mp hu.1
    have he : u = x.val := by
      ext i
      simpa only [Fin.append_left] using hx i
    have hb := hu.2
    rw [s2v_t11b_realize_subst] at hb
    simp only [MvPolynomial.eval_X, Fin.append_left] at hb
    refine ⟨x, ?_, he ▸ hb⟩
    ext i
    simpa only [Fin.append_right] using (hy i).symm
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x.val, ?_⟩
    change _ ∧ _
    refine ⟨(hG _).mpr ⟨x, fun i => by simp, fun i => by simp⟩, ?_⟩
    rw [s2v_t11b_realize_subst]
    simpa only [MvPolynomial.eval_X, Fin.append_left] using hx

end Semialgebraic.ScalarTriangulation
