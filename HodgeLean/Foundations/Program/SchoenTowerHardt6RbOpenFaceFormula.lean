import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenSimplexFormula

/-! Actual intrinsic open faces of independent finite vertex sets have Boolean formulas. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_face_formula {n : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n))) :
    ∃ f : s2v_t11b_Formula n,
      f.realize = intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let e := (Fintype.equivFin s).symm
  let v : Fin (Fintype.card s) → EuclideanSpace ℝ (Fin n) := fun i => (e i).val
  have hv : AffineIndependent ℝ v := hs.comp_embedding e.toEmbedding
  obtain ⟨f, hf⟩ := s2v_hardt6rb_open_simplex_formula v hv
  have hr : Set.range v = (↑s : Set (EuclideanSpace ℝ (Fin n))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  exact ⟨f, hr ▸ hf⟩

end HodgeLean.Foundations.Program
