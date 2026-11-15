import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubdivisionFull

/-! One finite geometric refinement simultaneously makes every original subcomplex full. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_common_full_subdivision {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      ∀ D : Geometry.SimplicialComplex ℝ E, D.faces ⊆ K.faces →
        ∃ M : Geometry.SimplicialComplex ℝ E, M.faces.Finite ∧ M.faces ⊆ L.faces ∧
          M.space = D.space ∧
          (∀ s ∈ L.faces, (∀ x ∈ s, x ∈ M.vertices) → s ∈ M.faces) := by
  obtain ⟨L, hfinite, hfaces, hspace⟩ := s2v_hardt6rb_centroid_subdivision K hK
  exact ⟨L, hfinite, hspace, fun D hDK => s2v_hardt6rb_subdivision_subcomplex_full K D hK hDK L hfaces⟩

end HodgeLean.Foundations.Program
