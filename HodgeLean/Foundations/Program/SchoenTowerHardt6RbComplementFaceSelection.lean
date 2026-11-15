import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceSubcomplex

/-! All faces outside a subcomplex select exactly the complement of its carrier. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_complement_face_selection {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hKL : K.faces ⊆ L.faces) (hL : L.faces.Finite) :
    ∃ R : Finset (Finset E),
      (∀ s, s ∈ R ↔ s ∈ L.faces ∧ s ∉ K.faces) ∧
      (∀ x : L.space, (∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) ↔
        x.val ∉ K.space) := by
  classical
  let R := hL.toFinset.filter (fun s => s ∉ K.faces)
  have hR : ∀ s, s ∈ R ↔ s ∈ L.faces ∧ s ∉ K.faces := by
    intro s
    simp only [R, Finset.mem_filter, hL.mem_toFinset]
  refine ⟨R, hR, ?_⟩
  intro x
  constructor
  · rintro ⟨s, hs, hx⟩ hxK
    have hh := (hR s).mp hs
    exact hh.2 ((s2v_hardt6rb_open_face_mem_subcomplex_iff L K hKL s hh.1 hx).mp hxK)
  · intro hx
    obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face L x.property
    refine ⟨s, (hR s).mpr ⟨hs, ?_⟩, hxs⟩
    intro hsK
    exact hx ((s2v_hardt6rb_open_face_mem_subcomplex_iff L K hKL s hs hxs).mpr hsK)

end HodgeLean.Foundations.Program
