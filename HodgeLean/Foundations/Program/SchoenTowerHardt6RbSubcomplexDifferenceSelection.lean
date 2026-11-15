import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplementFaceSelection

/-! Shared subcomplexes select their carrier difference by actual intrinsic open faces. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_subcomplex_difference_selection {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K P Q : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P.faces ⊆ K.faces) (hQK : Q.faces ⊆ K.faces) :
    ∃ R : Finset (Finset E), (↑R : Set _) ⊆ K.faces ∧
      ∀ x : K.space, (∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) ↔
        x.val ∈ P.space \ Q.space := by
  classical
  let R := hK.toFinset.filter (fun s => s ∈ P.faces ∧ s ∉ Q.faces)
  have hR : ∀ s, s ∈ R ↔ s ∈ K.faces ∧ s ∈ P.faces ∧ s ∉ Q.faces := by
    intro s
    simp only [R, Finset.mem_filter, hK.mem_toFinset]
  refine ⟨R, fun s hs => ((hR s).mp hs).1, ?_⟩
  intro x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨hsK, hsP, hsQ⟩ := (hR s).mp hs
    exact ⟨(s2v_hardt6rb_open_face_mem_subcomplex_iff K P hPK s hsK hx).mpr hsP,
      fun hq => hsQ ((s2v_hardt6rb_open_face_mem_subcomplex_iff K Q hQK s hsK hx).mp hq)⟩
  · rintro ⟨hp, hq⟩
    obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face K x.property
    refine ⟨s, (hR s).mpr ⟨hs, ?_, ?_⟩, hxs⟩
    · exact (s2v_hardt6rb_open_face_mem_subcomplex_iff K P hPK s hs hxs).mp hp
    · intro hsq
      exact hq ((s2v_hardt6rb_open_face_mem_subcomplex_iff K Q hQK s hs hxs).mpr hsq)

end HodgeLean.Foundations.Program
