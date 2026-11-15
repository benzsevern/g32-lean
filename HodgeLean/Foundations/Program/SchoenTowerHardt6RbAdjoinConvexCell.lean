import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdjoinConvexCone
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRelativeConeTriangulation

/-! Construction of a finite geometric extension by an actual compact convex cell with prescribed boundary. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adjoin_convex_cell {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hcompact : IsCompact C) (hC : Convex ℝ C)
    (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (K B : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hBK : B.faces ⊆ K.faces) (hB : B.space = C \ intrinsicInterior ℝ C)
    (hne : B.space.Nonempty) (hKC : K.space ∩ C ⊆ C \ intrinsicInterior ℝ C) :
    ∃ L P : Geometry.SimplicialComplex ℝ E,
      L.faces.Finite ∧ P.faces.Finite ∧ P.space = C ∧
      L.faces = K.faces ∪ P.faces ∧ L.space = K.space ∪ C ∧
      B.faces ⊆ P.faces ∧
      (∀ s, s ∈ P.faces ↔ ∃ t ∈ B.faces, s ⊆ insert a t ∧ s.Nonempty) ∧
      (∀ s ∈ P.faces, s ∈ B.faces ↔ a ∉ s) := by
  obtain ⟨P, hP, hPC, hBP, hfaces, hrestr⟩ := s2v_hardt6rb_relative_cone_triangulation
    C hcompact hC a ha B (hK.subset hBK) hB hne
  obtain ⟨L, hLf, hL, hLs⟩ := s2v_hardt6rb_adjoin_convex_cone C hC a ha K B P hK hP hBK hB hPC
    (fun s hs => by obtain ⟨t, ht, hst, _⟩ := (hfaces s).mp hs; exact ⟨t, ht, hst⟩) hKC
  exact ⟨L, P, hL, hP, hPC, hLf, hLs, hBP, hfaces, hrestr⟩

end HodgeLean.Foundations.Program
