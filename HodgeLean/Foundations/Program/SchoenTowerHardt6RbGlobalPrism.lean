import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalPrismIntersection

/-! A finite geometric band complex over an arbitrary finite ordered base complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_global_prism_complex {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (l u : E → ℝ) (hlu : ∀ x ∈ K.vertices, l x ≤ u x) :
    ∃ L : Geometry.SimplicialComplex ℝ (E × ℝ), L.faces.Finite ∧
      (∀ r, r ∈ L.faces ↔ ∃ s ∈ K.faces, ∃ j : s,
        (↑r : Set (E × ℝ)) ⊆
          (((fun i : s => (i.val, l i.val)) '' {i | j ≤ i}) ∪
            ((fun i : s => (i.val, u i.val)) '' {i | i ≤ j})) ∧ r.Nonempty) := by
  classical
  letI : Fintype K.faces := hK.fintype
  obtain ⟨C, hfinite, hfaces⟩ := s2v_hardt6rb_face_prisms K l u hlu
  obtain ⟨L, hLfaces, hLfinite, _⟩ := s2v_hardt6rb_assemble_complex C hfinite
    (s2v_hardt6rb_global_prism_intersection K l u C hfaces)
  refine ⟨L, hLfinite, ?_⟩
  intro r
  rw [hLfaces, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨j, hj, hne⟩ := (hfaces s r).mp hs
    exact ⟨s.val, s.property, j, hj, hne⟩
  · rintro ⟨s, hs, j, hj, hne⟩
    exact ⟨⟨s, hs⟩, (hfaces ⟨s, hs⟩ r).mpr ⟨j, hj, hne⟩⟩

end HodgeLean.Foundations.Program
