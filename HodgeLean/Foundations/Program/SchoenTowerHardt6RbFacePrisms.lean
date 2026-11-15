import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOrderedPrism

/-! Locally constructed ordered band complexes over every actual base face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_prisms {E : Type*}
    [AddCommGroup E] [Module ℝ E] [LinearOrder E]
    (K : Geometry.SimplicialComplex ℝ E) (l u : E → ℝ)
    (hlu : ∀ x ∈ K.vertices, l x ≤ u x) :
    ∃ C : K.faces → Geometry.SimplicialComplex ℝ (E × ℝ),
      (∀ s, (C s).faces.Finite) ∧
      (∀ s t, t ∈ (C s).faces ↔ ∃ j : s.val,
        (↑t : Set (E × ℝ)) ⊆
          (((fun i : s.val => (i.val, l i.val)) '' {i | j ≤ i}) ∪
            ((fun i : s.val => (i.val, u i.val)) '' {i | i ≤ j})) ∧ t.Nonempty) := by
  classical
  have hex (s : K.faces) : ∃ L : Geometry.SimplicialComplex ℝ (E × ℝ),
      L.faces.Finite ∧
      (∀ t, t ∈ L.faces ↔ ∃ j : s.val,
        (↑t : Set (E × ℝ)) ⊆
          (((fun i : s.val => (i.val, l i.val)) '' {i | j ≤ i}) ∪
            ((fun i : s.val => (i.val, u i.val)) '' {i | i ≤ j})) ∧ t.Nonempty) := by
    letI : Nonempty s.val := by
      obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces s.property
      exact ⟨⟨x, hx⟩⟩
    apply s2v_hardt6rb_ordered_prism_complex (fun i : s.val => i.val)
      (K.indep s.property) (fun i => l i.val) (fun i => u i.val)
    intro i
    apply hlu i.val
    exact K.down_closed s.property (Finset.singleton_subset_iff.mpr i.property)
      (Finset.singleton_nonempty _)
  choose C hfinite hfaces using hex
  exact ⟨C, hfinite, hfaces⟩

end HodgeLean.Foundations.Program
