import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveFullTriangulation

/-! # Original singleton algebraic marks give actual vertices -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual singleton subcomplex carrier forces its original point to be a vertex of the ambient complex.
Source: Geometry.SimplicialComplex.mem_space_iff; Geometry.SimplicialComplex.nonempty_of_mem_faces.
HC no distance; AV milestone no distance. -/
theorem properCycle_singleton_subcomplex_vertex {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces)
    (p : E) (hspace : D.space = {p}) : ({p} : Finset E) ∈ K.faces := by
  classical
  have hp : p ∈ D.space := by rw [hspace]; exact Set.mem_singleton p
  obtain ⟨s, hs, _⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
  have hsub (a : E) (ha : a ∈ s) : a = p := by
    have h : a ∈ D.space := D.convexHull_subset_space hs
      (subset_convexHull ℝ (s : Set E) ha)
    rw [hspace] at h
    exact h
  have he : s = {p} := by
    ext a
    constructor
    · intro ha
      exact Finset.mem_singleton.mpr (hsub a ha)
    · intro ha
      have hap : a = p := Finset.mem_singleton.mp ha
      obtain ⟨b, hb⟩ := D.nonempty_of_mem_faces hs
      rw [hap, ← hsub b hb]
      exact hb
  exact he ▸ hDK hs

end HodgeLean.Foundations.QuotientDuality
