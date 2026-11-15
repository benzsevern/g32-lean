import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment

/-! Membership in any selected union of intrinsic open faces is determined by the unique face. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_selected_open_face_membership {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (S : Finset (Finset E))
    (hS : (↑S : Set (Finset E)) ⊆ K.faces)
    (s : Finset E) (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) :
    (∃ t ∈ S, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑t : Set E))) ↔ s ∈ S := by
  constructor
  · rintro ⟨t, ht, hxt⟩
    have hst := s2v_hardt6rb_open_face_subset_of_mem_face K s t hs (hS ht)
      hx (intrinsicInterior_subset hxt)
    have hts := s2v_hardt6rb_open_face_subset_of_mem_face K t s (hS ht) hs
      hxt (intrinsicInterior_subset hx)
    exact (Finset.Subset.antisymm hst hts).symm ▸ ht
  · intro hsS
    exact ⟨s, hsS, hx⟩

end HodgeLean.Foundations.Program
