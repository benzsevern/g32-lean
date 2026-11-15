import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSelectedFaceMembership
import Mathlib.Topology.Homeomorph.Defs

/-! Exact target-mark membership on each selected intrinsic open source face. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_marked_open_face_membership {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
    (K : Geometry.SimplicialComplex ℝ E) (A M : Set F) (h : K.space ≃ₜ A)
    (S : Finset (Finset E)) (hS : (↑S : Set _) ⊆ K.faces)
    (hsel : A ∩ M = (fun x : K.space => (h x).val) ''
      {x : K.space | ∃ s ∈ S, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))})
    (s : Finset E) (hs : s ∈ K.faces) (x : K.space)
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) :
    (h x).val ∈ M ↔ s ∈ S := by
  constructor
  · intro hxM
    have him : (h x).val ∈ (fun y : K.space => (h y).val) ''
        {y : K.space | ∃ t ∈ S, y.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑t : Set E))} :=
      hsel ▸ ⟨(h x).property, hxM⟩
    obtain ⟨y, hy, hyx⟩ := him
    have he : y = x := h.injective (Subtype.ext hyx)
    exact (s2v_hardt6rb_selected_open_face_membership K S hS s hs hx).mp (he ▸ hy)
  · intro hsS
    have him : (h x).val ∈ A ∩ M := hsel.symm ▸
      Set.mem_image_of_mem (fun y : K.space => (h y).val) ⟨s, hsS, hx⟩
    exact him.2

end HodgeLean.Foundations.Program
