import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidFace
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Centroid incidence recovers actual face containment across a geometric complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_mem_base_face_iff {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (s t : Finset E)
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    s.centroid ℝ id ∈ convexHull ℝ (↑t : Set E) ↔ s ⊆ t := by
  classical
  have hne := K.nonempty_of_mem_faces hs
  constructor
  · intro hx
    let I : Finset s := Finset.univ.filter (fun i => i.val ∈ t)
    have hI : (fun i : s => i.val) '' (↑I : Set s) = (↑(s ∩ t) : Set E) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact Finset.mem_inter.mpr ⟨i.property, (Finset.mem_filter.mp hi).2⟩
      · intro hx
        obtain ⟨hxs, hxt⟩ := Finset.mem_inter.mp hx
        exact ⟨⟨x, hxs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt⟩, rfl⟩
    have huniv : (Finset.univ : Finset s).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hx⟩, Finset.mem_univ _⟩
    have hcent : (Finset.univ : Finset s).centroid ℝ (fun i : s => (i.val : E)) =
        s.centroid ℝ id := Finset.centroid_univ ℝ s
    have hmem : (Finset.univ : Finset s).centroid ℝ (fun i : s => (i.val : E)) ∈
        convexHull ℝ ((fun i : s => i.val) '' (↑I : Set s)) := by
      rw [hcent, hI]
      simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht
        ⟨s.centroid_mem_convexHull hne, hx⟩
    have hsub := (s2v_hardt6rb_centroid_mem_face_iff (fun i : s => i.val)
      (K.indep hs) Finset.univ I huniv).mp hmem
    intro x hx
    exact (Finset.mem_filter.mp (hsub (Finset.mem_univ ⟨x, hx⟩))).2
  · intro hst
    exact convexHull_mono (Finset.coe_subset.mpr hst) (s.centroid_mem_convexHull hne)

end HodgeLean.Foundations.Program
