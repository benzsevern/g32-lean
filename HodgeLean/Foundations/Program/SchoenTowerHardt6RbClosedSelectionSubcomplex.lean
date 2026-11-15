import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicDensity
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSelectedFaceMembership
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceCover

/-! A compatible closed locus is the carrier of an actual finite geometric subcomplex. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_closed_selection_subcomplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C : Set E) (hC : IsClosed C) (S : Finset (Finset E))
    (hS : (↑S : Set (Finset E)) ⊆ K.faces)
    (hsel : ∀ x ∈ K.space, x ∈ C ↔
      ∃ s ∈ S, x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) :
    ∃ D : Geometry.SimplicialComplex ℝ E, D.faces.Finite ∧ D.faces ⊆ K.faces ∧
      D.space = K.space ∩ C ∧
      (∀ s, s ∈ D.faces ↔ s ∈ K.faces ∧ convexHull ℝ (↑s : Set E) ⊆ C) := by
  let D : Geometry.SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (↑s : Set E) ⊆ C}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      indep := fun hs => K.indep hs.1
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  have hDK : D.faces ⊆ K.faces := fun _ hs => hs.1
  refine ⟨D, hK.subset hDK, hDK, ?_, fun _ => Iff.rfl⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨K.convexHull_subset_space hs.1 hxs, hs.2 hxs⟩
  · rintro ⟨hxK, hxC⟩
    obtain ⟨s, hs, hxs⟩ := s2v_hardt6rb_mem_open_face K hxK
    have hsS : s ∈ S := (s2v_hardt6rb_selected_open_face_membership K S hS s hs hxs).mp
      ((hsel x hxK).mp hxC)
    have hopen : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)) ⊆ C := by
      intro y hy
      exact (hsel y (K.convexHull_subset_space hs (intrinsicInterior_subset hy))).mpr ⟨s, hsS, hy⟩
    have hhull : convexHull ℝ (↑s : Set E) ⊆ C :=
      (s2v_hardt6rb_convex_subset_closure_intrinsicInterior _ (convex_convexHull ℝ _)).trans
        (closure_minimal hopen hC)
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hhull⟩, intrinsicInterior_subset hxs⟩

end HodgeLean.Foundations.Program
