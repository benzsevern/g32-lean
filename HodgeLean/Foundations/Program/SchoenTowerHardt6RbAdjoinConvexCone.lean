import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeBoundaryHull
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! A convex cone cell can be adjoined to a geometric complex along its existing boundary. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adjoin_convex_cone {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (K B P : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P.faces.Finite)
    (hBK : B.faces ⊆ K.faces) (hB : B.space = C \ intrinsicInterior ℝ C)
    (hPC : P.space = C)
    (hfaces : ∀ s ∈ P.faces, ∃ t ∈ B.faces, s ⊆ insert a t)
    (hKC : K.space ∩ C ⊆ C \ intrinsicInterior ℝ C) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces = K.faces ∪ P.faces ∧
      L.faces.Finite ∧ L.space = K.space ∪ C := by
  have hcross : ∀ s t, s ∈ K.faces → t ∈ P.faces →
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro s t hs ht x hx
    obtain ⟨u, hu, htu⟩ := hfaces t ht
    have heU : t.erase a ⊆ u := by
      intro y hy
      exact (Finset.mem_insert.mp (htu (Finset.mem_of_mem_erase hy))).resolve_left
        (Finset.ne_of_mem_erase hy)
    have heb : convexHull ℝ (↑(t.erase a) : Set E) ⊆ C \ intrinsicInterior ℝ C := by
      intro y hy
      rw [← hB]
      exact B.convexHull_subset_space hu (convexHull_mono (Finset.coe_subset.mpr heU) hy)
    have hxB := hKC ⟨K.convexHull_subset_space hs hx.1, hPC ▸ P.convexHull_subset_space ht hx.2⟩
    have hxe : x ∈ convexHull ℝ (↑(t.erase a) : Set E) := by
      rw [← s2v_hardt6rb_cone_boundary_hull C hC a ha t heb]
      exact ⟨hx.2, hxB⟩
    have hne : (t.erase a).Nonempty :=
      Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxe⟩)
    have heK := hBK (B.down_closed hu heU hne)
    have hxi := K.inter_subset_convexHull hs heK ⟨hx.1, hxe⟩
    apply convexHull_mono _ hxi
    rintro y ⟨hys, hye⟩
    exact ⟨hys, Finset.mem_of_mem_erase hye⟩
  let F : Bool → Geometry.SimplicialComplex ℝ E := fun b => if b then P else K
  have hf (b : Bool) : (F b).faces.Finite := by
    cases b
    · exact hK
    · exact hP
  have hc : ∀ i j s t, s ∈ (F i).faces → t ∈ (F j).faces →
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro i j s t hs ht
    cases i <;> cases j
    · exact K.inter_subset_convexHull hs ht
    · exact hcross s t hs ht
    · intro x hx
      have hh := hcross t s ht hs ⟨hx.2, hx.1⟩
      simpa only [Set.inter_comm] using hh
    · exact P.inter_subset_convexHull hs ht
  obtain ⟨L, hLf, hL, hLs⟩ := s2v_hardt6rb_assemble_complex F hf hc
  refine ⟨L, ?_, hL, ?_⟩
  · rw [hLf]
    ext s
    simp [F]
  · rw [hLs]
    ext x
    simp [F, hPC]

end HodgeLean.Foundations.Program
