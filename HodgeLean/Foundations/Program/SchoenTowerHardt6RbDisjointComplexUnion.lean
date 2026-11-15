import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! Disjoint finite geometric complexes can be assembled without introducing additional faces. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_disjoint_complex_union {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K P : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P.faces.Finite)
    (hdisj : Disjoint K.space P.space) :
    ∃ L : Geometry.SimplicialComplex ℝ E,
      L.faces = K.faces ∪ P.faces ∧ L.faces.Finite ∧ L.space = K.space ∪ P.space := by
  let F : Bool → Geometry.SimplicialComplex ℝ E := fun b => if b then P else K
  have hf (b : Bool) : (F b).faces.Finite := by cases b; exact hK; exact hP
  have hc : ∀ i j s t, s ∈ (F i).faces → t ∈ (F j).faces →
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro i j s t hs ht
    cases i <;> cases j
    · exact K.inter_subset_convexHull hs ht
    · rintro x ⟨hxs, hxt⟩
      exact False.elim (Set.disjoint_left.mp hdisj (K.convexHull_subset_space hs hxs)
        (P.convexHull_subset_space ht hxt))
    · rintro x ⟨hxs, hxt⟩
      exact False.elim (Set.disjoint_left.mp hdisj (K.convexHull_subset_space ht hxt)
        (P.convexHull_subset_space hs hxs))
    · exact P.inter_subset_convexHull hs ht
  obtain ⟨L, hLf, hL, hLs⟩ := s2v_hardt6rb_assemble_complex F hf hc
  refine ⟨L, ?_, hL, ?_⟩
  · rw [hLf]
    ext s
    simp [F]
  · rw [hLs]
    ext x
    simp [F]

end HodgeLean.Foundations.Program
