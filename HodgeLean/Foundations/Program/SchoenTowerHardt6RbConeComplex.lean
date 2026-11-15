import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeIndependence
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubfaceIntersection

/-! A finite geometric boundary complex cones to a finite complex retaining all prescribed faces. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cone_complex {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) (a : E) (ha : a ∈ intrinsicInterior ℝ C)
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hb : K.space ⊆ C \ intrinsicInterior ℝ C) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      (∀ s, s ∈ L.faces ↔ ∃ t ∈ K.faces, s ⊆ insert a t ∧ s.Nonempty) ∧
      K.faces ⊆ L.faces ∧
      (∀ x, x ∈ L.space ↔ ∃ y ∈ K.space, ∃ u ∈ Set.Icc (0 : ℝ) 1,
        AffineMap.lineMap a y u = x) := by
  classical
  letI : Fintype K.faces := hK.fintype
  have hi (s : K.faces) : AffineIndependent ℝ (fun x : {x : E // x ∈ insert a s.val} => x.val) :=
    s2v_hardt6rb_cone_independence C hC a ha s.val (K.nonempty_of_mem_faces s.property)
      (K.indep s.property) (fun _ hx => hb (K.convexHull_subset_space s.property hx))
  choose P hP hPf hPs using fun s : K.faces => s2v_hardt6rb_simplex_complex (insert a s.val) (hi s)
  have hcross : ∀ (i j : K.faces) s t, s ∈ (P i).faces → t ∈ (P j).faces →
      convexHull ℝ (↑s : Set E) ∩ convexHull ℝ (↑t : Set E) ⊆
        convexHull ℝ ((↑s : Set E) ∩ ↑t) := by
    intro i j s t hs ht
    apply s2v_hardt6rb_subface_intersection (insert a i.val) (insert a j.val) s t
      (hi i) (hi j) ((hP i s).mp hs).1 ((hP j t).mp ht).1
    simpa only [Finset.coe_insert, ← Set.insert_inter_distrib] using
      s2v_hardt6rb_cone_intersection C hC a ha i.val j.val
        (K.nonempty_of_mem_faces i.property) (K.nonempty_of_mem_faces j.property)
        (fun _ hx => hb (K.convexHull_subset_space i.property hx))
        (fun _ hx => hb (K.convexHull_subset_space j.property hx))
        (K.inter_subset_convexHull i.property j.property)
  obtain ⟨L, hLf, hfinite, hLs⟩ := s2v_hardt6rb_assemble_complex P hPf hcross
  have hfaces : ∀ s, s ∈ L.faces ↔ ∃ t ∈ K.faces, s ⊆ insert a t ∧ s.Nonempty := by
    intro s
    rw [hLf]
    simp only [Set.mem_iUnion, hP]
    constructor
    · rintro ⟨t, ht, hn⟩
      exact ⟨t.val, t.property, ht, hn⟩
    · rintro ⟨t, ht, hst, hn⟩
      exact ⟨⟨t, ht⟩, hst, hn⟩
  refine ⟨L, hfinite, hfaces, ?_, ?_⟩
  · intro s hs
    exact (hfaces s).mpr ⟨s, hs, Finset.subset_insert _ _, K.nonempty_of_mem_faces hs⟩
  · intro x
    rw [hLs]
    simp only [Set.mem_iUnion, hPs]
    constructor
    · rintro ⟨s, hx⟩
      obtain ⟨y, hy, u, hu, he⟩ := (s2v_hardt6rb_cone_coordinates a s.val
        (K.nonempty_of_mem_faces s.property) x).mp hx
      exact ⟨y, K.convexHull_subset_space s.property hy, u, hu, he⟩
    · rintro ⟨y, hy, u, hu, he⟩
      obtain ⟨s, hs, hys⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
      exact ⟨⟨s, hs⟩, (s2v_hardt6rb_cone_coordinates a s
        (K.nonempty_of_mem_faces hs) x).mpr ⟨y, hys, u, hu, he⟩⟩

end HodgeLean.Foundations.Program
