import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChainComplex
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChainIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChainCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubfaceIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! Construction of a finite centroid-chain subdivision of one independent vertex hull. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_centroid_subdivision {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧
      (∀ s, s ∈ K.faces ↔ ∃ C : Finset (Finset ι),
        (∀ T ∈ C, T.Nonempty) ∧
        (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) ∧
        (↑s : Set E) ⊆ (fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι)) ∧ s.Nonempty) ∧
      K.space = convexHull ℝ (Set.range v) := by
  classical
  let J := {C : Finset (Finset ι) //
    (∀ T ∈ C, T.Nonempty) ∧ (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)}
  letI : Fintype J := Fintype.ofFinite J
  choose A hfaces hfinite hspace using (fun j : J =>
    s2v_hardt6rb_centroid_chain_complex v hv j.val j.property.1 j.property.2)
  let P : J → Finset E := fun j => j.val.image (fun T => T.centroid ℝ v)
  have hP (j : J) : (↑(P j) : Set E) =
      (fun T => T.centroid ℝ v) '' (↑j.val : Set (Finset ι)) := Finset.coe_image
  have hind (j : J) : AffineIndependent ℝ (fun x : P j => x.val) := by
    have hi := (s2v_hardt6rb_centroid_chain_independent v hv j.val j.property.1 j.property.2).range
    change AffineIndependent ℝ (fun x : Set.range (fun T : j.val => T.val.centroid ℝ v) => x.val) at hi
    have hrange : Set.range (fun T : j.val => T.val.centroid ℝ v) = (↑(P j) : Set E) := by
      ext x
      simp only [Set.mem_range, Subtype.exists, exists_prop, P, Finset.mem_coe, Finset.mem_image]
    rw [hrange] at hi
    exact hi
  have hcross : ∀ i j s t, s ∈ (A i).faces → t ∈ (A j).faces →
      convexHull ℝ (↑s : Set E) ∩ convexHull ℝ (↑t : Set E) ⊆
        convexHull ℝ ((↑s : Set E) ∩ ↑t) := by
    intro i j s t hs ht
    have hsP : s ⊆ P i := Finset.coe_subset.mp (by
      rw [hP i]
      exact ((hfaces i s).mp hs).1)
    have htP : t ⊆ P j := Finset.coe_subset.mp (by
      rw [hP j]
      exact ((hfaces j t).mp ht).1)
    apply s2v_hardt6rb_subface_intersection (P i) (P j) s t (hind i) (hind j) hsP htP
    simpa only [hP i, hP j] using
      (s2v_hardt6rb_centroid_chain_intersection v hv i.val j.val i.property.1 j.property.1
        i.property.2 j.property.2).subset
  obtain ⟨K, hKfaces, hKfinite, hKspace⟩ := s2v_hardt6rb_assemble_complex A hfinite hcross
  refine ⟨K, hKfinite, ?_, ?_⟩
  · intro s
    rw [hKfaces, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨hsub, hne⟩ := (hfaces j s).mp hj
      exact ⟨j.val, j.property.1, j.property.2, hsub, hne⟩
    · rintro ⟨C, hne, hchain, hsub, hsne⟩
      exact ⟨⟨C, hne, hchain⟩, (hfaces ⟨C, hne, hchain⟩ s).mpr ⟨hsub, hsne⟩⟩
  · rw [hKspace]
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hp⟩
      rw [hspace j] at hp
      apply (convexHull_min ?_ (convex_convexHull ℝ (Set.range v))) hp
      rintro x ⟨T, hT, rfl⟩
      have hx := (s2v_hardt6rb_centroid_mem_face_iff v hv T Finset.univ (j.property.1 T hT)).mpr
        (Finset.subset_univ T)
      simpa only [Finset.coe_univ, Set.image_univ] using hx
    · intro hp
      obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights v p).mp hp
      obtain ⟨C, hne, hchain, _, hcover⟩ := s2v_hardt6rb_centroid_chain_cover v w
      let j : J := ⟨C, hne, hchain⟩
      refine ⟨j, ?_⟩
      rw [hspace j]
      exact hw ▸ hcover

end HodgeLean.Foundations.Program
