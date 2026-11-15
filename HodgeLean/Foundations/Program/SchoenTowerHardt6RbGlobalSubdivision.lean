import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalCentroidIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalCentroidIndependence
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexSubdivision

/-! A finite geometric centroid-chain subdivision of an arbitrary finite base complex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_subdivision {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      (∀ s, s ∈ L.faces ↔ ∃ C : Finset (Finset E),
        (∀ T ∈ C, T ∈ K.faces) ∧
        (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) ∧
        (↑s : Set E) ⊆ (fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E)) ∧ s.Nonempty) ∧
      L.space = K.space := by
  classical
  let F := hK.toFinset
  let J := {C : Finset (Finset E) // C ⊆ F ∧ (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)}
  have hJfinite : {C : Finset (Finset E) | C ⊆ F ∧ (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)}.Finite :=
    F.powerset.finite_toSet.subset (fun C hC => Finset.mem_powerset.mpr hC.1)
  letI : Fintype J := hJfinite.fintype
  have hJK (j : J) : ∀ T ∈ j.val, T ∈ K.faces :=
    fun T hT => hK.mem_toFinset.mp (j.property.1 hT)
  let P : J → Finset E := fun j => j.val.image (fun T : Finset E => T.centroid ℝ id)
  have hP (j : J) : (↑(P j) : Set E) =
      (fun T : Finset E => T.centroid ℝ id) '' (↑j.val : Set (Finset E)) := Finset.coe_image
  have hind (j : J) : AffineIndependent ℝ (fun x : P j => x.val) := by
    have hi := (s2v_hardt6rb_global_centroid_chain_independent K j.val (hJK j) j.property.2).range
    change AffineIndependent ℝ (fun x : Set.range (fun T : j.val => T.val.centroid ℝ id) => x.val) at hi
    have hrange : Set.range (fun T : j.val => T.val.centroid ℝ id) = (↑(P j) : Set E) := by
      ext x
      simp only [Set.mem_range, Subtype.exists, exists_prop, P, Finset.mem_coe, Finset.mem_image]
    rw [hrange] at hi
    exact hi
  choose A hfaces hfinite hspace using (fun j : J => s2v_hardt6rb_simplex_complex (P j) (hind j))
  have hcross : ∀ i j s t, s ∈ (A i).faces → t ∈ (A j).faces →
      convexHull ℝ (↑s : Set E) ∩ convexHull ℝ (↑t : Set E) ⊆ convexHull ℝ ((↑s : Set E) ∩ ↑t) := by
    intro i j s t hs ht
    apply s2v_hardt6rb_subface_intersection (P i) (P j) s t (hind i) (hind j)
      ((hfaces i s).mp hs).1 ((hfaces j t).mp ht).1
    simpa only [hP i, hP j] using
      (s2v_hardt6rb_global_centroid_chain_intersection K i.val j.val (hJK i) (hJK j)
        i.property.2 j.property.2).subset
  obtain ⟨L, hLfaces, hLfinite, hLspace⟩ := s2v_hardt6rb_assemble_complex A hfinite hcross
  refine ⟨L, hLfinite, ?_, ?_⟩
  · intro s
    rw [hLfaces, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨hsub, hne⟩ := (hfaces j s).mp hj
      refine ⟨j.val, hJK j, j.property.2, ?_, hne⟩
      rw [← hP j]
      exact Finset.coe_subset.mpr hsub
    · rintro ⟨C, hCK, hchain, hsub, hne⟩
      let j : J := ⟨C, (fun T hT => hK.mem_toFinset.mpr (hCK T hT)), hchain⟩
      have hsP : s ⊆ P j := Finset.coe_subset.mp (by rw [hP j]; exact hsub)
      exact ⟨j, (hfaces j s).mpr ⟨hsP, hne⟩⟩
  · rw [hLspace]
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hp⟩
      rw [hspace j, hP j] at hp
      have hCne : j.val.Nonempty := by
        by_contra hn
        have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he, Finset.coe_empty, Set.image_empty, convexHull_empty, Set.notMem_empty] using hp
      obtain ⟨S, hS, hmax⟩ := s2v_hardt6rb_face_chain_max j.val hCne j.property.2
      apply K.convexHull_subset_space (hJK j S hS)
      apply (convexHull_min ?_ (convex_convexHull ℝ (↑S : Set E))) hp
      rintro x ⟨T, hT, rfl⟩
      exact (s2v_hardt6rb_centroid_mem_base_face_iff K T S (hJK j T hT) (hJK j S hS)).mpr (hmax T hT)
    · intro hp
      obtain ⟨S, hS, hpS⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
      have hrange : Set.range (fun i : S => (i.val : E)) = (↑S : Set E) := by
        ext x
        simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right, Finset.mem_coe]
      rw [← hrange] at hpS
      obtain ⟨w, hw⟩ := (s2v_hardt6rb_convexHull_range_weights _ p).mp hpS
      obtain ⟨C, hneC, hchainC, _, hcover⟩ := s2v_hardt6rb_centroid_chain_cover (fun i : S => i.val) w
      let e : S ↪ E := Function.Embedding.subtype (fun x => x ∈ S)
      let M := C.image (fun U => U.map e)
      have hMK : ∀ T ∈ M, T ∈ K.faces := by
        intro T hT
        obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
        apply K.down_closed hS
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
          exact i.property
        · obtain ⟨i, hi⟩ := hneC U hU
          exact ⟨e i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
      have hMchain : ∀ T ∈ M, ∀ U ∈ M, T ⊆ U ∨ U ⊆ T := by
        intro T hT U hU
        obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
        obtain ⟨U', hU', rfl⟩ := Finset.mem_image.mp hU
        have hmono {V W : Finset S} (hVW : V ⊆ W) : V.map e ⊆ W.map e := by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
          exact Finset.mem_map.mpr ⟨i, hVW hi, rfl⟩
        rcases hchainC T' hT' U' hU' with h | h
        · exact Or.inl (hmono h)
        · exact Or.inr (hmono h)
      let j : J := ⟨M, (fun T hT => hK.mem_toFinset.mpr (hMK T hT)), hMchain⟩
      refine ⟨j, ?_⟩
      rw [hspace j, hP j]
      have himage : (fun U : Finset S => U.centroid ℝ (fun i : S => i.val)) '' (↑C : Set (Finset S)) ⊆
          (fun T : Finset E => T.centroid ℝ id) '' (↑M : Set (Finset E)) := by
        rintro x ⟨U, hU, hUx⟩
        exact ⟨U.map e, Finset.mem_image.mpr ⟨U, hU, rfl⟩, (U.centroid_map ℝ e id).trans hUx⟩
      exact hw ▸ convexHull_mono himage hcover

end HodgeLean.Foundations.Program
