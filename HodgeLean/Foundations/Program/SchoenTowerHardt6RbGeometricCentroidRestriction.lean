import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGeometricCentroidIntersection

/-! Exact geometric base-face restriction of a centroid-chain simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_geometric_centroid_chain_restriction {E : Type*}
    [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (S V : Finset E) (hS : AffineIndependent ℝ (fun i : S => i.val)) (hVS : V ⊆ S)
    (C : Finset (Finset E)) (hsub : ∀ T ∈ C, T ⊆ S) (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E))) ∩
        convexHull ℝ (↑V : Set E) =
      convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) ''
        (↑(C.filter (fun T => T ⊆ V)) : Set (Finset E))) := by
  classical
  let r : Finset E → Finset S := fun T => Finset.univ.filter (fun i => i.val ∈ T)
  obtain ⟨hneF, hchainF, hF⟩ := s2v_hardt6rb_centroid_chain_reindex S C hsub hne hchain
  have hsub' : ∀ T ∈ C.filter (fun T => T ⊆ V), T ⊆ S :=
    fun T hT => hsub T (Finset.mem_filter.mp hT).1
  have hne' : ∀ T ∈ C.filter (fun T => T ⊆ V), T.Nonempty :=
    fun T hT => hne T (Finset.mem_filter.mp hT).1
  have hchain' : ∀ T ∈ C.filter (fun T => T ⊆ V), ∀ U ∈ C.filter (fun T => T ⊆ V), T ⊆ U ∨ U ⊆ T :=
    fun T hT U hU => hchain T (Finset.mem_filter.mp hT).1 U (Finset.mem_filter.mp hU).1
  obtain ⟨_, _, hF'⟩ := s2v_hardt6rb_centroid_chain_reindex S (C.filter (fun T => T ⊆ V))
    hsub' hne' hchain'
  have hV := (s2v_hardt6rb_centroid_subtype S V hVS).1
  have hfilter : (C.image r).filter (fun I => I ⊆ r V) = (C.filter (fun T => T ⊆ V)).image r := by
    ext I
    constructor
    · intro hI
      obtain ⟨hIC, hIV⟩ := Finset.mem_filter.mp hI
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hIC
      have himage : (fun i : S => i.val) '' (↑(r T) : Set S) ⊆
          (fun i : S => i.val) '' (↑(r V) : Set S) := Set.image_mono (Finset.coe_subset.mpr hIV)
      have hTcoord := (s2v_hardt6rb_centroid_subtype S T (hsub T hT)).1
      have hTV : T ⊆ V := Finset.coe_subset.mp (by
        simpa only [r, hTcoord, hV] using himage)
      exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr ⟨hT, hTV⟩, rfl⟩
    · intro hI
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
      obtain ⟨hTC, hTV⟩ := Finset.mem_filter.mp hT
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨T, hTC, rfl⟩, ?_⟩
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTV (Finset.mem_filter.mp hi).2⟩
  have hi := s2v_hardt6rb_centroid_chain_restriction (fun i : S => i.val) hS
    (C.image r) hneF hchainF (r V)
  rw [hfilter] at hi
  simpa only [r, hF, hV, hF'] using hi

end HodgeLean.Foundations.Program
