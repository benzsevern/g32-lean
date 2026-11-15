import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidSubtype

/-! Canonical subtype reindexing of geometric centroid chains preserves their actual vertex sets. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_reindex {E : Type*}
    [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (S : Finset E) (C : Finset (Finset E))
    (hsub : ∀ T ∈ C, T ⊆ S) (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    let r : Finset E → Finset S := fun T => Finset.univ.filter (fun i => i.val ∈ T)
    let F := C.image r
    (∀ T ∈ F, T.Nonempty) ∧
      (∀ T ∈ F, ∀ U ∈ F, T ⊆ U ∨ U ⊆ T) ∧
      (fun T : Finset S => T.centroid ℝ (fun i : S => i.val)) '' (↑F : Set (Finset S)) =
        (fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E)) := by
  classical
  intro r F
  have hcoords (T : Finset E) (hT : T ∈ C) := s2v_hardt6rb_centroid_subtype S T (hsub T hT)
  have hmono {T U : Finset E} (hTU : T ⊆ U) : r T ⊆ r U := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTU (Finset.mem_filter.mp hi).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨x, hx⟩ := hne U hU
    exact ⟨⟨x, hsub U hU hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  · intro T hT U hU
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨U', hU', rfl⟩ := Finset.mem_image.mp hU
    rcases hchain T' hT' U' hU' with h | h
    · exact Or.inl (hmono h)
    · exact Or.inr (hmono h)
  · ext x
    constructor
    · rintro ⟨I, hI, rfl⟩
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
      exact ⟨T, hT, (hcoords T hT).2.symm⟩
    · rintro ⟨T, hT, rfl⟩
      exact ⟨r T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, (hcoords T hT).2⟩

end HodgeLean.Foundations.Program
