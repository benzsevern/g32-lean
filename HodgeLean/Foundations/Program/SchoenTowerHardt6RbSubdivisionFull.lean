import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGlobalSubdivision
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidSubcomplex

/-! The induced centroid subdivision of every original subcomplex is full. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_subdivision_subcomplex_full {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (hDK : D.faces ⊆ K.faces)
    (L : Geometry.SimplicialComplex ℝ E)
    (hL : ∀ s, s ∈ L.faces ↔ ∃ C : Finset (Finset E),
      (∀ T ∈ C, T ∈ K.faces) ∧
      (∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) ∧
      (↑s : Set E) ⊆ (fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E)) ∧ s.Nonempty) :
    ∃ M : Geometry.SimplicialComplex ℝ E, M.faces.Finite ∧ M.faces ⊆ L.faces ∧
      M.space = D.space ∧
      (∀ s ∈ L.faces, (∀ x ∈ s, x ∈ M.vertices) → s ∈ M.faces) := by
  classical
  obtain ⟨M, hMfinite, hM, hMspace⟩ := s2v_hardt6rb_centroid_subdivision D (hK.subset hDK)
  have hsub : M.faces ⊆ L.faces := by
    intro s hs
    obtain ⟨C, hCD, hchain, hset, hne⟩ := (hM s).mp hs
    exact (hL s).mpr ⟨C, (fun T hT => hDK (hCD T hT)), hchain, hset, hne⟩
  refine ⟨M, hMfinite, hsub, hMspace, ?_⟩
  intro s hs hvertices
  obtain ⟨C, hCK, hchain, hset, hne⟩ := (hL s).mp hs
  let C' := C.filter (fun T => T.centroid ℝ id ∈ s)
  have hCD : ∀ T ∈ C', T ∈ D.faces := by
    intro T hT
    obtain ⟨hTC, hTs⟩ := Finset.mem_filter.mp hT
    have hxM : T.centroid ℝ id ∈ M.space := M.vertices_subset_space (hvertices _ hTs)
    have hxD : T.centroid ℝ id ∈ D.space := by simpa only [hMspace] using hxM
    exact (s2v_hardt6rb_centroid_mem_subcomplex_iff K D hDK T (hCK T hTC)).mp hxD
  have hchain' : ∀ T ∈ C', ∀ U ∈ C', T ⊆ U ∨ U ⊆ T :=
    fun T hT U hU => hchain T (Finset.mem_filter.mp hT).1 U (Finset.mem_filter.mp hU).1
  apply (hM s).mpr
  refine ⟨C', hCD, hchain', ?_, hne⟩
  intro x hx
  obtain ⟨T, hT, hTx⟩ := hset hx
  refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩, hTx⟩
  change T.centroid ℝ id = x at hTx
  rw [hTx]
  exact hx

end HodgeLean.Foundations.Program
