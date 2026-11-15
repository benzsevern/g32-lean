import HodgeLean.Foundations.Program.SchoenSelectedGeometryEmbedding

noncomputable section
set_option maxHeartbeats 400000
open Manifold Set
open scoped ContDiff Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem s0_finite_meromorphic_separation
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ T : Finset (b4c_MeroFun ℂ C),
      ∀ x y : C, (∀ F ∈ T, F x = F y) → x = y := by
  classical
  choose F U ho hp hi using fun p : C ↦ s0_meromorphic_locally_injective p
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U ho
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hp x⟩)
  let W : Set (C × C) := ⋃ i ∈ s, U i ×ˢ U i
  have hWo : IsOpen W := isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ (ho i).prod (ho i)
  have hdiag (x : C) : (x, x) ∈ W := by
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact mem_iUnion₂.mpr ⟨i, hi, hx, hx⟩
  let V : b4c_MeroFun ℂ C → Set (C × C) := fun f ↦ {z | f z.1 ≠ f z.2}
  have hVo (f : b4c_MeroFun ℂ C) : IsOpen (V f) :=
    (isClosed_eq (f.property.1.continuous.comp continuous_fst)
      (f.property.1.continuous.comp continuous_snd)).isOpen_compl
  have hcover : Wᶜ ⊆ ⋃ f, V f := by
    intro z hz
    have hne : z.1 ≠ z.2 := by
      intro he
      apply hz
      change (z.1, z.2) ∈ W
      rw [he]
      exact hdiag z.2
    obtain ⟨f, hx, hy⟩ := s0_meromorphic_separates_points z.1 z.2 hne
    refine mem_iUnion.mpr ⟨f, ?_⟩
    exact fun he ↦ hy (he.symm.trans hx)
  obtain ⟨t, ht⟩ := hWo.isClosed_compl.isCompact.elim_finite_subcover V hVo hcover
  refine ⟨s.image F ∪ t, ?_⟩
  intro x y h
  by_cases hw : (x, y) ∈ W
  · obtain ⟨i, his, hx, hy⟩ := mem_iUnion₂.mp hw
    apply hi i hx hy
    exact h (F i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, his, rfl⟩))
  · obtain ⟨f, hft, hf⟩ := mem_iUnion₂.mp (ht hw)
    exact (hf (h f (Finset.mem_union_right _ hft))).elim

#print axioms s0_finite_meromorphic_separation

theorem s0_finite_meromorphic_embedding
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ (n : ℕ) (F : Fin n → b4c_MeroFun ℂ C),
      Topology.IsClosedEmbedding (fun x : C ↦ fun i ↦ F i x) := by
  classical
  obtain ⟨T, hT⟩ := s0_finite_meromorphic_separation (C := C)
  let E := (Fintype.equivFin T).symm
  let F : Fin (Fintype.card T) → b4c_MeroFun ℂ C := fun i ↦ (E i).val
  have hc : Continuous (fun x : C ↦ fun i ↦ F i x) :=
    continuous_pi (fun i ↦ (F i).property.1.continuous)
  refine ⟨Fintype.card T, F, hc.isClosedEmbedding ?_⟩
  intro x y h
  apply hT x y
  intro f hf
  have he := congrFun h ((Fintype.equivFin T) ⟨f, hf⟩)
  simpa only [F, E, Equiv.symm_apply_apply] using he

#print axioms s0_finite_meromorphic_embedding

theorem s0_finite_meromorphic_immersion
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ T : Finset (b4c_MeroFun ℂ C),
      (∀ x y : C, (∀ F ∈ T, F x = F y) → x = y) ∧
      ∀ x : C, ∃ F ∈ T, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0 := by
  classical
  obtain ⟨T, hT⟩ := s0_finite_meromorphic_separation (C := C)
  choose F U ho hp hu using fun x : C ↦ s0_meromorphic_unramified_neighborhood x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U ho
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hp x⟩)
  refine ⟨T ∪ s.image F, ?_, ?_⟩
  · intro x y h
    exact hT x y (fun f hf ↦ h f (Finset.mem_union_left _ hf))
  · intro x
    obtain ⟨i, his, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨F i, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, his, rfl⟩), hu i x hx⟩

#print axioms s0_finite_meromorphic_immersion

end HodgeLean.Foundations.Program
