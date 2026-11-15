import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual complex manifold chart classes are restrictions of one
absolute integral fundamental class in complex dimension one. -/
theorem s2e_c1_manifold_one_absolute_orientation
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin 1 → ℂ) M] [IsManifold 𝓘(ℂ, Fin 1 → ℂ) 1 M] :
    ∃ w : Homology ℤ (TopCat.of M) 2, ∀ x : M,
      (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom w =
        b6m_manifoldLocalClass ℤ 1 x := by
  let P := TopPair.ofSubset (X := TopCat.of M)
    (((⊤ : TopologicalSpace.Opens M) : Set M)ᶜ)
  haveI : IsEmpty P.snd := by
    change IsEmpty ↥(((⊤ : TopologicalSpace.Opens M) : Set M)ᶜ)
    rw [TopologicalSpace.Opens.coe_top, Set.compl_univ]
    infer_instance
  obtain ⟨w, hw⟩ := b6m_manifold_globalOrientation ℤ 1 (M := M)
  obtain ⟨a, ha⟩ := (b6m_relativeHomologyProjection_bijective_of_isEmpty ℤ P 2).2 w
  refine ⟨a, fun x => ?_⟩
  have h := b6m_relativeHomologyProjection_support ℤ (TopCat.of M)
    (Set.singleton_subset_iff.mpr (TopologicalSpace.Opens.mem_top x)) 2 a
  rw [ha] at h
  exact h.symm.trans (hw x)

/-- On a connected compact complex curve, the absolute integral orientation
class generates the full top homology group. -/
theorem s2e_c1_manifold_one_fundamental_generator
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (Fin 1 → ℂ) M] [IsManifold 𝓘(ℂ, Fin 1 → ℂ) 1 M] :
    ∃ w : Homology ℤ (TopCat.of M) 2,
      (∀ x : M, (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom w =
        b6m_manifoldLocalClass ℤ 1 x) ∧ Function.Bijective (fun r : ℤ => r • w) := by
  obtain ⟨w, hw⟩ := s2e_c1_manifold_one_absolute_orientation M
  have hgen := b6m_absolute_topHomology_generated_by_point_generators ℤ
    (E := Fin 1 → ℂ) (by simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]) w
    (fun x => by
      rw [hw x]
      exact b6m_localClassOfChart_one_smul_bijective ℤ (chartAt (Fin 1 → ℂ) x) x
        (mem_chart_source _ x))
  refine ⟨w, hw, ?_⟩
  convert hgen using 1
  funext r
  exact (Int.cast_smul_eq_zsmul ℤ r w).symm

end HodgeLean.Foundations.Program
