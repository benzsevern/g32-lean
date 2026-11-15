import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGeneration

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters

theorem b6m_loopChain_rebase (T : Type) [TopologicalSpace T] [PathConnectedSpace T]
    (a : T) (p : C(UnitAddCircle, T)) :
    ∃ g : Path a a, b6m_pathChain g.toContinuousMap =
      b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p)) := by
  let c : Path (p 0) (p 0) :=
    { toContinuousMap := simplexPath (loopSimplex p)
      source' := by
        rw [spec_simplexPath_loopSimplex]
        change p ((0 : ℝ) : UnitAddCircle) = p 0
        simp
      target' := by
        rw [spec_simplexPath_loopSimplex]
        change p ((1 : ℝ) : UnitAddCircle) = p 0
        rw [AddCircle.coe_period] }
  let q := PathConnectedSpace.somePath a (p 0)
  refine ⟨(q.trans c).trans q.symm, ?_⟩
  rw [b6m_pathChain_trans, b6m_pathChain_trans, b6m_pathChain_symm]
  have hc : b6m_pathChain c.toContinuousMap =
      b6m_chainQuotientMap _ (Simplicial.chainOfSimplex ℤ (loopSimplex p)) := by
    simp only [c, b6m_pathChain, b3Rest2_pathSimplex_simplexPath (T := T)]
  rw [hc]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem b6m_continuous_loopClass_surjective (T : Type) [TopologicalSpace T]
    [PathConnectedSpace T] :
    Function.Surjective (fun p : C(UnitAddCircle, T) ↦
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
        (loopCycle ℤ p)) := by
  let Y := TopCat.toSSet.obj (TopCat.of T)
  let S := (SingularChainComplex ℤ (TopCat.of T)).sc 1
  let a : T := Classical.choice inferInstance
  let L : AddSubgroup (b6m_chainQuotient Y) :=
    { carrier := Set.range (fun g : Path a a ↦ b6m_pathChain g.toContinuousMap)
      zero_mem' := ⟨Path.refl a, b6m_pathChain_const a⟩
      add_mem' := by
        rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨g.trans h, b6m_pathChain_trans g h⟩
      neg_mem' := by
        rintro _ ⟨g, rfl⟩
        exact ⟨g.symm, b6m_pathChain_symm g⟩ }
  obtain ⟨j, hj, hJ⟩ := b6m_homology_chain_embedding T
  have hle : Submodule.span ℤ (Set.range (fun p : C(UnitAddCircle, T) ↦
      S.moduleCatHomologyClass (loopCycle ℤ p))) ≤ L.toIntSubmodule.comap j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change j (S.moduleCatHomologyClass (loopCycle ℤ p)) ∈ L
    rw [hJ]
    exact b6m_loopChain_rebase T a p
  rw [b6m_continuous_loops_span T] at hle
  intro x
  have hx : j x ∈ L := hle trivial
  obtain ⟨g, hg⟩ := hx
  obtain ⟨p, hp⟩ := b6m_pathChain_loop g
  refine ⟨p, hj ?_⟩
  rw [hJ]
  exact hp.symm.trans hg

open scoped Manifold ContDiff

theorem b6m_smooth_loopClass_surjective (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] : Function.Surjective (b6m_loopClass C) := by
  letI : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ℂ C
  letI : PathConnectedSpace C := PathConnectedSpace.of_locallyPathConnectedSpace
  intro x
  obtain ⟨p, hp⟩ := b6m_continuous_loopClass_surjective C x
  obtain ⟨γ, hγ⟩ := b6m_exists_integral_smoothLoop C p
  exact ⟨γ, hγ.trans hp⟩

end HodgeLean.Foundations.Program
