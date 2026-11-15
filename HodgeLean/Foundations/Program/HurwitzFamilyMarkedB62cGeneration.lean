import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cChains

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homologyClass_zero_iff (R : Type) [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R)) (z : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyClass z = 0 ↔ z.1 ∈ LinearMap.range S.f.hom := by
  change S.moduleCatHomologyIso.toLinearEquiv.symm
    ((LinearMap.range S.moduleCatToCycles).mkQ z) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨x, Subtype.ext hx⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homology_chain_embedding (T : Type) [TopologicalSpace T] :
    ∃ j : b6m_H1 T →ₗ[ℤ] b6m_chainQuotient (TopCat.toSSet.obj (TopCat.of T)),
      Function.Injective j ∧
      ∀ z : LinearMap.ker ((SingularChainComplex ℤ (TopCat.of T)).sc 1).g.hom,
        j (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass z) =
          b6m_chainQuotientMap _ z.1 := by
  let Y := TopCat.toSSet.obj (TopCat.of T)
  let S := (SingularChainComplex ℤ (TopCat.of T)).sc 1
  let φ : S.X₂ →ₗ[ℤ] b6m_chainQuotient Y :=
    { toFun := b6m_chainQuotientMap Y
      map_add' := (b6m_chainQuotientMap Y).map_add
      map_smul' := by
        intro n c
        change b6m_chainQuotientMap Y (S.X₂.isModule.smul n c) = n • b6m_chainQuotientMap Y c
        rw [int_smul_eq_zsmul]
        exact map_zsmul (b6m_chainQuotientMap Y) n c }
  have hφ : φ.comp S.f.hom = 0 := by
    change φ.comp ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d
      ((ComplexShape.down ℕ).prev 1) 1).hom = 0
    rw [ChainComplex.prev]
    ext c
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨c, rfl⟩
  obtain ⟨j, hj⟩ := b6m_descIntegralCocycle ℤ S (b6m_chainQuotient Y) φ hφ
  have h0 : ∀ x, j x = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := S.moduleCatHomologyClass_surjective x
    have hzq : b6m_chainQuotientMap Y z.1 = 0 := (hj z).symm.trans hx
    have hz := (QuotientAddGroup.eq_zero_iff z.1).mp hzq
    apply (b6m_homologyClass_zero_iff ℤ S z).mpr
    change z.1 ∈ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d
      ((ComplexShape.down ℕ).prev 1) 1).hom.range
    rw [ChainComplex.prev]
    exact hz
  refine ⟨j, ?_, hj⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply h0
  exact (map_sub j x y).trans (sub_eq_zero.mpr hxy)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_continuous_loops_span (T : Type) [TopologicalSpace T] [PathConnectedSpace T] :
    Submodule.span ℤ (Set.range (fun p : C(UnitAddCircle, T) ↦
      ((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass (loopCycle ℤ p))) =
        (⊤ : Submodule ℤ (b6m_H1 T)) := by
  let Y := TopCat.toSSet.obj (TopCat.of T)
  let S := (SingularChainComplex ℤ (TopCat.of T)).sc 1
  let L : Submodule ℤ (b6m_H1 T) := Submodule.span ℤ (Set.range
    (fun p : C(UnitAddCircle, T) ↦ S.moduleCatHomologyClass (loopCycle ℤ p)))
  obtain ⟨j, hj, hJ⟩ := b6m_homology_chain_embedding T
  have hle : Submodule.span ℤ (Set.range (fun p : C(UnitAddCircle, T) ↦
      b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ (loopSimplex p)))) ≤ L.map j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨S.moduleCatHomologyClass (loopCycle ℤ p), Submodule.subset_span ⟨p, rfl⟩,
        hJ (loopCycle ℤ p)⟩
  change L = ⊤
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := S.moduleCatHomologyClass_surjective x
  have hcycle : Simplicial.boundary ℤ 0 z.1 = 0 := by
    have h := z.2
    change ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d 1
      ((ComplexShape.down ℕ).next 1)).hom z.1 = 0 at h
    rw [ChainComplex.next_nat_succ] at h
    exact h
  obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp (hle (b6m_cycle_chain_span T z.1 hcycle))
  have hyx : y = x := hj (heq.trans ((hJ z).symm.trans (congrArg j hz)))
  exact hyx ▸ hy

open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem b6m_smooth_loops_span (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    Submodule.span ℤ (Set.range (b6m_loopClass C)) = ⊤ := by
  have : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ℂ C
  have : PathConnectedSpace C := PathConnectedSpace.of_locallyPathConnectedSpace
  apply top_unique
  rw [← b6m_continuous_loops_span C]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  obtain ⟨γ, hγ⟩ := b6m_exists_integral_smoothLoop C p
  have hmem : b6m_loopClass C γ ∈ Submodule.span ℤ (Set.range (b6m_loopClass C)) :=
    Submodule.subset_span ⟨γ, rfl⟩
  exact (congrArg (fun x : b6m_H1 C ↦
    x ∈ Submodule.span ℤ (Set.range (b6m_loopClass C))) hγ).mp hmem

theorem b6m_period_evaluation_mem (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ))
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ)
    (x : b6m_H1 C) : P x ∈ b3_periodLattice ℂ C := by
  have hle : Submodule.span ℤ (Set.range (b6m_loopClass C)) ≤
      (b3_periodLattice ℂ C).toIntSubmodule.comap P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, rfl⟩
    change P (b6m_loopClass C γ) ∈ b3_periodLattice ℂ C
    rw [hP]
    exact AddSubgroup.subset_closure ⟨γ, rfl⟩
  rw [b6m_smooth_loops_span C] at hle
  exact hle (Submodule.mem_top : x ∈ ⊤)

theorem b6m_period_lattice_map_exists (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C, Function.Surjective P ∧
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ := by
  obtain ⟨P, hP⟩ := b6m_period_evaluation_exists C
  let Q : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C :=
    { toFun := fun x ↦ ⟨P x, b6m_period_evaluation_mem C P hP x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add P x y)
      map_smul' := fun n x ↦ Subtype.ext (P.map_smul n x) }
  have hQ : ∀ γ : b3_SmoothLoop ℂ C, Q (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ :=
    fun γ ↦ Subtype.ext (hP γ)
  exact ⟨Q, b6m_period_map_surjective C Q hQ, hQ⟩

theorem b6m_homology_linearMap_ext (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (M : Type*) [AddCommGroup M] [Module ℤ M] (P Q : b6m_H1 C →ₗ[ℤ] M)
    (h : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = Q (b6m_loopClass C γ)) :
    P = Q :=
  LinearMap.ext_on_range (b6m_smooth_loops_span C) h

theorem b6m_homology_bilin_ext (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (Q R : LinearMap.BilinForm ℤ (b6m_H1 C))
    (h : ∀ γ δ : b3_SmoothLoop ℂ C,
      Q (b6m_loopClass C γ) (b6m_loopClass C δ) =
        R (b6m_loopClass C γ) (b6m_loopClass C δ)) : Q = R := by
  apply b6m_homology_linearMap_ext C
  intro γ
  exact b6m_homology_linearMap_ext C ℤ _ _ (h γ)

end HodgeLean.Foundations.Program
