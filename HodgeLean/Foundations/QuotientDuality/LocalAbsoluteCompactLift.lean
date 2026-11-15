import HodgeLean.Foundations.QuotientDuality.LocalChainSupport

/-! Absolute singular homology classes lift from compact subsets. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem absolute_homology_compact_lift (X : TopCat.{0}) (n : ℕ)
    (a : Homology ℚ X n) :
    ∃ (K : Set X), IsCompact K ∧ ∃ b : Homology ℚ (TopCat.of K) n,
      homologyMap ℚ n (TopPair.ofSubset (X := X) K).map b = a := by
  classical
  let C := SingularChainComplex ℚ X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance a
  let c := (C.iCycles n).hom z
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp
    (C_chain_mem_iSup_range (TopCat.toSSet.obj X) n c)
  let K : Set X := ⋃ σ ∈ s, Set.range (X.toSSetObjEquiv _ σ)
  have hK : IsCompact K := s.isCompact_biUnion
    (fun σ _ => isCompact_range (X.toSSetObjEquiv _ σ).continuous)
  let P := TopPair.ofSubset (X := X) K
  let D := ((chainPairFunctor ℚ).obj P).left
  let F := ((chainPairFunctor ℚ).obj P).hom
  have hc : c ∈ LinearMap.range (F.f n).hom := by
    suffices H : (⨆ σ ∈ s, LinearMap.range
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom) ≤
        LinearMap.range (F.f n).hom from H hs
    refine iSup₂_le fun σ hσ => ?_
    rintro _ ⟨r, rfl⟩
    exact C_simplex_mem_range K σ (fun t => by
      simp only [K, Set.mem_iUnion, Set.mem_range]
      exact ⟨σ, hσ, t, rfl⟩) r
  obtain ⟨b, hb⟩ := hc
  let j := (ComplexShape.down ℕ).next n
  have hcyc : ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ b) ≫ D.d n j = 0 := by
    ext : 1
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    letI : Mono F := relativeChainMap_mono ℚ P
    apply (ModuleCat.mono_iff_injective (F.f j)).mp inferInstance
    rw [map_zero]
    have H := congrArg (fun g => g.hom b) (F.comm n j).symm
    change (F.f j).hom ((D.d n j).hom b) = (C.d n j).hom ((F.f n).hom b) at H
    rw [H, hb]
    exact congrArg (fun g => g.hom z) (C.iCycles_d n j)
  let l := D.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ b)) j rfl hcyc
  refine ⟨K, hK, (D.homologyπ n).hom (l.hom 1), ?_⟩
  change (HomologicalComplex.homologyMap F n).hom ((D.homologyπ n).hom (l.hom 1)) = a
  have H := congrArg (fun g => g.hom (l.hom 1))
    (HomologicalComplex.homologyπ_naturality F n).symm
  change (C.homologyπ n).hom ((HomologicalComplex.cyclesMap F n).hom (l.hom 1)) =
    (HomologicalComplex.homologyMap F n).hom ((D.homologyπ n).hom (l.hom 1)) at H
  rw [← H, ← hz]
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  have H1 := congrArg (fun g => g.hom (l.hom 1)) (HomologicalComplex.cyclesMap_i F n)
  change (C.iCycles n).hom ((HomologicalComplex.cyclesMap F n).hom (l.hom 1)) =
    (F.f n).hom ((D.iCycles n).hom (l.hom 1)) at H1
  rw [H1]
  have H2 := congrArg (fun g => g.hom 1)
    (D.liftCycles_i (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ b)) j rfl hcyc)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at H2
  erw [LinearMap.toSpanSingleton_apply_one] at H2
  have H2' : (D.iCycles n).hom (l.hom 1) = b := H2
  rw [H2']
  exact hb

#print axioms absolute_homology_compact_lift
end HodgeLean.Foundations.QuotientDuality
