import HodgeLean.Foundations.QuotientDuality.RetainedCycleBoundedGlobalChainMap

/-! # Nonzero detection for the literal bounded support chain map -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual bounded support construction retains the nonzero global image of a support chain class. -/
lemma retained_bounded_support_chain_global_nonzero
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (S : Closeds X)
    (N : ℕ) (i : ℤ) (hi : -(N : ℤ)+1 < i)
    (a : ((((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj
      (SingularChainComplex ℚ (TopCat.of (S : Set X)))).extend
        ComplexShape.embeddingDownNat).homology i)
    (ha : (HomologicalComplex.homologyMap (extendMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
        (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom))
          ComplexShape.embeddingDownNat) i).hom a ≠ 0) :
    (HomologicalComplex.homologyMap (properCycle_bounded_support_chain_map X S N ≫
      ((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (properCycle_bounded_chain_sheaf X N).obj) i).hom a ≠ 0 := by
  have hm : properCycle_bounded_support_chain_map X S N ≫
      ((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
        (properCycle_bounded_chain_sheaf X N).obj =
    extendMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
        (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom))
          ComplexShape.embeddingDownNat ≫ retainedBoundedGlobalChainMap X N := by
    rw [retained_bounded_support_forgetting]
    simp only [extendMap_comp, retainedBoundedGlobalChainMap, Category.assoc]
  letI := retained_bounded_global_chain_quasiIsoAt X N i hi
  have hinj := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (retainedBoundedGlobalChainMap X N) i)).1
  rw [hm, HomologicalComplex.homologyMap_comp]
  intro hz
  exact ha (hinj (hz.trans (map_zero _).symm))

/-- A support chain class with nonzero ambient image stays nonzero under the original bounded support map. -/
lemma retained_bounded_support_chain_nonzero
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (S : Closeds X)
    (N : ℕ) (i : ℤ) (hi : -(N : ℤ)+1 < i)
    (a : ((((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj
      (SingularChainComplex ℚ (TopCat.of (S : Set X)))).extend
        ComplexShape.embeddingDownNat).homology i)
    (ha : (HomologicalComplex.homologyMap (extendMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map
        (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (S : Set X))).hom))
          ComplexShape.embeddingDownNat) i).hom a ≠ 0) :
    (HomologicalComplex.homologyMap (properCycle_bounded_support_chain_map X S N) i).hom a ≠ 0 := by
  have hn := retained_bounded_support_chain_global_nonzero X S N i hi a ha
  intro hz
  apply hn
  rw [HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap
    (((retainedSupportForgetting X S).mapHomologicalComplex (.up ℤ)).app
      (properCycle_bounded_chain_sheaf X N).obj) i).hom
    ((HomologicalComplex.homologyMap (properCycle_bounded_support_chain_map X S N) i).hom a) = 0
  rw [hz, map_zero]

end HodgeLean.Foundations.QuotientDuality
