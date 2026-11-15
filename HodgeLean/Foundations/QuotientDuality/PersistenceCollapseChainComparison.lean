import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseExcision
import HodgeLean.Foundations.QuotientDuality.PersistenceHomeomorphPairIso

/-! Actual relative-chain comparison on the enlarged quotient pairs. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_collapse_punctured_relative_chain_quasiIso
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) :
    QuasiIso ((relativeChainFunctor K).map (persistenceCollapsePuncturedPairMap A hA V)) := by
  exact persistence_homeomorph_relative_chain_quasiIso K _
    (persistenceCollapseComplementHomeomorph A hA).isHomeomorph _

lemma persistence_collapse_enlarged_relative_chain_quasiIso
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A : Set X) (hA : IsClosed A)
    (V : Set (Quotient (persistenceCollapseSetoid A))) (hV : IsOpen V)
    (hAV : (Quotient.mk (persistenceCollapseSetoid A)) '' A ⊆ V) :
    QuasiIso ((relativeChainFunctor K).map (persistenceCollapseEnlargedPairMap A V)) := by
  haveI hs : QuasiIso ((relativeChainFunctor K).map
      (persistencePuncturedNeighbourhoodPairMap A
        ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V))) :=
    persistence_punctured_neighbourhood_relative_chain_quasiIso K
      hA (hV.preimage continuous_quotient_mk') (fun x hx => hAV ⟨x, hx, rfl⟩)
  haveI ht := persistence_punctured_neighbourhood_relative_chain_quasiIso K
    (persistence_collapse_isClosedMap A hA A hA) hV hAV
  haveI hm := persistence_collapse_punctured_relative_chain_quasiIso K A hA V
  have heq := congrArg ((relativeChainFunctor K).map) (persistence_collapse_excision_square A hA V)
  rw [Functor.map_comp, Functor.map_comp] at heq
  haveI hc : QuasiIso (((relativeChainFunctor K).map
      (persistencePuncturedNeighbourhoodPairMap A
        ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V))) ≫
      ((relativeChainFunctor K).map (persistenceCollapseEnlargedPairMap A V))) := by
    rw [heq]
    infer_instance
  exact quasiIso_of_comp_left
    ((relativeChainFunctor K).map (persistencePuncturedNeighbourhoodPairMap A
      ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹' V)))
    ((relativeChainFunctor K).map (persistenceCollapseEnlargedPairMap A V))

lemma persistence_collapse_neighbourhood_relative_chain_quasiIso
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor K).map (persistenceCollapseNeighbourhoodPairMap A U)) := by
  let e := persistenceSubsetPairIso (TopCat.of X) U
    ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹'
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U))
    (persistence_collapse_neighbourhood_preimage A U hAU).symm
  have hmap : persistenceCollapseNeighbourhoodPairMap A U = e.hom ≫
      persistenceCollapseEnlargedPairMap A
        ((Quotient.mk (persistenceCollapseSetoid A)) '' U) := by
    apply persistence_pair_hom_ext
    rfl
  haveI hb : QuasiIso ((relativeChainFunctor K).map (persistenceCollapseEnlargedPairMap A
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U))) :=
    persistence_collapse_enlarged_relative_chain_quasiIso K A hA _
      (persistence_collapse_neighbourhood_isOpen A U hAU hU) (Set.image_mono hAU)
  rw [hmap, Functor.map_comp]
  infer_instance

lemma persistence_collapse_neighbourhood_relative_homology_bijective
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) (n : ℕ) :
    Function.Bijective
      (relativeHomologyMap K n (persistenceCollapseNeighbourhoodPairMap A U)) := by
  haveI := persistence_collapse_neighbourhood_relative_chain_quasiIso K A U hA hU hAU
  have hIso : IsIso ((relativeHomologyFunctor K n).map
      (persistenceCollapseNeighbourhoodPairMap A U)) := by
    change IsIso (HomologicalComplex.homologyMap ((relativeChainFunctor K).map
      (persistenceCollapseNeighbourhoodPairMap A U)) n)
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hIso

end HodgeLean.Foundations.QuotientDuality
