import HodgeLean.Foundations.QuotientDuality.ProperCycleEvenCapHomology
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # Original sum-relative triad complexes under enlargement of the second subspace -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Enlarging the second actual triad subspace preserves the literal two-summand subspace chain map under the original inclusion square.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, relative chain quotients and naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_subspace_inclusion_square
    (X : TopCat.{0}) (A B C : Set X) (hBC : B ⊆ C) :
    biprod.map
        (𝟙 (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).left))
        (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map
          (TopPair.Hom.snd (TopPair.ofSubsetHom (𝟙 X) (fun _ hz => hBC hz)))) ≫
      triadSubspaceChainMap ℚ X A C = triadSubspaceChainMap ℚ X A B := by
  let F := (singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  have hj : F.map (TopPair.Hom.snd (TopPair.ofSubsetHom (𝟙 X) (fun _ hz => hBC hz))) ≫
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) C)).hom =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) B)).hom := by
    change F.map (TopPair.Hom.snd (TopPair.ofSubsetHom (𝟙 X) (fun _ hz => hBC hz))) ≫
      F.map (TopPair.ofSubset (X := X) C).map = F.map (TopPair.ofSubset (X := X) B).map
    rw [← F.map_comp]
    rfl
  change biprod.map _ _ ≫ biprod.desc _ _ = biprod.desc _ _
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc, Category.id_comp]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc]
    exact hj

/-- Enlarge the second actual triad subspace by the canonical map between the original chain cokernels.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, relative chain quotient maps.
HC no distance; AV milestone no distance. -/
def properCycle_triad_inclusion_chain_map
    (X : TopCat.{0}) (A B C : Set X) (hBC : B ⊆ C) :
    triadRelativeChainComplex ℚ X A B ⟶ triadRelativeChainComplex ℚ X A C :=
  cokernel.desc (triadSubspaceChainMap ℚ X A B) (triadRelativeChainProjection ℚ X A C) (by
    rw [← properCycle_triad_subspace_inclusion_square X A B C hBC, Category.assoc,
      triadSubspaceChainMap_triadRelativeChainProjection, comp_zero])

/-- The actual quotient map for triad enlargement commutes with the literal original ambient chain projections.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of relative chain quotients.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_projection_inclusion
    (X : TopCat.{0}) (A B C : Set X) (hBC : B ⊆ C) :
    triadRelativeChainProjection ℚ X A B ≫ properCycle_triad_inclusion_chain_map X A B C hBC =
      triadRelativeChainProjection ℚ X A C := by
  exact cokernel.π_desc _ _ _

end HodgeLean.Foundations.QuotientDuality
