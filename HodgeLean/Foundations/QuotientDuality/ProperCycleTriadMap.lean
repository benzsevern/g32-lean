import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVCapDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapCocycleNaturality
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # Actual triad chain maps induced by continuous maps of both subspaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual map preserving both subspaces commutes with the original two-summand subspace chain map.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, maps of triads.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_subspace_map_square
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    biprod.map
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetHom f hA))) (ModuleCat.of ℚ ℚ))
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetHom f hB))) (ModuleCat.of ℚ ℚ)) ≫
        triadSubspaceChainMap ℚ Y C D =
      triadSubspaceChainMap ℚ X A B ≫ SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) := by
  apply biprod.hom_ext'
  · simp only [triadSubspaceChainMap, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
    exact ((chainPairFunctor ℚ).map (TopPair.ofSubsetHom f hA)).w
  · simp only [triadSubspaceChainMap, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
    exact ((chainPairFunctor ℚ).map (TopPair.ofSubsetHom f hB)).w

/-- A map preserving both actual subspaces induces the original map between the sum-relative triad chain quotients.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, functorial relative triad chains.
HC no distance; AV milestone no distance. -/
def properCycle_triad_relative_chain_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    triadRelativeChainComplex ℚ X A B ⟶ triadRelativeChainComplex ℚ Y C D :=
  cokernel.map (triadSubspaceChainMap ℚ X A B) (triadSubspaceChainMap ℚ Y C D)
    (biprod.map
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetHom f hA))) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.snd (TopPair.ofSubsetHom f hB))) (ModuleCat.of ℚ ℚ)))
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))
    (properCycle_triad_subspace_map_square f A B C D hA hB).symm

/-- The actual map of triad quotients retains the original ambient singular-chain projection square.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, natural relative projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_relative_chain_projection_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    triadRelativeChainProjection ℚ X A B ≫ properCycle_triad_relative_chain_map f A B C D hA hB =
      SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) ≫
        triadRelativeChainProjection ℚ Y C D := by
  simp [properCycle_triad_relative_chain_map, triadRelativeChainProjection]

end HodgeLean.Foundations.QuotientDuality
