import HodgeLean.Foundations.QuotientDuality.ProperCycleChainSheafSections
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # Original supported singular chains vanish on disjoint open chain sections
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual chain section comparison sends original singular chains in a support to zero on any open disjoint from that support.
Source: subspaceChainMap_relativeChainProjection; TopPair.Homotopy.relativeChainProjection_naturality; properCycle_chain_sheaf_section_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_supported_chain_sheaf_section_zero
    (X : TopCat.{0}) (S : Set X) (U : Opens X) (hSU : S ⊆ (U : Set X)ᶜ) :
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)).map
        (((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) S)).hom) ≫
      properCycle_chain_sheaf_section_map X U = 0 := by
  let P := TopPair.ofSubset (X := X) S
  let Q := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  let f : P ⟶ Q := TopPair.ofSubsetHom (𝟙 X) hSU
  let C := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  have hn := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f
  change relativeChainProjection ℚ P ≫ (relativeChainFunctor ℚ).map f =
    C.map (𝟙 X) ≫ relativeChainProjection ℚ Q at hn
  rw [C.map_id, Category.id_comp] at hn
  have hz : ((chainPairFunctor ℚ).obj P).hom ≫ relativeChainProjection ℚ Q = 0 := by
    rw [← hn, ← Category.assoc, subspaceChainMap_relativeChainProjection, zero_comp]
  let F := (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (.down ℕ)
  change F.map (((chainPairFunctor ℚ).obj P).hom) ≫ (F.map (relativeChainProjection ℚ Q) ≫ _) = 0
  rw [← Category.assoc, ← F.map_comp, hz, F.map_zero, zero_comp]

end HodgeLean.Foundations.QuotientDuality
