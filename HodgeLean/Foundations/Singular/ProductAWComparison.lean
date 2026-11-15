import HodgeLean.Foundations.Singular.ProductAWBoundary
import HodgeLean.Foundations.Singular.ProductAWNaturality

/-! The actual Alexander–Whitney rational chain comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The specified Alexander–Whitney chain map from actual product chains to actual total tensor chains.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney chain map. -/
def productAlexanderWhitney (X Y : TopCat.{0}) :
    rationalChains (TopCat.of (X × Y)) ⟶ rationalTensorChains X Y where
  f n := ModuleCat.ofHom (productAlexanderWhitneyDegree X Y n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact (productAlexanderWhitneyDegree_boundary X Y j).symm

/-- The specified Alexander–Whitney chain comparison is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the Alexander–Whitney map. -/
theorem productAlexanderWhitney_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    rationalChainMap (topologicalProductMap f g) ≫ productAlexanderWhitney X' Y' =
      productAlexanderWhitney X Y ≫ rationalTensorChainMap f g := by
  apply HomologicalComplex.hom_ext
  intro n
  exact productAlexanderWhitneyDegree_naturality f g n

#print axioms productAlexanderWhitney_naturality
#print axioms productAlexanderWhitney
end HodgeLean.Foundations.Singular
