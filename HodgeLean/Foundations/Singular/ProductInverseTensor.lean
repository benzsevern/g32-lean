import HodgeLean.Foundations.Singular.ProductAWComparison
import HodgeLean.Foundations.Singular.ProductComparison
import HodgeLean.Foundations.Singular.ProductVertexInverse
import HodgeLean.Foundations.Singular.TensorNaturalHomotopy

/-! The inverse homotopy on the actual tensor chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual tensor-chain endomap formed by the two product comparison maps.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
def tensorComparisonComposite (X Y : TopCat.{0}) :
    rationalTensorChains X Y ⟶ rationalTensorChains X Y :=
  tensorProductComparison X Y ≫ productAlexanderWhitney X Y

/-- The tensor-chain comparison composite is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
theorem tensorComparisonComposite_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    rationalTensorChainMap f g ≫ tensorComparisonComposite X' Y' =
      tensorComparisonComposite X Y ≫ rationalTensorChainMap f g := by
  unfold tensorComparisonComposite
  calc
    _ = (rationalTensorChainMap f g ≫ tensorProductComparison X' Y') ≫
        productAlexanderWhitney X' Y' := (Category.assoc _ _ _).symm
    _ = (tensorProductComparison X Y ≫ rationalChainMap (topologicalProductMap f g)) ≫
        productAlexanderWhitney X' Y' := congrArg (fun k => k ≫ productAlexanderWhitney X' Y')
          (tensorProductComparison_naturality f g)
    _ = tensorProductComparison X Y ≫
        (rationalChainMap (topologicalProductMap f g) ≫ productAlexanderWhitney X' Y') :=
          Category.assoc _ _ _
    _ = tensorProductComparison X Y ≫
        (productAlexanderWhitney X Y ≫ rationalTensorChainMap f g) :=
          congrArg (fun k => tensorProductComparison X Y ≫ k) (productAlexanderWhitney_naturality f g)
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual tensor comparison composite is chain homotopic to the identity.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
def tensorComparisonHomotopy (X Y : TopCat.{0}) :
    Homotopy (tensorProductComparison X Y ≫ productAlexanderWhitney X Y)
      (𝟙 (rationalTensorChains X Y)) := by
  apply tensorNaturalChainHomotopy tensorComparisonComposite (fun X Y => 𝟙 _)
    (fun f g => tensorComparisonComposite_naturality f g)
    (fun f g => by simp)
    (fun X Y => ?_) X Y
  apply ModuleCat.hom_ext
  exact AW_after_tensorProductZero X Y

#print axioms tensorComparisonHomotopy
#print axioms tensorComparisonComposite
#print axioms tensorComparisonComposite_naturality
end HodgeLean.Foundations.Singular
