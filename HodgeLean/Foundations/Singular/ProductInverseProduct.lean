import HodgeLean.Foundations.Singular.ProductNaturalHomotopy
import HodgeLean.Foundations.Singular.ProductInverseTensor

/-! The inverse homotopy on the actual rational product chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual product-chain endomap formed by the two comparison maps.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
def productComparisonComposite (X Y : TopCat.{0}) :
    rationalProductChains X Y ⟶ rationalProductChains X Y :=
  productAlexanderWhitney X Y ≫ tensorProductComparison X Y

/-- The product-chain comparison composite is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
theorem productComparisonComposite_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    rationalProductChainMap f g ≫ productComparisonComposite X' Y' =
      productComparisonComposite X Y ≫ rationalProductChainMap f g := by
  unfold productComparisonComposite
  calc
    _ = (rationalProductChainMap f g ≫ productAlexanderWhitney X' Y') ≫
        tensorProductComparison X' Y' := (Category.assoc _ _ _).symm
    _ = (productAlexanderWhitney X Y ≫ rationalTensorChainMap f g) ≫
        tensorProductComparison X' Y' := congrArg (fun k => k ≫ tensorProductComparison X' Y')
          (productAlexanderWhitney_naturality f g)
    _ = productAlexanderWhitney X Y ≫
        (rationalTensorChainMap f g ≫ tensorProductComparison X' Y') := Category.assoc _ _ _
    _ = productAlexanderWhitney X Y ≫
        (tensorProductComparison X Y ≫ rationalProductChainMap f g) :=
          congrArg (fun k => productAlexanderWhitney X Y ≫ k) (tensorProductComparison_naturality f g)
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual product-chain comparison composite is chain homotopic to the identity.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber comparison. -/
def productComparisonHomotopy (X Y : TopCat.{0}) :
    Homotopy (productAlexanderWhitney X Y ≫ tensorProductComparison X Y)
      (𝟙 (rationalProductChains X Y)) := by
  apply productNaturalChainHomotopy productComparisonComposite (fun X Y => 𝟙 _)
    (fun f g => productComparisonComposite_naturality f g)
    (fun f g => by simp)
    (fun X Y => ?_) X Y
  apply ModuleCat.hom_ext
  exact tensorProductZero_after_AW X Y

#print axioms productComparisonHomotopy
#print axioms productComparisonComposite
#print axioms productComparisonComposite_naturality
end HodgeLean.Foundations.Singular
