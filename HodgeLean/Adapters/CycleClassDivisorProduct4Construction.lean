import HodgeLean.Adapters.CycleClassDivisorProduct4Defs

/-! # The supported comparison and cup construction

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Rational linear upgrade of the supported additive comparison.
Source: `supportedSingularClass` and rational linearity of additive maps. -/
def ccm16_supportedLinearEquiv (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    H_[S]^n(X; ℚ) ≃ₗ[ℚ]
      RelativeCohomology ℚ (neighborhoodSupportComplementPair Set.univ
        (S : Set (ComplexPoint X))) n :=
  (supportedSingularClass X S n).linearEquiv ℚ

attribute [local irreducible] ccm4_supportHModule ccm16_supportedLinearEquiv

/-- Supported sheaf classes as relative classes in the ordinary ambient space.
Source: Iversen, Cohomology of Sheaves, II.9 and III; Bredon, Sheaf Theory, II. -/
def ccm16_supportedComparison (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    H_[S]^n(X; ℚ) ≃ₗ[ℚ]
      RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
        (S : Set (ComplexPoint X))ᶜ) n :=
  (ccm16_supportedLinearEquiv X S n).trans
    (ccm16_pairTransport (TopCat.of (ComplexPoint X)) S n)

attribute [local irreducible] ccm16_supportedComparison

/-- The supported cup is the inverse comparison applied to the relative cup.
Source: Bredon, Sheaf Theory, VI, products with supports; Hatcher, §3.2. -/
def ccm16_supportedCup (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (p q : ℕ) :
    H_[S]^p(X; ℚ) →ₗ[ℚ] H_[T]^q(X; ℚ) →ₗ[ℚ] H_[S ⊓ T]^(p + q)(X; ℚ) :=
  ((ccm15_relativeCup (TopCat.of (ComplexPoint X)) S T p q).compl₁₂
    (ccm16_supportedComparison X S p).toLinearMap
    (ccm16_supportedComparison X T q).toLinearMap).compr₂
    (ccm16_supportedComparison X (S ⊓ T) (p + q)).symm.toLinearMap

end HodgeLean.Adapters
