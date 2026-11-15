import HodgeLean.Adapters.CycleClassDivisorProduct4Proofs

/-! # Supported cup and normalized forget-support law: frozen specification

Implication from smoothness, projectivity and integrality: the supported cup
constructed from relative singular cup agrees after forgetting support with
the actual cupProductOf. The raw unit and raw forget-support comparisons are
separate open obligations. No local orientation or intersection law is claimed.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

/-- The unnormalized sheaf comparison preserves the actual constant unit.
Source: Bredon, Sheaf Theory, II and III.1; Iversen, Cohomology of Sheaves,
II.9 and III, comparison through the constants-to-singular resolution. -/
theorem ccm16_rawComparison_unit (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalCohomologyLinearEquivSingular X 0 (HQ.linearEquiv X 0 (cupUnit X)) =
      Singular.unit (TopCat.of (ComplexPoint X)) :=
  ccm16_rawComparison_unit_aux X

/-- The supported injective comparison commutes with the actual forget-support map.
Source: Bredon, Sheaf Theory, II, relative cohomology; Iversen, Cohomology of
Sheaves, II.9 and III, naturality of resolution comparisons. -/
theorem ccm16_supportedComparison_forget (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) (u : H_[S]^n(X; ℚ)) :
    relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X))ᶜ) n
        (ccm16_supportedComparison X S n u) =
      rationalCohomologyLinearEquivSingular X n
        (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X S n u) :=
  ccm16_supportedComparison_forget_aux X S n u

/-- Forgetting support intertwines the constructed product with actual cupProductOf.
Source: Hatcher, Algebraic Topology, §3.2; Bredon, Sheaf Theory, VI, products
with supports; the separate raw-unit and forget-support obligations above. -/
theorem ccm16_supportedCup_forget (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (p q : ℕ)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ)) :
    (HQ.linearEquiv X (p + q)).symm
      (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X (S ⊓ T) (p + q)
        (ccm16_supportedCup X S T p q u v)) =
      (cupProductOf X).cup rfl
        ((HQ.linearEquiv X p).symm
          (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X S p u))
        ((HQ.linearEquiv X q).symm
          (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X T q v)) :=
  ccm16_supportedCup_forget_aux X S T p q u v

end HodgeLean.Adapters
