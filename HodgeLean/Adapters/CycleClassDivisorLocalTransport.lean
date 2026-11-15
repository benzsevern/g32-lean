import HodgeLean.Adapters.CycleClassDivisorLocalTransportProofs
import HodgeLean.Adapters.CycleClassDivisorProduct4Examples

/-! # Supported product restriction to an anchored germ
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Restriction expresses the global supported product germ using the actual local relative cup.
Source: `ccm5_supportGerm_restriction`, relative cup naturality, and the full-open pair identification. -/
theorem ccm17_supportedCup_germ (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (p q : ℕ) (a : ComplexPoint X) (ha : a ∈ U)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ)) :
    ccm5_supportGerm X (S ⊓ T) (p + q) a (ccm16_supportedCup X S T p q u v) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      ((S ⊓ T : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) (p + q) U a ha
      (ccm15_relativeCup (TopCat.of U)
        (S.preimage continuous_subtype_val) (T.preimage continuous_subtype_val) p q
        (relativeCohomologyMap ℚ p
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
            ⟨Subtype.val, continuous_subtype_val⟩ S)
          (ccm16_supportedComparison X S p u))
        (relativeCohomologyMap ℚ q
          (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
            ⟨Subtype.val, continuous_subtype_val⟩ T)
          (ccm16_supportedComparison X T q v))) :=
  ccm17_supportedCup_germ_aux X S T U p q a ha u v

/-- The actual scheme point with its constructed nonzero supported unit in both slots.
Source: the full-support point model in ccm16. -/
example :
    ccm5_supportGerm ccm16_point ((⊤ : Closeds (ComplexPoint ccm16_point)) ⊓ (⊤ : Closeds (ComplexPoint ccm16_point))) (0 + 0) (𝟙 ccm16_point) (ccm16_supportedCup ccm16_point (⊤ : Closeds (ComplexPoint ccm16_point)) (⊤ : Closeds (ComplexPoint ccm16_point)) 0 0 ccm16_pointSupportedUnit ccm16_pointSupportedUnit) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint ccm16_point))
      (((⊤ : Closeds (ComplexPoint ccm16_point)) ⊓ (⊤ : Closeds (ComplexPoint ccm16_point)) : Closeds (ComplexPoint ccm16_point)) : Set (ComplexPoint ccm16_point)) (0 + 0) (⊤ : Opens (ComplexPoint ccm16_point)) (𝟙 ccm16_point) (Set.mem_univ _)
      (ccm15_relativeCup (TopCat.of (⊤ : Opens (ComplexPoint ccm16_point)))
        ((⊤ : Closeds (ComplexPoint ccm16_point)).preimage continuous_subtype_val) ((⊤ : Closeds (ComplexPoint ccm16_point)).preimage continuous_subtype_val) 0 0
        (relativeCohomologyMap ℚ 0
          (ccm17_preimagePair (TopCat.of (⊤ : Opens (ComplexPoint ccm16_point))) (TopCat.of (ComplexPoint ccm16_point))
            ⟨Subtype.val, continuous_subtype_val⟩ (⊤ : Closeds (ComplexPoint ccm16_point)))
          (ccm16_supportedComparison ccm16_point (⊤ : Closeds (ComplexPoint ccm16_point)) 0 ccm16_pointSupportedUnit))
        (relativeCohomologyMap ℚ 0
          (ccm17_preimagePair (TopCat.of (⊤ : Opens (ComplexPoint ccm16_point))) (TopCat.of (ComplexPoint ccm16_point))
            ⟨Subtype.val, continuous_subtype_val⟩ (⊤ : Closeds (ComplexPoint ccm16_point)))
          (ccm16_supportedComparison ccm16_point (⊤ : Closeds (ComplexPoint ccm16_point)) 0 ccm16_pointSupportedUnit))) :=
  ccm17_supportedCup_germ ccm16_point ⊤ ⊤ ⊤ 0 0 (𝟙 ccm16_point)
    (Set.mem_univ _) ccm16_pointSupportedUnit ccm16_pointSupportedUnit

end HodgeLean.Adapters
