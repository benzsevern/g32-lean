import HodgeLean.Adapters.CycleClassDivisorLocal

/-! # Supported product restriction to an anchored germ
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

private theorem ccm17_supportedComparison_restrict (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (n : ℕ) (u : H_[S]^n(X; ℚ)) :
    relativeCohomologyMap ℚ n
      (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
        ⟨Subtype.val, continuous_subtype_val⟩ S)
      (ccm16_supportedComparison X S n u) =
    relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from le_top) (S : Set (ComplexPoint X)))
      (supportedSingularClass X S n u) := by
  change (relativeCohomologyMap ℚ n
    (ccm17_preimagePair (TopCat.of U) (TopCat.of (ComplexPoint X))
      ⟨Subtype.val, continuous_subtype_val⟩ S)).comp
    (relativeCohomologyMap ℚ n (ccm16_fullPairIso (TopCat.of (ComplexPoint X)) S).hom)
      (supportedSingularClass X S n u) = _
  rw [← relativeCohomologyMap_comp]
  rfl

theorem ccm17_supportedCup_germ_aux (X : Over (Spec ↧ℂ))
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
          (ccm16_supportedComparison X T q v))) := by
  rw [← ccm5_supportGerm_restriction X (S ⊓ T) U (p + q) a ha,
    ← ccm17_supportedComparison_restrict]
  have hc : ccm16_supportedComparison X (S ⊓ T) (p + q)
      (ccm16_supportedCup X S T p q u v) =
    ccm15_relativeCup (TopCat.of (ComplexPoint X)) S T p q
      (ccm16_supportedComparison X S p u) (ccm16_supportedComparison X T q v) :=
    (ccm16_supportedComparison X (S ⊓ T) (p + q)).apply_symm_apply _
  rw [hc]
  exact congrArg (supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    ((S ⊓ T : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) (p + q) U a ha)
    (ccm17_relativeCup_pullback_aux (TopCat.of U) (TopCat.of (ComplexPoint X))
      ⟨Subtype.val, continuous_subtype_val⟩ S T p q
      (ccm16_supportedComparison X S p u) (ccm16_supportedComparison X T q v))

#print axioms ccm17_supportedCup_germ_aux

end HodgeLean.Adapters
