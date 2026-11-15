import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalSupportedCapLift

/-! # The actual support cap on the original middle cycle groups
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual original supported group maps linearly to homology of its literal analytic support by the constructed projective support cap.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_projective_support_cap.
HC no distance; AV milestone no distance. -/
def properCycle_original_support_cap
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (c : Homology ℚ (a3b4_an X.hom) (2 * k + 2 * k)) :
    s2e_supportedClass X γ k →ₗ[ℚ]
      Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2 * k) :=
  properCycle_projective_support_cap X (a3b4a_classAlgebraicSupport X.hom γ)
    (2*k) (2*k) c

/-- The literal support inclusion carries the constructed original map to the exact absolute cap in the frozen factorization statement.
Source: properCycle_projective_support_cap_inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_support_cap_inclusion
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (c : Homology ℚ (a3b4_an X.hom) (2 * k + 2 * k)) (a : s2e_supportedClass X γ k) :
    homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ)).map (properCycle_original_support_cap X γ k c a) =
      capCohomologyLinear ℚ (a3b4_an X.hom) (2*k) (2*k)
        ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2*k)).symm
          (s2e_classToAbsolute X γ k a))
        c := by
  unfold properCycle_original_support_cap
  exact properCycle_projective_support_cap_inclusion X (a3b4a_classAlgebraicSupport X.hom γ)
    (2*k) (2*k) c a

/-- The constructed original cap respects the exact enlargement map for literal cycle supports.
Source: properCycle_projective_support_cap_enlarge_support.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_support_cap_enlarge_support
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ δ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k)) (a : s2e_supportedClass X γ k) :
    homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h))
      (properCycle_original_support_cap X γ k c a) =
      properCycle_original_support_cap X δ k c
        (enlargeSupport ℚ (a3b4_an X.hom) h (2*k) a) := by
  unfold properCycle_original_support_cap
  exact properCycle_projective_support_cap_enlarge_support X
    (a3b4a_classAlgebraicSupport X.hom γ) (a3b4a_classAlgebraicSupport X.hom δ)
    h (2*k) (2*k) c a

end HodgeLean.Foundations.QuotientDuality
