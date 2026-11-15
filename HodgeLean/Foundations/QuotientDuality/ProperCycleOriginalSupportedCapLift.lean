import HodgeLean.Adapters.NormalConeB4aClassSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveCapSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleTopology
import HodgeLean.Foundations.Program.SchoenCycleClassDefs

/-! # Original middle supported cap on the literal cycle support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original middle supported cap has a homology lift on the literal analytic cycle support, including components in the singular ambient locus.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_projective_algebraic_cap_support.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_supported_cap_lift
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (a : s2e_supportedClass X γ k)
    (c : Homology ℚ (a3b4_an X.hom) (2 * k + 2 * k)) :
    ∃ b : Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2 * k),
      homologyMap ℚ (2 * k) (TopPair.ofSubset (X := a3b4_an X.hom)
        (a3b4_cycleSupport X.hom γ)).map b =
      capCohomologyLinear ℚ (a3b4_an X.hom) (2 * k) (2 * k)
        ((cochainCohomologyEquiv ℚ (a3b4_an X.hom) (2 * k)).symm
          (s2e_classToAbsolute X γ k a)) c := by
  exact properCycle_projective_algebraic_cap_support X
    (a3b4a_classAlgebraicSupport X.hom γ) (2 * k) (2 * k) a c

end HodgeLean.Foundations.QuotientDuality
