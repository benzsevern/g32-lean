import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveSupportCollar

/-! # Actual global linear cap on original projective algebraic supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual global support cap constructed from retained projective neighborhood maps and the original excised relative class.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, supported cap products; properCycle_projective_support_collar.
HC no distance; AV milestone no distance. -/
def properCycle_projective_support_cap
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left)
    (p q : ℕ) (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p + q)) :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) p →ₗ[ℚ]
      Homology ℚ (TopCat.of (Point.underlying ⁻¹' (S : Set X.left))) q :=
  (properCycle_projective_support_collar X S).cap
    (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c

/-- The original support inclusion carries the constructed projective support cap to the literal absolute cap.
Source: ProperCycleSupportCollar.cap_inclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_support_cap_inclusion
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (S : Closeds X.left)
    (p q : ℕ) (c : Homology ℚ (TopCat.of (ComplexPoint X)) (p + q))
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left)) p) :
    homologyMap ℚ q (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (Point.underlying ⁻¹' (S : Set X.left))).map
      (properCycle_projective_support_cap X S p q c a) =
      capCohomologyLinear ℚ (TopCat.of (ComplexPoint X)) p q
        ((cochainCohomologyEquiv ℚ (TopCat.of (ComplexPoint X)) p).symm
          (forgetSupport ℚ (TopCat.of (ComplexPoint X))
            (Point.underlying ⁻¹' (S : Set X.left)) p a)) c :=
  (properCycle_projective_support_collar X S).cap_inclusion
    (S.isClosed.preimage (continuous_underlying_to_zariski X)) p q c a

end HodgeLean.Foundations.QuotientDuality
