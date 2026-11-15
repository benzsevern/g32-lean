import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity

/-! # Original normalized relative coclasses under specified degree transport
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normalized relative coclass retains the same normalization through the specified homology and cohomology degree transports.
Source: normalizedRelativeCoclass; AlgebraicTopology.Singular.relativeHomologyDegreeCast.
HC no distance; AV milestone no distance. -/
theorem properCycle_normalized_relative_coclass_degree {P : TopPair.{0}} {i j : ℕ}
    (e : i = j) (z : RelativeHomology ℚ P i) (hz : z ≠ 0) :
    (e ▸ normalizedRelativeCoclass z hz) =
      normalizedRelativeCoclass (relativeHomologyDegreeCast e z)
        ((relativeHomologyDegreeCast_ne_zero_iff e z).mpr hz) := by
  subst j
  rfl

end HodgeLean.Foundations.QuotientDuality
