import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Composition of original relative homology degree transports
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative homology degree transports compose through the specified equality of degrees.
Source: AlgebraicTopology.Singular.relativeHomologyDegreeCast; equality transport.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_degree_cast_trans {P : TopPair.{0}} {i j k : ℕ}
    (e : i = j) (h : j = k) (z : RelativeHomology ℚ P i) :
    relativeHomologyDegreeCast h (relativeHomologyDegreeCast e z) =
      relativeHomologyDegreeCast (e.trans h) z := by
  subst j
  subst k
  rfl

end HodgeLean.Foundations.QuotientDuality
