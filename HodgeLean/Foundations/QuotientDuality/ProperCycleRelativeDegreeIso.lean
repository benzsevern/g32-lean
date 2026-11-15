import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Original module equality isomorphisms and relative degree casts
HC no distance; AV milestone no distance. -/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original equality-induced module isomorphism acts by the specified original relative degree cast.
Source: CategoryTheory.eqToIso; relativeHomologyDegreeCast.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_degree_iso_apply {P : TopPair.{0}} {i j : ℕ}
    (e : i = j) (z : RelativeHomology ℚ P i) :
    (eqToIso (congrArg (fun n => RelativeHomology ℚ P n) e)).hom.hom z =
      relativeHomologyDegreeCast e z := by
  subst j
  rfl

end HodgeLean.Foundations.QuotientDuality
