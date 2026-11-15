import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClassGenerator

/-! # Original relative homology degree transports under actual pair maps
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative homology degree transport commutes with every actual relative pair map.
Source: AlgebraicTopology.Singular.relativeHomologyDegreeCast; functorial relative singular homology.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_homology_degree_map {P Q : TopPair.{0}} (f : P ⟶ Q)
    {i j : ℕ} (e : i = j) (z : RelativeHomology ℚ P i) :
    relativeHomologyMap ℚ j f (relativeHomologyDegreeCast e z) =
      relativeHomologyDegreeCast e (relativeHomologyMap ℚ i f z) := by
  subst j
  rfl

end HodgeLean.Foundations.QuotientDuality
