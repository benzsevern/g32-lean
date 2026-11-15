import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalizedCoclassDegree
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Specified standard complex normal coclass in the original degree
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual standard complex normal coclass retains its specified normalization in the frozen degree spelling.
Source: properCycle_normalized_relative_coclass_degree; standardComplexLocalClass.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_coclass_degree (d : ℕ) :
    let hz := (standardComplexLocalClassMul_ne_zero_iff d).mpr
      ((standardComplexLocalClass_ne_zero_iff d).mp (standardComplexLocalClass_ne_zero_for_chart d))
    (Nat.mul_comm d 2 ▸ normalizedRelativeCoclass (standardComplexLocalClassMul d) hz) =
      normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
        (standardComplexLocalClass_ne_zero_for_chart d) := by
  dsimp only
  rw [properCycle_normalized_relative_coclass_degree]
  rfl

end HodgeLean.Foundations.QuotientDuality
