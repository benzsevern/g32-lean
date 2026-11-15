import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalCapScalar
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-! # Actual cap duality on the standard complex normal slice -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Capping by the original standard complex normal coclass identifies the actual normal local homology line with the actual degree-zero homology of the normal slice.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, connected degree-zero homology and complex normal orientations.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_normal_cap_bijective (d : ℕ) :
    Function.Bijective (relativeCapCohomologyLinear ℚ (puncturedPair ℂ d) (2 * d) 0
      (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
        (standardComplexLocalClass_ne_zero_for_chart d))) := by
  apply properCycle_normalized_relative_cap_bijective (puncturedPair ℂ d) (2 * d)
    (standardComplexLocalClass ℚ d) (standardComplexLocalClass_ne_zero_for_chart d)
  · constructor
    · intro r s h
      change r • standardComplexLocalClass ℚ d = s • standardComplexLocalClass ℚ d at h
      exact smul_left_injective ℚ (standardComplexLocalClass_ne_zero_for_chart d) h
    · intro v
      apply Submodule.mem_span_singleton.mp
      rw [span_standardComplexLocalClass_eq_top_for_chart d]
      trivial
  · let e := (asIso (TopCat.singularHomology₀ε (TopCat.of (Fin d → ℂ))
      (ModuleCat.of ℚ ℚ))).toLinearEquiv
    exact e.finrank_eq.trans (Module.finrank_self ℚ)

end HodgeLean.Foundations.QuotientDuality
