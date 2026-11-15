import HodgeLean.Foundations.QuotientDuality.RetainedCycleMiddleSymmetry
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapWithOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapPairing
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

noncomputable section
open AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The middle-dimensional actual cap map with the specified orientation and its degree transport. -/
def retainedMiddleCapWithOrientation (X : TopCat.{0}) (k : ℕ)
    (c : Homology ℚ X (2 * (2 * k))) :
    Cohomology ℚ X (2 * k) →ₗ[ℚ] Homology ℚ X (2 * k) :=
  retainedCapWithOrientation X (2 * k) (2 * k)
    ((show 2 * k + 2 * k = 2 * (2 * k) by omega).symm ▸ c)

/-- Bijectivity of the actual middle cap map yields perfectness of the specified cup pairing. -/
theorem retained_middle_pairing_perfect_of_cap (X : TopCat.{0}) (k : ℕ)
    [Module.Finite ℚ (Cohomology ℚ X (2 * k))]
    (c : Homology ℚ X (2 * (2 * k)))
    (hcap : Function.Bijective (retainedMiddleCapWithOrientation X k c)) :
    Function.Bijective (properCyclePairing X k c) := by
  apply retained_pairing_perfect_of_cap (properCyclePairing X k c)
    (retainedMiddleCapWithOrientation X k c) (cohomologyEquivDualHomology ℚ X (2 * k)) hcap
  intro a b
  exact retained_orientation_cap_evaluation_cast X (2 * k) (2 * k) (2 * (2 * k))
    (by omega) c a b

/-- Actual middle cap bijectivity alone gives perfectness through middle cup symmetry. -/
theorem retained_middle_pairing_perfect_of_cap_bijective (X : TopCat.{0}) (k : ℕ)
    (c : Homology ℚ X (2 * (2 * k)))
    (hcap : Function.Bijective (retainedMiddleCapWithOrientation X k c)) :
    Function.Bijective (properCyclePairing X k c) := by
  apply retained_symmetric_pairing_perfect_of_cap (properCyclePairing X k c)
    (retainedMiddleCapWithOrientation X k c) (cohomologyEquivDualHomology ℚ X (2 * k)) hcap
  · intro a b
    exact retained_orientation_cap_evaluation_cast X (2 * k) (2 * k) (2 * (2 * k))
      (by omega) c a b
  · exact retained_middle_pairing_symmetric X k c

end HodgeLean.Foundations.QuotientDuality
