import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Foundations.Singular.GradedComm

noncomputable section
open AlgebraicTopology.Singular
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified middle pairing is symmetric because its cohomology degree is even. -/
theorem retained_middle_pairing_symmetric (X : TopCat.{0}) (k : ℕ)
    (c : Homology ℚ X (2 * (2 * k))) (a b : Cohomology ℚ X (2 * k)) :
    properCyclePairing X k c a b = properCyclePairing X k c b a := by
  have hc := HodgeLean.Foundations.Singular.cup_comm_graded X
    (show 2 * k + 2 * k = 2 * (2 * k) by omega)
    (show 2 * k + 2 * k = 2 * (2 * k) by omega) a b
  have hs : (-1 : ℚ) ^ ((2 * k) * (2 * k)) = 1 := by
    rw [show (2 * k) * (2 * k) = 2 * (k * (2 * k)) by ring, pow_mul]
    norm_num
  rw [hs, one_smul] at hc
  exact congrArg (orientationIntegral X (2 * (2 * k)) c) hc.symm

end HodgeLean.Foundations.QuotientDuality
