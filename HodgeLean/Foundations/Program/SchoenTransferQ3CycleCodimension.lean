import HodgeLean.Foundations.Program.SchoenTransferQ3Generalizing
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedCoefficients

/-! Exact coheight of every surviving weighted inverse component. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- All surviving inverse components retain the input cycle's codimension,
using the actual target-prime coefficient and coheight preservation. -/
theorem s4_q3_flatPullback_pure_coheight
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsNoetherian X.left]
    (q : X ⟶ W) [LocallyQuasiFinite q.left] (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ) (k : ℕ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k) :
    ∀ p ∈ (ccm3_flatPullback q.left z).support, Order.coheight p = k := by
  intro p hp
  change ccm3_flatPullback q.left z p ≠ 0 at hp
  rw [s4_q3_flatPullback_coefficient_at_image q hq z p] at hp
  exact (s4_q3_coheight_eq_of_open_quasiFinite q.left hq p).trans
    (hz (q.left p) (mul_ne_zero_iff.mp hp).1)

end HodgeLean.Foundations.Program
