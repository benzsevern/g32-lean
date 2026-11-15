import HodgeLean.Adapters.CycleClassFlatPullback
/-! # Algebraic pullback along powers sum maps: proofs -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}

theorem ccm2_pwSumMap_smooth_of_ne_zero_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Smooth (P.pwSumMap θ a).left := by
  exact ccm3_ccm2_pwSumMap_smooth_of_ne_zero P θ a ha

end HodgeLean.Adapters
