import HodgeLean.Foundations.DiscreteValuationRing.ParameterExpansion
import HodgeLean.Foundations.Port.AlgebraicGeometry.Smooth.RegularLocal
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Every codimension-one stalk of a smooth integral complex scheme is a DVR. -/
theorem s2v_l1b_divisor_codimension_one_dvr
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (x : X.left) (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.left.presheaf.stalk x) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsRegularLocalRing (X.left.presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalk_complex (f := X.hom) x
  exact DiscreteValuationRing.ParameterExpansion.stalk_dvr_of_coheight_one X.left x hx

end HodgeLean.Foundations.Program
