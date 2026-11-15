import HodgeLean.Foundations.Program.G32Native.IdealTargetPullback
import HodgeLean.Foundations.Program.SchoenCycleC2OpenIdealRestrictionHelpers

/-! # The actual ideal module on an ambient affine open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Restriction and the canonical affine chart transport the actual kernel
ideal module without changing the restricted immersion. -/
def affineOpenIdealPullbackIso {Q W : Scheme.{0}} (i : Q ⟶ W)
    (U : W.Opens) (hU : IsAffineOpen U) :
    (Scheme.Modules.pullback hU.fromSpec).obj (Conormal.idealModule i) ≅
      Conormal.idealModule ((i ∣_ U) ≫ hU.isoSpec.hom) :=
  (Scheme.Modules.pullbackComp hU.isoSpec.inv U.ι).symm.app _ ≪≫
    (Scheme.Modules.pullback hU.isoSpec.inv).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
        s2e_idealModule_restrict_iso i U) ≪≫
    idealTargetPullbackIso (i ∣_ U) hU.isoSpec

#print axioms affineOpenIdealPullbackIso
end HodgeLean.Foundations.Program.G32Native
