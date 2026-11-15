import HodgeLean.Foundations.Program.G32Native.AffineOpenIdealTransport
import HodgeLean.Foundations.Program.G32Native.AffinePointFibreTensor

/-! # Original ideal fibres in canonical ambient affine coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual ideal fibre at an original ambient point is its fibre on
an actual affine open, retaining the specified point factorization. -/
def affineOpenIdealPointEquiv {Q W : Scheme.{0}} (i : Q ⟶ W)
    (U : W.Opens) (hU : IsAffineOpen U) (p : Spec ↧ℂ ⟶ W)
    (ε : Γ(W, U) ⟶ CommRingCat.of ℂ) (hp : Spec.map ε ≫ hU.fromSpec = p) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback p).obj (Conormal.idealModule i)) ≃ₗ[ℂ]
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj
        (Conormal.idealModule ((i ∣_ U) ≫ hU.isoSpec.hom))) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackCongr hp).symm.app _ ≪≫
      (Scheme.Modules.pullbackComp (Spec.map ε) hU.fromSpec).symm.app _ ≪≫
      (Scheme.Modules.pullback (Spec.map ε)).mapIso (affineOpenIdealPullbackIso i U hU))).toLinearEquiv

#print axioms affineOpenIdealPointEquiv
end HodgeLean.Foundations.Program.G32Native
