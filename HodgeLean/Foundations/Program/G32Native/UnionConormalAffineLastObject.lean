import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoPushforwardObject
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineConormalPresentation
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffinePushforwardCoordinates

/-! # The actual affine last object in scalar-restricted kernel coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The affine last object is the associated scalar-restricted extended kernel. -/
def unionConormalAffineLastObjectIso
    {Q S W : Scheme.{0}} [IsAffine Q] [IsAffine S] [IsAffine W]
    (f : S ⟶ Q) (i : S ⟶ W) :
    (Scheme.Modules.pullback Q.isoSpec.inv).obj
      ((Scheme.Modules.pushforward f).obj (s2c_conormal i)) ≅
      tilde ((ModuleCat.restrictScalars f.appTop.hom).obj
        ((ModuleCat.extendScalars i.appTop.hom).obj
          (ModuleCat.of Γ(W, ⊤) (RingHom.ker i.appTop.hom)))) :=
  unionConormalIsoPushforwardObjectIso f (Spec.map f.appTop)
      S.isoSpec.inv Q.isoSpec.inv (Scheme.isoSpec_inv_naturality f).symm
      (s2c_conormal i) ≪≫
    (Scheme.Modules.pushforward (Spec.map f.appTop)).mapIso
      (unionConormalAffineConormalPresentation i) ≪≫
    unionAffinePushforwardTildeIso Γ(Q, ⊤) Γ(S, ⊤) f.appTop _

end HodgeLean.Foundations.Program.G32Native
