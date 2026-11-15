import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison
import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison

/-! # The actual conormal on affine schemes in associated-module coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- Pulling an affine conormal along its spectrum identification gives
the associated scalar-extended kernel module. -/
def unionConormalAffineConormalPresentation
    {Q W : Scheme.{0}} [IsAffine Q] [IsAffine W] (i : Q ⟶ W) :
    (Scheme.Modules.pullback Q.isoSpec.inv).obj (s2c_conormal i) ≅
      tilde ((ModuleCat.extendScalars i.appTop.hom).obj
        (ModuleCat.of Γ(W, ⊤) (RingHom.ker i.appTop.hom))) := by
  let iΓ := Spec.map i.appTop
  let h : Q.isoSpec.inv ≫ i = iΓ ≫ W.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality i).symm
  haveI : IsIso (idealPullbackMap i iΓ W.isoSpec.inv Q.isoSpec.inv h) :=
    idealPullbackMap_isIso_of_isIso i iΓ W.isoSpec.inv Q.isoSpec.inv h
  haveI : IsIso (comparisonMap i iΓ W.isoSpec.inv Q.isoSpec.inv h) := by
    rw [unionConormal_comparisonMap_eq_prefix]
    infer_instance
  exact asIso (comparisonMap i iΓ W.isoSpec.inv Q.isoSpec.inv h) ≪≫
    unionConormalAffineComparisonTargetIso Γ(W, ⊤) Γ(Q, ⊤) i.appTop

end HodgeLean.Foundations.Program.G32Native
