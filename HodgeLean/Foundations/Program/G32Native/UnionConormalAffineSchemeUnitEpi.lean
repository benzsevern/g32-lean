import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitSchemeIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitObjectIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineUnitEpi
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Epic pullback units on affine schemes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An associated-module presentation gives an epic unit for an affine immersion. -/
lemma unionConormal_affineSchemeUnit_epi
    {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : Y.Modules)
    (M₀ : ModuleCat Γ(Y, ⊤))
    (eM : (Scheme.Modules.pullback Y.isoSpec.inv).obj M ≅ tilde M₀) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  haveI := unionConormal_affineUnit_epi Γ(Y, ⊤) Γ(X, ⊤) f.appTop
    (f.app_surjective ⊤ (isAffineOpen_top Y)) M₀
  haveI := unionConormal_unit_epi_of_iso
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f.appTop)) eM
  exact unionConormal_unit_epi_of_scheme_isos f (Spec.map f.appTop)
    X.isoSpec.inv Y.isoSpec.inv (Scheme.isoSpec_inv_naturality f).symm M

end HodgeLean.Foundations.Program.G32Native
