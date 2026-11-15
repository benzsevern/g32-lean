module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Affine pullback and associated sheaves -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
universe u
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Affine pushforward commutes with global sections and restriction of scalars. -/
def s2e_affinePushforwardGammaIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let A := (Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor).obj M
    let B := (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom).obj M
    let e : A ≃ₗ[R] B :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change ((Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) • (show Γ(M, ⊤) from x) =
            ((Scheme.ΓSpecIso S).inv.hom (f.hom r)) • (show Γ(M, ⊤) from x)
          congr 1
          exact congrArg (fun g : R ⟶ Γ(Spec S, ⊤) => g.hom r)
            (Scheme.ΓSpecIso_inv_naturality f).symm }
    exact e.toModuleIso
  · intro M N g
    rfl

/-- Associated sheaves carry extension of scalars to affine pullback. -/
def s2e_affinePullbackTildeIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars.{u, u, u} f.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (s2e_affinePushforwardGammaIso f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).comp (tilde.adjunction (R := S)))

end HodgeLean.Foundations.Program
