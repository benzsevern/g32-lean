import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- On affine schemes, taking global sections after pushforward is scalar
restriction along the actual ring homomorphism. -/
def s2e_affine_pushforward_sections_iso
    (R S : CommRingCat.{0}) (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom := by
  let F := Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)
  let G := moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom
  change F ≅ G
  refine NatIso.ofComponents (fun M => ?_) ?_
  · refine (show (F.obj M) ≃ₗ[R] G.obj M from ?_).toModuleIso
    refine
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := ?_ }
    intro r x
    change (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) • (show Γ(M, ⊤) from x) =
      (Scheme.ΓSpecIso S).inv (φ r) • (show Γ(M, ⊤) from x)
    congr 1
    exact (congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ r)
      (Scheme.ΓSpecIso_inv_naturality φ)).symm
  · intro M N f
    ext x
    rfl

end HodgeLean.Foundations.Program
