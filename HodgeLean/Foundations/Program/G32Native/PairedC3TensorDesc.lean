import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorSections

/-! # Descending original presheaf tensor morphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Descend a presheaf tensor morphism through the original sheafification. -/
def pairedC3TensorDesc {X : Scheme.{0}} {L M N : X.Modules}
    (p : L.val ⊗ M.val ⟶ N.val) : L ⊗ M ⟶ N :=
  (tensorIsoSheafify L M).inv ≫
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).homEquiv _ _).symm p

/-- The descended morphism retains its original value on pure tensors. -/
theorem paired_c3_tensor_desc_sections {X : Scheme.{0}} {L M N : X.Modules}
    (p : L.val ⊗ M.val ⟶ N.val) (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    (pairedC3TensorDesc p).app U (tensorSections s t) =
      p.app (op U) (s ⊗ₜ[Γ(X, U)] t) := by
  let A := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property
  let d := (A.homEquiv (L.val ⊗ M.val) N).symm p
  have hd : A.unit.app (L.val ⊗ M.val) ≫
      (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map d = p :=
    (A.homEquiv _ _).apply_symm_apply p
  have h := congrArg (fun q : L.val ⊗ M.val ⟶ N.val =>
      q.app (op U) (s ⊗ₜ[Γ(X, U)] t)) hd
  change d.val.app (op U) ((A.unit.app (L.val ⊗ M.val)).app (op U)
    (s ⊗ₜ[Γ(X, U)] t)) = _ at h
  change (pairedC3TensorDesc p).val.app (op U)
      ((tensorSectionsHom L M).app (op U) (s ⊗ₜ[Γ(X, U)] t)) = _
  change (((tensorIsoSheafify L M).hom ≫
      (tensorIsoSheafify L M).inv ≫ d).val.app (op U))
      ((A.unit.app (L.val ⊗ M.val)).app (op U) (s ⊗ₜ[Γ(X, U)] t)) = _
  rw [Iso.hom_inv_id_assoc]
  exact h

#print axioms paired_c3_tensor_desc_sections
end HodgeLean.Foundations.Program.G32Native
