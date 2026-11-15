import HodgeLean.Foundations.Program.G32Native.PairedC3DualFrame
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorSectionSheafification

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry.Scheme.Modules.SheafifyMu

/-- Forgetting after restricting scalars along the identity retains the native presheaf. -/
def pairedC3UnderlyingPresheafIso {X : Scheme.{0}} (M : X.Modules) :
    (ι X).obj M ≅ M.val :=
  PresheafOfModules.isoMk
    (fun U => (ModuleCat.restrictScalarsId (X.ringCatSheaf.obj.obj U)).app (M.val.obj U))
    (by intro U V f; ext x; rfl)

/-- The native dual as an arrow into the explicit natural-family presheaf. -/
def pairedC3DualFamilyMap {X : Scheme.{0}} (M : X.Modules) :
    (ι X).obj M.dual ⟶ PresheafOfModules.ihomObj (R := X.sheaf.obj)
      ((ι X).obj M) ((ι X).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (pairedC3UnderlyingPresheafIso M.dual).hom ≫ (pairedC3DualPresheafIso M).hom.val

/-- Evaluation of the original native dual on the original module. -/
def pairedC3DualEvaluation {X : Scheme.{0}} (M : X.Modules) :
    M ⊗ M.dual ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (sheafifyTensorIso M M.dual).inv ≫
    ((adj X).homEquiv _ _).symm
      (PresheafOfModules.uncurry' (R := X.sheaf.obj) (G := (ι X).obj M.dual)
        (N := (ι X).obj (SheafOfModules.unit X.ringCatSheaf)) ((ι X).obj M) (pairedC3DualFamilyMap M))

/-- Evaluation on a tensor of sections is the actual local functional value. -/
theorem paired_c3_dual_evaluation_tensor {X : Scheme.{0}} (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) (φ : Γ(M.dual, U)) :
    (pairedC3DualEvaluation M).app U (tensorSections s φ) =
      ((pairedC3DualPresheafIso M).hom.app U φ).1 (𝟙 (op U)) s := by
  let P := (ι X).obj M ⊗ (ι X).obj M.dual
  let g : P ⟶ (ι X).obj (SheafOfModules.unit X.ringCatSheaf) :=
    PresheafOfModules.uncurry' (R := X.sheaf.obj) (G := (ι X).obj M.dual)
        (N := (ι X).obj (SheafOfModules.unit X.ringCatSheaf)) ((ι X).obj M) (pairedC3DualFamilyMap M)
  let a := ((adj X).homEquiv P (SheafOfModules.unit X.ringCatSheaf)).symm g
  have h : (adj X).unit.app P ≫ (ι X).map a = g := by
    have hh := ((adj X).homEquiv P (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply g
    rw [Adjunction.homEquiv_unit] at hh
    exact hh
  have hv := congrArg (fun p => p.app (op U)
    (s ⊗ₜ[Γ(X, U)] φ)) h
  change a.app U (((adj X).unit.app P).app (op U) (s ⊗ₜ[Γ(X, U)] φ)) = _ at hv
  rw [tensorSections_eq]
  change a.app U ((sheafifyTensorIso M M.dual).inv.app U
    ((sheafifyTensorIso M M.dual).hom.app U
      (((adj X).unit.app P).app (op U) (s ⊗ₜ[Γ(X, U)] φ)))) = _
  let z := ((adj X).unit.app P).app (op U) (s ⊗ₜ[Γ(X, U)] φ)
  have he := congrArg (fun p => (p.val.app (op U)).hom z)
    (sheafifyTensorIso M M.dual).hom_inv_id
  change (sheafifyTensorIso M M.dual).inv.app U
    ((sheafifyTensorIso M M.dual).hom.app U z) = z at he
  rw [he]
  exact hv

end HodgeLean.Foundations.Program.G32Native
