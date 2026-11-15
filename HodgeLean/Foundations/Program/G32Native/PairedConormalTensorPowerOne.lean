import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorPowers

/-! # The actual degree-one tensor comparison retains the supplied section -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Scheme.Modules
namespace HodgeLean.Foundations.Program.G32Native

/-- The original degree-one tensor section is the inverse unitor image of
the supplied section, without an additional normalization scalar. -/
theorem paired_tensorPowOneIso_inv_section {X : Scheme} (L : X.Modules)
    (U : X.Opens) (s : Γ(L, U)) :
    (L.tensorPowOneIso.inv).val.app (Opposite.op U) s = tensorPowSection s 1 := by
  let e := (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)).mapIso
    L.tensorPowOneIso
  apply e.toLinearEquiv.injective
  have hs : (λ_ L).hom.app U (tensorPowSection s 1) = s := by
    simpa only [tensorPowSection_one, unitSection_def, one_smul] using
      (leftUnitor_hom_app_tensorSections (1 : Γ(X, U)) s)
  exact (e.toLinearEquiv.apply_symm_apply s).trans hs.symm

end HodgeLean.Foundations.Program.G32Native
