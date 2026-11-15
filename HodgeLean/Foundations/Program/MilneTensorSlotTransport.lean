import HodgeLean.Foundations.Program.MilneTensorHelpers

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_tensorPow_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (u : Module.End ℂ V) (t : ⨂[ℂ] _ : ι, V) :
    PiTensorProduct.reindex ℂ (fun _ => V) e (SchurWeyl.tensorPow ι u t) =
      SchurWeyl.tensorPow κ u (PiTensorProduct.reindex ℂ (fun _ => V) e t) := by
  have h : (PiTensorProduct.reindex ℂ (fun _ => V) e).toLinearMap.comp
      (SchurWeyl.tensorPow ι u) = (SchurWeyl.tensorPow κ u).comp
        (PiTensorProduct.reindex ℂ (fun _ => V) e).toLinearMap := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      SchurWeyl.tensorPow_tprod, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod]
  exact LinearMap.congr_fun h t

end HodgeLean.Foundations.Program
