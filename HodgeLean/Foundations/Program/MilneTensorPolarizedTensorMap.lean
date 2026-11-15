import HodgeLean.Foundations.Program.MilneTensorRankOnePolarization
import HodgeLean.Foundations.Program.MilneTensorFunctionEquiv

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def m1b_polarizedTensorMap (C : LinearMap.BilinForm ℂ (ι → ℂ))
    (hC : C.Nondegenerate) (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ)) :
    Module.End ℂ (⨂[ℂ]^(k * 2) (ι → ℂ)) :=
  PiTensorProduct.lift ((m1b_tensorFunctionEquiv C hC (k * 2)).symm.toLinearMap.compMultilinearMap
    (m1b_rankOnePolarization k J))

theorem m1b_polarizedTensorMap_tprod (C : LinearMap.BilinForm ℂ (ι → ℂ))
    (hC : C.Nondegenerate) (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (x v : Fin (k * 2) → ι → ℂ) :
    m1b_tensorFunction C (k * 2) (m1b_polarizedTensorMap C hC k J (⨂ₜ[ℂ] s, x s)) v =
      J v (fun a => m1b_rankOneForm (fun s => x (finProdFinEquiv (a, s)))) := by
  change m1b_tensorFunctionEquiv C hC (k * 2)
    (m1b_polarizedTensorMap C hC k J (⨂ₜ[ℂ] s, x s)) v = _
  simp only [m1b_polarizedTensorMap, PiTensorProduct.lift.tprod,
    LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, m1b_rankOnePolarization_apply]

end HodgeLean.Foundations.Program
