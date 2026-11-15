import HodgeLean.Foundations.Program.MilneTensorPolarizedTensorMap

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

theorem m1b_polarizedTensorMap_pairSum (C : LinearMap.BilinForm ℂ (ι → ℂ))
    (hC : C.Nondegenerate) (k : ℕ)
    (J : MultilinearMap ℂ (fun _ : Fin (k * 2) => ι → ℂ)
      (MultilinearMap ℂ (fun _ : Fin k => ι × ι → ℂ) ℂ))
    (w : Fin k → β → Fin 2 → ι → ℂ) (v : Fin (k * 2) → ι → ℂ) :
    m1b_tensorFunction C (k * 2)
      (m1b_polarizedTensorMap C hC k J
        (∑ f : Fin k → β, ⨂ₜ[ℂ] s, w (finProdFinEquiv.symm s).1
          (f (finProdFinEquiv.symm s).1) (finProdFinEquiv.symm s).2)) v =
      J v (fun a => ∑ b, m1b_rankOneForm (w a b)) := by
  classical
  simp only [map_sum, MultilinearMap.sum_apply, m1b_polarizedTensorMap_tprod,
    Equiv.symm_apply_apply]
  exact ((J v).map_sum (fun a b => m1b_rankOneForm (w a b))).symm

end HodgeLean.Foundations.Program
