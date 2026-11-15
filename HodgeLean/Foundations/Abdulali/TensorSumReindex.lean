import HodgeLean.Foundations.Program.MilneTensorContractions

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Abdulali

/-- Reindexing the first summand commutes with joining the two tensor factors. -/
theorem tensorSum_reindex_left {A C J V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : A ≃ C) (a : ⨂[ℂ] (_ : A), V) (b : ⨂[ℂ] (_ : J), V) :
    PiTensorProduct.reindex ℂ (fun _ : A ⊕ J => V)
      (Equiv.sumCongr e (Equiv.refl J)) ((PiTensorProduct.tmulEquiv ℂ V) (a ⊗ₜ[ℂ] b)) =
    (PiTensorProduct.tmulEquiv ℂ V)
      (PiTensorProduct.reindex ℂ (fun _ : A => V) e a ⊗ₜ[ℂ] b) := by
  have hc : (PiTensorProduct.reindex ℂ (fun _ : A ⊕ J => V)
      (Equiv.sumCongr e (Equiv.refl J))).toLinearMap.comp
      (PiTensorProduct.tmulEquiv ℂ V).toLinearMap =
      (PiTensorProduct.tmulEquiv ℂ V).toLinearMap.comp
        (TensorProduct.map (PiTensorProduct.reindex ℂ (fun _ : A => V) e).toLinearMap
          (LinearMap.id : (⨂[ℂ] (_ : J), V) →ₗ[ℂ] _)) := by
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change PiTensorProduct.reindex ℂ _ (Equiv.sumCongr e (Equiv.refl J))
        ((PiTensorProduct.tmulEquiv ℂ V)
          (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)) =
      (PiTensorProduct.tmulEquiv ℂ V)
        (TensorProduct.map (PiTensorProduct.reindex ℂ (fun _ : A => V) e).toLinearMap
          LinearMap.id (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w))
    simp only [PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
      LinearMap.comp_apply]
    congr 1
    funext x
    cases x <;> rfl
  exact LinearMap.congr_fun hc (a ⊗ₜ[ℂ] b)

end HodgeLean.Foundations.Abdulali
