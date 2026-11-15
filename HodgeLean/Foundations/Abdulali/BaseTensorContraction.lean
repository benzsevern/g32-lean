import HodgeLean.Foundations.Abdulali.MixedTensorContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Contract the final block of a base-space tensor with an arbitrary covector. -/
def baseTensorContraction (n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ) :
    (⨂[ℂ]^(n + d) V) →ₗ[ℂ] (⨂[ℂ]^n V) :=
  ((TensorProduct.rid ℂ _).toLinearMap.comp (TensorProduct.map LinearMap.id ℓ)).comp
    (InvariantsExterior.tensorAppend n d).symm.toLinearMap

/-- On a pure tensor, contraction evaluates the final block and retains the initial block. -/
theorem baseTensorContraction_tprod (n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ)
    (v : Fin (n + d) → V) :
    baseTensorContraction n d ℓ (PiTensorProduct.tprod ℂ v) =
      ℓ (PiTensorProduct.tprod ℂ (fun j => v (Fin.natAdd n j))) •
        PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd d i)) := by
  have hv : InvariantsExterior.tensorAppend n d
      (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd d i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun j => v (Fin.natAdd n j))) =
      PiTensorProduct.tprod ℂ v := by
    rw [InvariantsExterior.tensorAppend_tprod, Fin.append_castAdd_natAdd]
  simp only [baseTensorContraction, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← hv, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul]

/-- Base contraction is sum-index reindexing followed by contraction of the second tensor factor. -/
theorem baseTensorContraction_eq_reindex (n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ)
    (t : ⨂[ℂ]^(n + d) V) :
    baseTensorContraction n d ℓ t =
      (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id ℓ
        ((PiTensorProduct.tmulEquiv ℂ V).symm
          (PiTensorProduct.reindex ℂ (fun _ : Fin (n + d) => V)
            (finSumFinEquiv : Fin n ⊕ Fin d ≃ Fin (n + d)).symm t))) := by
  simp only [baseTensorContraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    InvariantsExterior.tensorAppend, LinearEquiv.symm_trans_apply,
    PiTensorProduct.reindex_symm]

end HodgeLean.Foundations.Abdulali
