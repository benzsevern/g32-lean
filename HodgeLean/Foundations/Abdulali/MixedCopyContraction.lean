import HodgeLean.Foundations.Abdulali.BaseTensorContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On a pure tensor, the enlarged contraction projects each block to its intended copies. -/
theorem mixedTensorContraction_tprod (r n d : ℕ) (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ)
    (v : Fin (n + d) → Fin (r + 1) → V) :
    mixedTensorContraction r n d ℓ (PiTensorProduct.tprod ℂ v) =
      ℓ (PiTensorProduct.tprod ℂ
        (fun j => mixedExtraOut r (v (Fin.natAdd n j)))) •
      PiTensorProduct.tprod ℂ (fun i => mixedCopiesOut r (v (Fin.castAdd d i))) := by
  have hv : InvariantsExterior.tensorAppend n d
      (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd d i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun j => v (Fin.natAdd n j))) =
      PiTensorProduct.tprod ℂ v := by
    rw [InvariantsExterior.tensorAppend_tprod, Fin.append_castAdd_natAdd]
  simp only [mixedTensorContraction, mixedTensorOut, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← hv, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul]
  simp only [PiTensorProduct.map_tprod]

end HodgeLean.Foundations.Abdulali
