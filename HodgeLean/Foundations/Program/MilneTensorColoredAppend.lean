import HodgeLean.Foundations.Program.MilneTensorAppendClosure
import HodgeLean.Foundations.Program.MilneTensorGLPairTheorem

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_coloredWordIn_append (n k l : ℕ) (s : Finset (Fin n))
    (e : Fin k ≃ {i // i ∈ s}) (d : Fin l ≃ {i // i ∉ s})
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l W) :
    let u := (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).symm.trans
      ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s)))
    InvariantsExterior.coloredWordIn s
      (PiTensorProduct.reindex ℂ (fun _ => V) e a ⊗ₜ[ℂ]
        PiTensorProduct.reindex ℂ (fun _ => W) d b) =
      PiTensorProduct.reindex ℂ (fun _ => V × W) u
        (InvariantsExterior.tensorAppend k l
          (PiTensorProduct.map (fun _ => LinearMap.inl ℂ V W) a ⊗ₜ[ℂ]
            PiTensorProduct.map (fun _ => LinearMap.inr ℂ V W) b)) := by
  classical
  dsimp only
  have h : (InvariantsExterior.coloredWordIn s).comp
      (TensorProduct.map (PiTensorProduct.reindex ℂ (fun _ => V) e).toLinearMap
        (PiTensorProduct.reindex ℂ (fun _ => W) d).toLinearMap) =
      (PiTensorProduct.reindex ℂ (fun _ => V × W)
        ((finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).symm.trans
          ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s))))).toLinearMap.comp
        ((InvariantsExterior.tensorAppend k l).toLinearMap.comp
          (TensorProduct.map (PiTensorProduct.map (fun _ => LinearMap.inl ℂ V W))
            (PiTensorProduct.map (fun _ => LinearMap.inr ℂ V W)))) := by
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change InvariantsExterior.coloredWordIn s
        (PiTensorProduct.reindex ℂ (fun _ => V) e (⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ]
          PiTensorProduct.reindex ℂ (fun _ => W) d (⨂ₜ[ℂ] i, w i)) =
      PiTensorProduct.reindex ℂ (fun _ => V × W)
        ((finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).symm.trans
          ((Equiv.sumCongr e d).trans (Equiv.sumCompl (· ∈ s))))
        (InvariantsExterior.tensorAppend k l
          (PiTensorProduct.map (fun _ => LinearMap.inl ℂ V W) (⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ]
            PiTensorProduct.map (fun _ => LinearMap.inr ℂ V W) (⨂ₜ[ℂ] i, w i)))
    simp only [PiTensorProduct.reindex_tprod, InvariantsExterior.coloredWordIn,
      LinearMap.comp_apply, TensorProduct.map_tmul, InvariantsExterior.orderedWordIn,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, PiTensorProduct.tmulEquiv_apply,
      InvariantsExterior.tensorAppend_tprod, PiTensorProduct.reindex_tprod]
    congr 1
    funext i
    cases h : (Equiv.sumCompl (· ∈ s)).symm i <;> simp [h, Fin.append]
  exact LinearMap.congr_fun h (a ⊗ₜ[ℂ] b)

end HodgeLean.Foundations.Program
