import HodgeLean.Foundations.Program.MilneTensorContractions

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_tensorAppend_assoc_two (k l : ℕ) (a : ⨂[ℂ]^k V)
    (b : ⨂[ℂ]^l V) (c : ⨂[ℂ]^2 V) :
    InvariantsExterior.tensorAppend k (l + 2)
      (a ⊗ₜ[ℂ] InvariantsExterior.tensorAppend l 2 (b ⊗ₜ[ℂ] c)) =
    InvariantsExterior.tensorAppend (k + l) 2
      (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod x v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod y w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod z u =>
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
          smul_smul, mul_assoc, InvariantsExterior.tensorAppend_tprod]
        congr 1
        congr 1
        funext i
        have h := congrFun (Fin.append_assoc v w u) i
        simpa only [Function.comp_apply, Fin.cast_eq_self] using h.symm
      | add c d hc hd =>
        simp only [TensorProduct.tmul_add, map_add, hc, hd]
    | add b c hb hc =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hb, hc]
  | add a b ha hb =>
    simp only [TensorProduct.add_tmul, map_add, ha, hb]

theorem m1b_tensorAppend_right_unit (k : ℕ) (a : ⨂[ℂ]^k V) :
    InvariantsExterior.tensorAppend k 0
      (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V))) = a := by
  have h : (InvariantsExterior.tensorAppend k 0).toLinearMap.comp
      ((TensorProduct.mk ℂ (⨂[ℂ]^k V) (⨂[ℂ]^0 V)).flip
        (PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)))) = LinearMap.id := by
    ext v
    change InvariantsExterior.tensorAppend k 0
      ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V))) = _
    rw [InvariantsExterior.tensorAppend_tprod]
    congr 1
    exact Fin.append_right_nil _ _ rfl
  exact LinearMap.congr_fun h a

end HodgeLean.Foundations.Program
