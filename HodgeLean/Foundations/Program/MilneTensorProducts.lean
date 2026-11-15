import HodgeLean.Foundations.Program.MilneTensorHelpers

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_tensorAppend_zero_two (t : ⨂[ℂ]^2 V) :
    InvariantsExterior.tensorAppend 0 2
      (PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)) ⊗ₜ[ℂ] t) = t := by
  have h : (InvariantsExterior.tensorAppend 0 2).toLinearMap.comp
      (TensorProduct.mk ℂ (⨂[ℂ]^0 V) (⨂[ℂ]^2 V)
        (PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)))) =
      LinearMap.id := by
    ext v
    change InvariantsExterior.tensorAppend 0 2
      (PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ v
    rw [InvariantsExterior.tensorAppend_tprod]
    congr 1
    funext i
    fin_cases i <;> rfl
  exact LinearMap.congr_fun h t

theorem m1b_products_two (S : Set (Module.End ℂ V)) :
    m1b_products (m1b_fixed S 2) 2 = m1b_fixed S 2 := by
  apply le_antisymm (m1b_products_le_fixed S 2)
  intro t ht
  apply Submodule.subset_span
  refine ⟨1, PiTensorProduct.tprod ℂ (fun i : Fin 0 => (Fin.elim0 i : V)),
    t, Submodule.mem_top, ht, ?_⟩
  simp only [map_one, Module.End.one_apply, m1b_tensorAppend_zero_two]

theorem m1b_tensor_generation_degree_zero (S : Set (Module.End ℂ V)) :
    m1b_fixed S 0 = m1b_products (m1b_fixed S 2) 0 := m1b_fixed_zero S

end HodgeLean.Foundations.Program
