import HodgeLean.Foundations.Program.MilneTensorAppendPermutation

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_products_append (Q : Submodule ℂ (⨂[ℂ]^2 V)) (k : ℕ)
    (a : ⨂[ℂ]^k V) (ha : a ∈ m1b_products Q k) :
    ∀ (l : ℕ) (b : ⨂[ℂ]^l V), b ∈ m1b_products Q l →
      InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b) ∈ m1b_products Q (k + l) := by
  intro l
  induction l using Nat.twoStepInduction with
  | zero =>
    intro b _
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      have hv : v = fun i : Fin 0 => (Fin.elim0 i : V) := Subsingleton.elim _ _
      rw [hv, TensorProduct.tmul_smul, map_smul, m1b_tensorAppend_right_unit]
      exact Submodule.smul_mem _ c ha
    | add b c hb hc =>
      rw [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ (hb Submodule.mem_top) (hc Submodule.mem_top)
  | one =>
    intro b hb
    have hz : b = 0 := hb
    rw [hz, TensorProduct.tmul_zero, map_zero]
    exact Submodule.zero_mem _
  | more l ih _ =>
    intro b hb
    change b ∈ Submodule.span ℂ _ at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨σ, u, q, hu, hq, rfl⟩ := hb
      rw [m1b_tensorAppend_perm_right, m1b_tensorAppend_assoc_two]
      apply m1b_products_perm
      apply Submodule.subset_span
      refine ⟨1, InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] u), q,
        ih u hu, hq, ?_⟩
      simp only [map_one, Module.End.one_apply]
      rfl
    | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
    | add b c hb hc ihb ihc =>
      rw [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ ihb ihc
    | smul c b hb ihb =>
      rw [TensorProduct.tmul_smul, map_smul]
      exact Submodule.smul_mem _ c ihb

end HodgeLean.Foundations.Program
