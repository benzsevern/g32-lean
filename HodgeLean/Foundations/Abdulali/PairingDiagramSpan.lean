import HodgeLean.Foundations.Abdulali.PairingDiagram

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V β : Type*} [AddCommGroup V] [Module ℂ V] [Fintype β]

/-- Products of a diagonal quadratic are spanned by its pairing diagrams in every degree. -/
theorem diagonal_products_le_pairingDiagram_span (b : β → V) (n : ℕ) :
    m1b_products (Submodule.span ℂ
      {∑ a : β, PiTensorProduct.tprod ℂ (fun _ : Fin 2 => b a)}) n ≤
    Submodule.span ℂ {t | ∃ (m : ℕ) (e : (Fin m × Fin 2) ≃ Fin n),
      t = pairingDiagram b e} := by
  classical
  induction n using Nat.twoStepInduction with
  | zero =>
    intro t ht
    clear ht
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨0, Equiv.equivOfIsEmpty _ _, ?_⟩
      rw [pairingDiagram, Fintype.sum_unique]
      congr 1
      funext i
      exact Fin.elim0 i
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  | one => exact bot_le
  | more n ih _ =>
    apply Submodule.span_le.mpr
    rintro t ⟨σ, a, q, ha, hq, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hq
    rw [← hc, TensorProduct.tmul_smul, map_smul, map_smul]
    apply Submodule.smul_mem
    have ha' := ih ha
    clear ha
    induction ha' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, e, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨m + 1, (pairingAppendEquiv m n e).trans σ, ?_⟩
      rw [← pairingDiagram_perm, pairingDiagram_append]
    | zero =>
      rw [TensorProduct.zero_tmul, map_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul d x hx ihx =>
      rw [← TensorProduct.smul_tmul', map_smul, map_smul]
      exact Submodule.smul_mem _ d ihx

end HodgeLean.Foundations.Abdulali
