import HodgeLean.Foundations.Abdulali.OrthogonalPairingSpan
import HodgeLean.Foundations.Abdulali.PairingVolumeDiagrams

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Contracted base orthogonal fixed tensors give the prescribed volume products under any copy labels. -/
theorem orthogonal_base_contraction_copy_mem
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n : ℕ) (c : Fin n → Fin r)
    (t : ⨂[ℂ]^(n + Module.finrank ℂ V) V)
    (ht : t ∈ m1b_fixed (m1b_isometries B) (n + Module.finrank ℂ V)) :
    m1b_copyTensorIn r n c
      (baseTensorContraction n (Module.finrank ℂ V) normalizedVolumeCovector t) ∈
      orthogonalVolumeProducts B r n := by
  have hq : (∑ a : Fin (Module.finrank ℂ V),
      PiTensorProduct.tprod ℂ (fun _ : Fin 2 => inverseFormBasis B hB hs a)) ∈
      m1b_fixed (m1b_isometries B) 2 := by
    rw [← inverseFormTensor_diagonal B hB hs,
      orthogonal_base_quadratics_eq_inverseForm_span B hB hs]
    exact Submodule.subset_span (Set.mem_singleton _)
  have ht' := orthogonal_base_fixed_le_pairingDiagram_span B hB hs
    (n + Module.finrank ℂ V) ht
  clear ht
  induction ht' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, e, rfl⟩ := hx
    exact pairingDiagram_volume_contract_mem B r n _ hq e c
  | zero =>
    simp only [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ihx =>
    simp only [map_smul]
    exact Submodule.smul_mem _ a ihx

end HodgeLean.Foundations.Abdulali
