import HodgeLean.Foundations.Abdulali.OrthogonalQuadraticTensors
import HodgeLean.Foundations.Program.MilneTensorCopyFixed
import HodgeLean.Foundations.Program.MilneTensorCopyInjection

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations HodgeLean.Foundations.Program

/-- The inverse-form tensor with an independent copy label on each of its
two slots.
Source: Weyl, The Classical Groups, Chapter II, §9. -/
def labelledInverseFormTensor (d r : ℕ) (labels : Fin 2 → Fin r) :
    ⨂[ℂ]^2 (Fin r → Fin d → ℂ) :=
  m1b_copyTensorIn r 2 labels (standardInverseFormTensor d)

example (d r : ℕ) (labels : Fin 2 → Fin r) :
    labelledInverseFormTensor d r labels = PiTensorProduct.map
      (fun i => LinearMap.single ℂ (fun _ : Fin r => Fin d → ℂ) (labels i))
      (standardInverseFormTensor d) := rfl

/-- The degree-two full-O invariants on any number of standard copies are
exactly the span of independently labelled inverse-form tensors.
Source: Weyl, The Classical Groups, Chapter II, §9 (polarized contractions). -/
theorem standard_orthogonal_labelled_quadratics (d : ℕ) (hd : 0 < d) (r : ℕ) :
    m1b_fixed (m1b_copies r ''
      m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin') 2 =
      Submodule.span ℂ (Set.range (labelledInverseFormTensor d r)) := by
  apply le_antisymm
  · intro t ht
    rw [← m1b_sum_copyTensorIn_out r 2 t]
    apply Submodule.sum_mem
    intro labels _
    have ha := m1b_copyTensorOut_fixed
      (m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin') r 2 labels t ht
    rw [standard_orthogonal_quadratic_tensors d hd] at ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    rw [← hc, map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨labels, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨labels, rfl⟩
    have hQ : standardInverseFormTensor d ∈
        m1b_fixed (m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin') 2 := by
      rw [standard_orthogonal_quadratic_tensors d hd]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact m1b_copyInjection_family_fixed _ r 2
      (fun i => LinearMap.single ℂ (fun _ : Fin r => Fin d → ℂ) (labels i))
      (fun i => ⟨labels i, rfl⟩) _ hQ

/-- The standard quadratic generator is nonzero in every positive dimension.
Source: Weyl, The Classical Groups, Chapter II, §9; its normalization is
`standardInverseFormTensor_pairing`. -/
theorem standardInverseFormTensor_ne_zero (d : ℕ) (hd : 0 < d) :
    standardInverseFormTensor d ≠ 0 := by
  intro h
  have hh := standardInverseFormTensor_pairing d
    ![(Pi.single ⟨0, hd⟩ (1 : ℂ) : Fin d → ℂ), Pi.single ⟨0, hd⟩ 1]
  rw [h, map_zero] at hh
  norm_num [Matrix.toBilin'_single] at hh

end HodgeLean.Foundations.Abdulali
