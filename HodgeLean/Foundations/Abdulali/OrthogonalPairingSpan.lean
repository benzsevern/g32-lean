import HodgeLean.Foundations.Abdulali.InverseFormBaseSpan
import HodgeLean.Foundations.Abdulali.PairingDiagramSpan
import HodgeLean.Foundations.Program.MilneTensorProofs

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The full orthogonal FFT expands every base fixed tensor into actual inverse-form pairing diagrams. -/
theorem orthogonal_base_fixed_le_pairingDiagram_span
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (n : ℕ) :
    m1b_fixed (m1b_isometries B) n ≤
      Submodule.span ℂ {t | ∃ (m : ℕ) (e : (Fin m × Fin 2) ≃ Fin n),
        t = pairingDiagram (inverseFormBasis B hB hs) e} := by
  have hg := m1b_generation_of_copies_one (m1b_isometries B) n
    (m1b_orthogonal_tensors_aux V B hB hs 1 n)
  rw [hg, orthogonal_base_quadratics_eq_inverseForm_span B hB hs,
    inverseFormTensor_diagonal]
  exact diagonal_products_le_pairingDiagram_span _ n

end HodgeLean.Foundations.Abdulali
