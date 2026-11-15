import HodgeLean.Foundations.Program.G32SelectedRealizationKernelBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_baseChange_range {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (T : V →ₗ[ℚ] W) :
    LinearMap.range (T.baseChange ℂ) =
      LinearMap.range ((LinearMap.range T).subtype.baseChange ℂ) := by
  ext z
  change z ∈ LinearMap.range (T.lTensor ℂ) ↔
    z ∈ LinearMap.range ((LinearMap.range T).subtype.lTensor ℂ)
  rw [LinearMap.lTensor_range]

end HodgeLean.Foundations.Program
