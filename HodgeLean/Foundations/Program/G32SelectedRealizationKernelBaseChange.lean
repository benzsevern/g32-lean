import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveCoordinates
import Mathlib.RingTheory.Flat.Basic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_baseChange_kernel {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (f : U →ₗ[ℚ] V) :
    LinearMap.range ((LinearMap.ker f).subtype.baseChange ℂ) =
      LinearMap.ker (f.baseChange ℂ) := by
  have he : Function.Exact (LinearMap.ker f).subtype f := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  have ht : Function.Exact ((LinearMap.ker f).subtype.baseChange ℂ) (f.baseChange ℂ) :=
    Module.Flat.lTensor_exact ℂ he
  exact (LinearMap.exact_iff.mp ht).symm

end HodgeLean.Foundations.Program
