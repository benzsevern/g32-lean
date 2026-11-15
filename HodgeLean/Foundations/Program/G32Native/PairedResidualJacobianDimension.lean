import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodFormDuality
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs

/-! # Dimension of the unchanged theta-model Jacobian -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The retained theta model has precisely the dimension of the original holomorphic forms. -/
theorem residual_jacobian_model_dimension (h : Module.finrank ℂ E = 1) :
    TopologicalSpace.dim (model (C := C) h).left = Module.finrank ℂ (b3_HolForm E C) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b3_holForm_finiteDimensional (C := C) h
  have hQ := b3_intersectionForm_isRiemannForm h (polarization (C := C) h)
    (b3_exists_intersectionForm (C := C) h).choose_spec
  have hd : Module.finrank ℂ (b5_V (b3_periodLattice E C) (b3_periodF E C)) =
      TopologicalSpace.dim (model (C := C) h).left := by
    simpa only [model, Module.finrank_fin_fun] using
      (b5_periodLinearEquiv (b3_periodLattice E C) (b3_periodF E C)
        (b3_isWeightOne h) (polarization (C := C) h) hQ).finrank_eq
  calc
    TopologicalSpace.dim (model (C := C) h).left =
        Module.finrank ℂ (b5_V (b3_periodLattice E C) (b3_periodF E C)) := hd.symm
    _ = Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) :=
      (b2_coord ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)).finrank_eq.symm
    _ = Module.finrank ℂ (Module.Dual ℂ (b3_HolForm E C)) :=
      (periodQuotientDualEquiv (C := C) h).finrank_eq
    _ = Module.finrank ℂ (b3_HolForm E C) := Subspace.dual_finrank_eq

#print axioms residual_jacobian_model_dimension
/-- The retained Jacobian model is smooth of the exact genus dimension. -/
theorem residual_jacobian_smooth_dimension (h : Module.finrank ℂ E = 1) :
    SmoothOfRelativeDimension (Module.finrank ℂ (b3_HolForm E C)) (model (C := C) h).hom := by
  have hs : SmoothOfRelativeDimension (TopologicalSpace.dim (model (C := C) h).left)
      (model (C := C) h).hom := SmoothOfRelativeDimension.of_isIntegral _
  exact (residual_jacobian_model_dimension (C := C) h) ▸ hs

#print axioms residual_jacobian_smooth_dimension
end HodgeLean.Foundations.Program.G32Native
