import HodgeLean.Foundations.Program.G32SelectedRealizationPowerBasisEigen
import HodgeLean.Foundations.Program.G32SelectedRealizationPointwiseEigen
import HodgeLean.Foundations.Program.G32SelectedRealizationTensorCoordinates

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_cyclotomic_eigenspace_dimension {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m))
    (σ : cyc_Field m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cyc_eigenspace e σ) = d := by
  classical
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  let pb := (IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)).powerBasis ℚ
  have hg : pb.gen = ζ := IsPrimitiveRoot.powerBasis_gen _ _
  let A := (cyc_scalar e ζ).baseChange ℂ
  let T := (Algebra.lmul ℚ (cyc_Field m) ζ).baseChange ℂ
  let E := g32y_cyclotomic_tensor_coordinates e
  let L := g32y_pointwise_eigenspace_equiv E A T
    (g32y_tensor_coordinates_scalar e ζ) (σ ζ)
  have h₁ : Module.finrank ℂ (Module.End.eigenspace T (σ ζ)) = 1 := by
    have hh := g32y_powerBasis_eigenspace_dimension pb σ
    rw [hg] at hh
    exact hh
  rw [g32y_cyclotomic_eigenspace_generator]
  change Module.finrank ℂ (Module.End.eigenspace A (σ ζ)) = d
  calc
    _ = Module.finrank ℂ (Fin d → Module.End.eigenspace T (σ ζ)) := L.finrank_eq
    _ = d := by simp [Module.finrank_pi_fintype, h₁]

end HodgeLean.Foundations.Program
