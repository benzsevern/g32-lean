import HodgeLean.Foundations.Program.G32SelectedRealizationPreserves
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_cyclotomic_eigenspace_generator {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} [NeZero m] (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m))
    (σ : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_eigenspace e σ = Module.End.eigenspace
      ((cyc_scalar e (IsCyclotomicExtension.zeta m ℚ (cyc_Field m))).baseChange ℂ)
      (σ (IsCyclotomicExtension.zeta m ℚ (cyc_Field m))) := by
  let ζ := IsCyclotomicExtension.zeta m ℚ (cyc_Field m)
  let hz := IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)
  let pb := hz.powerBasis ℚ
  apply le_antisymm
  · exact iInf_le _ ζ
  · intro v hv
    simp only [cyc_eigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro a
    obtain ⟨p, hp⟩ := pb.exists_eq_aeval' a
    have hgen : pb.gen = ζ := hz.powerBasis_gen ℚ
    rw [hgen] at hp
    let ρ : cyc_Field m →ₐ[ℚ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
      (Module.End.baseChangeHom ℚ ℂ V).comp (cyc_rep e)
    have ha : (cyc_scalar e a).baseChange ℂ =
        Polynomial.aeval ((cyc_scalar e ζ).baseChange ℂ) (p.map (algebraMap ℚ ℂ)) := by
      change ρ a = _
      rw [hp, ← Polynomial.aeval_algHom_apply]
      exact Polynomial.aeval_eq_aeval_map
        (IsScalarTower.algebraMap_eq ℚ ℂ (Module.End ℂ (ℂ ⊗[ℚ] V))).symm p (ρ ζ)
    have hs : (p.map (algebraMap ℚ ℂ)).eval (σ ζ) = σ a := by
      rw [hp, ← Polynomial.aeval_algHom_apply]
      simp only [Polynomial.aeval_def, Polynomial.eval_map, AlgHom.commutes]
    have hv' := Module.End.mem_eigenspace_iff.mp hv
    rw [ha, Module.End.aeval_apply_of_mem_apply_eq_smul hv', hs]

end HodgeLean.Foundations.Program
