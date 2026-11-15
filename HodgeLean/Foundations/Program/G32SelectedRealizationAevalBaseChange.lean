import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_aeval_baseChange {U : Type*} [AddCommGroup U] [Module ℚ U]
    (T : Module.End ℚ U) (p : Polynomial ℚ) :
    (Polynomial.aeval T p).baseChange ℂ =
      Polynomial.aeval (T.baseChange ℂ) (p.map (algebraMap ℚ ℂ)) := by
  let ρ := Module.End.baseChangeHom ℚ ℂ U
  change ρ (Polynomial.aeval T p) = _
  rw [← Polynomial.aeval_algHom_apply]
  exact Polynomial.aeval_eq_aeval_map
    (IsScalarTower.algebraMap_eq ℚ ℂ (Module.End ℂ (ℂ ⊗[ℚ] U))).symm p (ρ T)

end HodgeLean.Foundations.Program
