import HodgeLean.Adapters.NormalConeB4aGysinLowerDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

noncomputable section
namespace HodgeLean.Adapters

/-- Analytic images from strictly smaller complex dimension have zero volume
in the parameter space. -/
theorem a3b4a_gysin_complex_lower_dimensional_image_null
    {m n : ℕ} (U : Set (Fin m → ℂ))
    (f : (Fin m → ℂ) → (Fin n → ℂ)) (hf : AnalyticOnNhd ℂ f U)
    (hmn : m < n) : MeasureTheory.volume (f '' U) = 0 := by
  apply a3b4a_gysin_lower_dimensional_image_null U f (hf.differentiableOn.restrictScalars ℝ)
  simp only [finrank_real_of_complex, Module.finrank_fin_fun]
  omega

end HodgeLean.Adapters
