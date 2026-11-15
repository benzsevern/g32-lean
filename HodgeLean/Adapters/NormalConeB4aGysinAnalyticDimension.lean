import HodgeLean.Adapters.NormalConeB4aClassInverseDense

noncomputable section
namespace HodgeLean.Adapters

/-- An analytic map with finite fibres on a nonempty open set cannot lower
complex dimension. -/
theorem a3b4a_gysin_finite_fibre_analytic_dimension_le
    {d m : ℕ} (U : Set (Fin d → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)
    (f : (Fin d → ℂ) → (Fin m → ℂ)) (hf : AnalyticOnNhd ℂ f U)
    (hfin : ∀ a, {z | z ∈ U ∧ f z = a}.Finite) : d ≤ m := by
  obtain ⟨x, _, hinj⟩ := HodgeLean.Foundations.Analytic.ancrs_exists_injective_of_finite_fibres
    hU hne hf hfin
  simpa only [Module.finrank_fin_fun] using
    LinearMap.finrank_le_finrank_of_injective
      (f := (fderiv ℂ f x : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ))) hinj

end HodgeLean.Adapters
